/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPar — a parallel model of the fused sweep + coalesce
///
/// The heap is cut at boundaries bs = [zero_addr; b1; ...; bk; heap_size].
/// Every interior boundary is a header the sequential walk lands on.
/// Segment i covers the objects whose headers lie in [b_i, b_{i+1}).
///
///   1. Segments (in parallel).  Each segment walks its own objects from its
///      own start, against the frozen input heap, exactly as `fused_aux`
///      does, with two differences:
///        - its leading free run (objects before its first survivor) and its
///          trailing free run (objects after its last survivor) are returned
///          unflushed; a segment with no survivor returns one run, the whole
///          segment;
///        - its local free list starts from a placeholder (0UL), and it
///          reports the first block it linked, whose link word holds that
///          placeholder.
///      Each segment writes into its own copy of the heap, and only the bytes
///      of its own range [b_i, b_{i+1}) are kept (`splice`).
///
///   2. Merge and link (sequential, left to right).  A carried run is the
///      trailing run so far.  An all-free segment extends it, so a run can
///      chain across any number of segments.  At a segment with a survivor,
///      carry ++ leading run is flushed as one run (one `flush_blue`, as the
///      sequential pass does), the segment's first linked block is patched to
///      point at the free-list head so far, and the head becomes the
///      segment's local head.  The final carry is flushed at the end.
///
/// The theorem: for every valid bs, under the precondition of the extracted
/// `GC.Impl.FusedSweepCoalesce.fused_sweep_coalesce`,
///
///   sweep_par bs g == fused_sweep_coalesce g      (heap and free-list head)
///
/// It is stated and admitted; see docs/parallel-sweep-phase1.md.
/// ---------------------------------------------------------------------------
module GC.Spec.SweepPar

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SweepPar.Exec

module SI = GC.Spec.SweepInv
module Defs = GC.Spec.SweepCoalesce.Defs
module SC = GC.Spec.Coalesce
module CC = GC.Spec.Coalesce.Correct
module Ind = GC.Spec.SweepCoalesce.Induction
module HeapGraph = GC.Spec.HeapGraph

/// ---------------------------------------------------------------------------
/// Boundaries
/// ---------------------------------------------------------------------------

/// The boundaries after `prev`: strictly increasing walk positions, ending
/// with exactly `heap_size`.
let rec bounds_from (g: heap) (prev: nat) (bs: list nat)
  : Tot bool (decreases bs) =
  match bs with
  | [] -> false
  | [b] -> prev < b && b = heap_size
  | b :: rest ->
    prev < b && b < heap_size && b % 8 = 0 &&
    walk_visits_x g zero_addr (U64.uint_to_t b) &&
    bounds_from g b rest

let valid_bounds (g: heap) (bs: list nat) : bool =
  match bs with
  | b0 :: rest -> b0 = U64.v zero_addr && bounds_from g b0 rest
  | [] -> false

/// ---------------------------------------------------------------------------
/// Free runs
/// ---------------------------------------------------------------------------

/// A pending free run, as `fused_aux` carries it in (fb, rw):
/// first block and total words, rw = 0 meaning no run.
type run = { fb: U64.t; rw: nat }

let no_run : run = { fb = 0UL; rw = 0 }

/// One more free object at the end of a run (fused_aux's accumulate step).
let extend (r: run) (obj: obj_addr) (ws: nat) : run =
  { fb = (if r.rw = 0 then obj else r.fb); rw = r.rw + ws + 1 }

/// Run `a` immediately followed by run `b`.
let join (a b: run) : run =
  if a.rw = 0 then b else { fb = a.fb; rw = a.rw + b.rw }

/// ---------------------------------------------------------------------------
/// One segment
/// ---------------------------------------------------------------------------

/// The objects whose headers lie in [start, hi): the walk of `objects`,
/// started at `start` and stopped at `hi`.
let rec seg_objects (g: heap) (start: hp_addr) (hi: nat)
  : Tot (seq obj_addr) (decreases (heap_size - U64.v start))
  = if U64.v start >= hi then Seq.empty
    else if U64.v start + 8 >= heap_size then Seq.empty
    else
      let wz = getWosize (read_word g start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size || next >= pow2 64 then Seq.empty
      else begin
        f_address_spec start;
        let o : obj_addr = f_address start in
        if next >= heap_size then Seq.cons o Seq.empty
        else begin
          aligned_plus_mul8 (U64.v start) (U64.v wz + 1);
          Seq.cons o (seg_objects g (mk_hp_addr next) hi)
        end
      end

noeq type seg_out = {
  sheap: heap;                (* the segment's copy of the heap *)
  all_free: bool;             (* no survivor: `lead` is the whole segment *)
  lead: run;                  (* leading free run, unflushed *)
  trail: run;                 (* trailing free run, unflushed *)
  first_link: option U64.t;   (* first block linked; its link word is 0UL *)
  local_head: U64.t;          (* head of the segment's local list *)
}

/// `fused_aux` on one segment's objects.  `seen` records whether a survivor
/// has been passed; before it, free objects grow `lead`, after it `cur`.
let rec seg_aux (g0: heap) (g: heap) (objs: seq obj_addr)
    (seen: bool) (lead: run) (cur: run) (fp: U64.t) (first: option U64.t)
  : Tot seg_out (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      { sheap = g; all_free = not seen; lead = lead; trail = cur;
        first_link = first; local_head = fp }
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_black_x obj g0 then
        if not seen then
          (* First survivor: the leading run stays unflushed. *)
          seg_aux g0 (makeWhite_x obj g) rest true lead no_run fp first
        else
          let (g', fp') = flush_blue_x g cur.fb cur.rw fp in
          (* flush_blue returns either fp (not linked) or the run's block. *)
          let first' =
            match first with
            | Some _ -> first
            | None -> if fp' <> fp then Some fp' else None in
          seg_aux g0 (makeWhite_x obj g') rest true lead no_run fp' first'
      else
        let ws = U64.v (wosize_x obj g0) in
        if seen then seg_aux g0 g rest seen lead (extend cur obj ws) fp first
        else seg_aux g0 g rest seen (extend lead obj ws) cur fp first

let sweep_segment (g: heap) (lo: hp_addr) (hi: nat) : seg_out =
  seg_aux g g (seg_objects g lo hi) false no_run no_run 0UL None

/// ---------------------------------------------------------------------------
/// All segments
/// ---------------------------------------------------------------------------

noeq type seg_raw = { lo: nat; hi: nat; out: seg_out }
type seg = s:seg_raw{s.lo <= s.hi /\ s.hi <= heap_size}

/// Consecutive pairs of boundaries.
let rec segments (bs: list nat) : list (nat & nat) =
  match bs with
  | lo :: hi :: rest -> (lo, hi) :: segments (hi :: rest)
  | _ -> []

/// Every segment swept independently, each against the input heap.
/// (Pairs that are not segments of a valid bs are skipped.)
let rec sweep_all (g: heap) (ps: list (nat & nat)) : Tot (list seg) (decreases ps) =
  match ps with
  | [] -> []
  | (lo, hi) :: rest ->
    if lo < hi && hi <= heap_size && lo % 8 = 0 then
      { lo = lo; hi = hi; out = sweep_segment g (U64.uint_to_t lo) hi }
        :: sweep_all g rest
    else sweep_all g rest

/// `base` with bytes [lo, hi) taken from `src`.
let splice (base src: heap) (lo: nat) (hi: nat{lo <= hi /\ hi <= heap_size}) : heap =
  Seq.append (Seq.slice base 0 lo)
    (Seq.append (Seq.slice src lo hi) (Seq.slice base hi heap_size))

/// Each segment owns its range: keep only those bytes of its copy.
let rec splice_all (g: heap) (rs: list seg) : Tot heap (decreases rs) =
  match rs with
  | [] -> g
  | r :: rest -> splice_all (splice g r.out.sheap r.lo r.hi) rest

/// ---------------------------------------------------------------------------
/// Merge and link
/// ---------------------------------------------------------------------------

/// Set the link word (field 1) of block `a` to `v`.
let patch_link (g: heap) (a: U64.t) (v: U64.t) : heap =
  if U64.v a >= U64.v mword && U64.v a < heap_size && U64.v a % 8 = 0 &&
     U64.v (hd_address a) + U64.v mword * 2 <= heap_size
  then set_field_x g a 1UL v
  else g

let rec link_all (g: heap) (carry: run) (fp: U64.t) (rs: list seg)
  : Tot (heap & U64.t) (decreases rs)
  = match rs with
    | [] -> flush_blue_x g carry.fb carry.rw fp
    | r :: rest ->
      let o = r.out in
      if o.all_free then
        (* The run continues through this segment. *)
        link_all g (join carry o.lead) fp rest
      else
        (* The run ends at this segment's first survivor. *)
        let run = join carry o.lead in
        let (g1, fp1) = flush_blue_x g run.fb run.rw fp in
        let (g2, fp2) =
          match o.first_link with
          | None -> (g1, fp1)
          | Some a -> (patch_link g1 a fp1, o.local_head) in
        link_all g2 o.trail fp2 rest

/// ---------------------------------------------------------------------------
/// The parallel sweep
/// ---------------------------------------------------------------------------

let sweep_par (bs: list nat) (g: heap) : heap & U64.t =
  let rs = sweep_all g (segments bs) in
  link_all (splice_all g rs) no_run 0UL rs

/// ---------------------------------------------------------------------------
/// Proof, part 1: what one flush and one whitening write
/// ---------------------------------------------------------------------------
///
/// The proof compares heaps word by word.  A flush overwrites exactly its
/// run's words, with values that depend only on the run and, for the link
/// word, on the head it is given.  A whitening overwrites one header.

/// A pending run occupies [fb - mword, run_end); an empty run is `no_run`.
let run_geom (r: run) (run_end: nat) : prop =
  (r.rw = 0 ==> r == no_run) /\
  (r.rw > 0 ==>
    U64.v r.fb >= U64.v mword /\ U64.v r.fb < heap_size /\
    U64.v r.fb % U64.v mword == 0 /\
    U64.v r.fb - U64.v mword + r.rw * U64.v mword == run_end /\
    run_end <= heap_size)

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let run_words_bound (r: run) (run_end: nat)
  : Lemma (requires run_geom r run_end /\ r.rw > 0)
          (ensures r.rw - 1 < pow2 54)
  = assert (r.rw * 8 <= heap_size);
    assert_norm (pow2 57 == 8 * pow2 54)
#pop-options

/// Words outside the run are untouched.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let flush_outside (h: heap) (r: run) (run_end: nat) (fp: U64.t) (p: hp_addr)
  : Lemma (requires run_geom r run_end /\
                    (r.rw = 0 \/ U64.v p < U64.v r.fb - U64.v mword \/ U64.v p >= run_end))
          (ensures read_word (fst (SC.flush_blue h r.fb r.rw fp)) p == read_word h p)
  = SC.flush_blue_preserves_outside h r.fb r.rw fp p
#pop-options

/// The flush returns the run's block when it links it (two words or more),
/// and the head it was given otherwise.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let flush_head (h: heap) (r: run) (run_end: nat) (fp: U64.t)
  : Lemma (requires run_geom r run_end)
          (ensures snd (SC.flush_blue h r.fb r.rw fp) == (if r.rw >= 2 then r.fb else fp))
  = if r.rw > 0 then begin
      run_words_bound r run_end;
      hd_address_spec (r.fb <: obj_addr)
    end
#pop-options

/// A linked block's link word holds the head the flush was given.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let flush_link_word (h: heap) (r: run) (run_end: nat) (fp: U64.t)
  : Lemma (requires run_geom r run_end /\ r.rw >= 2)
          (ensures U64.v r.fb < heap_size /\ U64.v r.fb % 8 == 0 /\
                   read_word (fst (SC.flush_blue h r.fb r.rw fp)) r.fb == fp)
  = run_words_bound r run_end;
    hd_address_spec (r.fb <: obj_addr);
    SC.flush_blue_field1_spec h r.fb r.rw fp
#pop-options

/// The words after the link word are zeroed.  (`GC.Spec.Coalesce` and
/// `GC.Spec.SweepCoalesce.Induction` each prove this privately.)
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let flush_zero_word (g: heap) (fb: obj_addr) (rw: nat) (fp: U64.t) (a: hp_addr)
  : Lemma (requires rw >= 3 /\ rw - 1 < pow2 54 /\
                    U64.v (hd_address fb) + rw * 8 <= heap_size /\
                    U64.v a >= U64.v fb + 8 /\ U64.v a < U64.v fb + (rw - 1) * 8)
          (ensures read_word (fst (SC.flush_blue g fb rw fp)) a == 0UL)
  = hd_address_spec fb;
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    let hd = hd_address fb in
    let wz_u64 : wosize = U64.uint_to_t (rw - 1) in
    let g1 = write_word g hd (makeHeader wz_u64 GC.Lib.Header.Blue 0UL) in
    assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
    let g2 = HeapGraph.set_field g1 fb 1UL fp in
    Ind.zero_fields_read_within g2 (U64.uint_to_t (U64.v fb + 8)) (rw - 2) a
#pop-options

/// Inside the run, two flushes of the same run write the same word, except
/// the link word when they are given different heads.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let flush_inside (h1 h2: heap) (r: run) (run_end: nat) (fp1 fp2: U64.t) (p: hp_addr)
  : Lemma (requires run_geom r run_end /\ r.rw > 0 /\
                    U64.v r.fb - U64.v mword <= U64.v p /\ U64.v p < run_end /\
                    (fp1 == fp2 \/ p <> r.fb))
          (ensures read_word (fst (SC.flush_blue h1 r.fb r.rw fp1)) p ==
                   read_word (fst (SC.flush_blue h2 r.fb r.rw fp2)) p)
  = run_words_bound r run_end;
    let fb : obj_addr = r.fb in
    hd_address_spec fb;
    Ind.flush_blue_inside_agree h1 h2 fb r.rw fp1 p;
    if fp1 = fp2 then ()
    else if U64.v p = U64.v fb - 8 then begin
      SC.flush_blue_header_spec h2 fb r.rw fp1;
      SC.flush_blue_header_spec h2 fb r.rw fp2
    end else begin
      flush_zero_word h2 fb r.rw fp1 p;
      flush_zero_word h2 fb r.rw fp2 p
    end
#pop-options

/// Two flushes of the same run agree at `p` if the heaps agreed there or `p`
/// is in the run, and the heads agree or `p` is not the link word.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let flush_agree_at (h1 h2: heap) (r: run) (run_end: nat) (fp1 fp2: U64.t) (p: hp_addr)
  : Lemma (requires run_geom r run_end /\
                    (read_word h1 p == read_word h2 p \/
                     (r.rw > 0 /\ U64.v r.fb - U64.v mword <= U64.v p /\ U64.v p < run_end)) /\
                    (fp1 == fp2 \/ p <> r.fb))
          (ensures read_word (fst (SC.flush_blue h1 r.fb r.rw fp1)) p ==
                   read_word (fst (SC.flush_blue h2 r.fb r.rw fp2)) p)
  = if r.rw > 0 && U64.v r.fb - U64.v mword <= U64.v p && U64.v p < run_end
    then flush_inside h1 h2 r run_end fp1 fp2 p
    else begin
      flush_outside h1 r run_end fp1 p;
      flush_outside h2 r run_end fp2 p
    end
#pop-options

/// Whitening writes only the object's header, from the header already there.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let white_other (h: heap) (x: obj_addr) (p: hp_addr)
  : Lemma (requires p <> hd_address x)
          (ensures read_word (makeWhite x h) p == read_word h p)
  = makeWhite_spec x h;
    read_write_different h (hd_address x) p
      (colorHeader (read_word h (hd_address x)) GC.Lib.Header.White)

let white_same (h1 h2: heap) (x: obj_addr)
  : Lemma (requires read_word h1 (hd_address x) == read_word h2 (hd_address x))
          (ensures read_word (makeWhite x h1) (hd_address x) ==
                   read_word (makeWhite x h2) (hd_address x))
  = makeWhite_spec x h1;
    makeWhite_spec x h2;
    read_write_same h1 (hd_address x) (colorHeader (read_word h1 (hd_address x)) GC.Lib.Header.White);
    read_write_same h2 (hd_address x) (colorHeader (read_word h2 (hd_address x)) GC.Lib.Header.White)
#pop-options

/// ---------------------------------------------------------------------------
/// Proof, part 2: the sequential pass, step by step
/// ---------------------------------------------------------------------------

/// `fused_aux`'s steps, without the final flush: the heap, the pending run
/// and the head after `objs`.
let rec fsteps (g0 h: heap) (objs: seq obj_addr) (r: run) (fp: U64.t)
  : GTot (heap & run & U64.t) (decreases Seq.length objs)
  = if Seq.length objs = 0 then (h, r, fp)
    else
      let obj = Seq.head objs in
      if is_black obj g0 then
        let (h', fp') = SC.flush_blue h r.fb r.rw fp in
        fsteps g0 (makeWhite obj h') (Seq.tail objs) no_run fp'
      else
        fsteps g0 h (Seq.tail objs) (extend r obj (U64.v (wosize_of_object obj g0))) fp

/// `fused_aux` over `a ++ b` is `fused_aux` over `b` from the state after `a`.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec fused_aux_append (g0 h: heap) (a b: seq obj_addr) (r: run) (fp: U64.t)
  : Lemma (ensures (let (h', r', fp') = fsteps g0 h a r fp in
                    Defs.fused_aux g0 h (Seq.append a b) r.fb r.rw fp ==
                    Defs.fused_aux g0 h' b r'.fb r'.rw fp'))
          (decreases Seq.length a)
  = if Seq.length a = 0 then Seq.lemma_eq_elim (Seq.append a b) b
    else begin
      let ab = Seq.append a b in
      Seq.lemma_eq_elim (Seq.tail ab) (Seq.append (Seq.tail a) b);
      assert (Seq.head ab == Seq.head a);
      let obj = Seq.head a in
      if is_black obj g0 then begin
        let (h1, fp1) = SC.flush_blue h r.fb r.rw fp in
        fused_aux_append g0 (makeWhite obj h1) (Seq.tail a) b no_run fp1
      end else
        fused_aux_append g0 h (Seq.tail a) b
          (extend r obj (U64.v (wosize_of_object obj g0))) fp
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Proof, part 3: a segment's walk is a slice of the heap's walk
/// ---------------------------------------------------------------------------

/// `seg_objects` from a cursor that may have reached `heap_size`.
let seg_rest (g: heap) (c: nat) (hi: nat) : seq obj_addr =
  if c < heap_size && c % 8 = 0 then seg_objects g (mk_hp_addr c) hi else Seq.empty

/// The walk from `c` lands exactly on `hi`, unless `hi` is the heap's end.
let reach (g: heap) (c: nat) (hi: nat) : prop =
  c < hi ==>
    (c < heap_size /\ c % 8 == 0 /\
     (hi == heap_size \/
      (hi < heap_size /\ hi % 8 == 0 /\ CC.walk_visits g (mk_hp_addr c) (mk_hp_addr hi))))

/// One object of a segment: its header is at the cursor, it ends at or
/// before `hi`, and the rest of the segment is the walk from its end.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let seg_step (g: heap) (c hi: nat)
  : Lemma (requires reach g c hi /\ c < hi /\ hi <= heap_size /\
                    Seq.length (seg_rest g c hi) > 0)
          (ensures (let objs = seg_rest g c hi in
                    let obj = Seq.head objs in
                    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
                    U64.v obj == c + 8 /\ c < heap_size /\ hd_address obj == mk_hp_addr c /\
                    next <= hi /\ next % 8 == 0 /\
                    Seq.tail objs == seg_rest g next hi /\
                    reach g next hi))
  = let cc = mk_hp_addr c in
    let wz = getWosize (read_word g cc) in
    let next = c + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 c (U64.v wz + 1);
    assert (seg_rest g c hi == seg_objects g cc hi);
    f_address_spec cc;
    let o : obj_addr = f_address cc in
    let tl = if next < heap_size then seg_objects g (mk_hp_addr next) hi else Seq.empty in
    assert (next <= heap_size);
    assert (seg_objects g cc hi == Seq.cons o tl);
    Seq.lemma_tl o tl;
    Seq.head_cons o tl;
    assert (tl == seg_rest g next hi);
    hd_address_spec o;
    wosize_of_object_spec o g;
    if hi < heap_size then CC.walk_visits_next_bound g cc (mk_hp_addr hi)
#pop-options

/// A segment's walk only runs out at `hi`, unless `hi` is the heap's end.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let seg_empty_end (g: heap) (c hi: nat)
  : Lemma (requires reach g c hi /\ c <= hi /\ hi < heap_size /\
                    Seq.length (seg_rest g c hi) == 0)
          (ensures c == hi)
  = if c < hi then begin
      let cc = mk_hp_addr c in
      let wz = getWosize (read_word g cc) in
      aligned_plus_mul8 c (U64.v wz + 1)
    end
#pop-options

/// The walk from `s` is the segment [s, hi) followed by the walk from `hi`.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let rec objects_seg_split (g: heap) (s hi: hp_addr)
  : Lemma (requires CC.walk_visits g s hi)
          (ensures objects s g == Seq.append (seg_objects g s (U64.v hi)) (objects hi g))
          (decreases (heap_size - U64.v s))
  = if U64.v s = U64.v hi then
      Seq.lemma_eq_elim (Seq.append (seg_objects g s (U64.v hi)) (objects hi g)) (objects hi g)
    else begin
      let wz = getWosize (read_word g s) in
      let next_nat = U64.v s + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      let next = mk_hp_addr next_nat in
      CC.walk_visits_above g next hi;
      objects_seg_split g next hi;
      f_address_spec s;
      let o : obj_addr = f_address s in
      Seq.append_assoc (Seq.create 1 o) (seg_objects g next (U64.v hi)) (objects hi g)
    end
#pop-options

/// The last segment is the whole rest of the walk.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let rec objects_seg_last (g: heap) (s: hp_addr)
  : Lemma (ensures objects s g == seg_objects g s heap_size)
          (decreases (heap_size - U64.v s))
  = let wz = getWosize (read_word g s) in
    let next_nat = U64.v s + (U64.v wz + 1) * 8 in
    aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
    if U64.v s + 8 < heap_size && next_nat < heap_size then
      objects_seg_last g (mk_hp_addr next_nat)
#pop-options

/// ---------------------------------------------------------------------------
/// Statement
/// ---------------------------------------------------------------------------

/// The precondition of the extracted `fused_sweep_coalesce`
/// (mark-and-sweep/impl/GC.Impl.FusedSweepCoalesce.fsti).
let fused_pre (g: heap) : prop =
  well_formed_heap g /\
  Seq.length (objects zero_addr g) > 0 /\
  SI.heap_objects_dense g /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> ~(is_gray x g))

val sweep_par_correct (bs: list nat) (g: heap)
  : Lemma (requires fused_pre g /\ valid_bounds g bs)
          (ensures sweep_par bs g == Defs.fused_sweep_coalesce g)

let sweep_par_correct bs g = admit ()

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// Every heap has a valid bs: the single segment [zero_addr, heap_size).
/// So the theorem covers every heap `fused_sweep_coalesce` is called on.
let whole_heap_bounds_valid (g: heap)
  : Lemma (valid_bounds g [U64.v zero_addr; heap_size])
  = ()

/// bs must start at zero_addr and end at heap_size: neither a missing
/// endpoint nor a lone boundary is accepted.
let invalid_bounds_rejected (g: heap)
  : Lemma (not (valid_bounds g []) /\
           not (valid_bounds g [U64.v zero_addr]) /\
           not (valid_bounds g [heap_size]) /\
           not (valid_bounds g [U64.v zero_addr; U64.v zero_addr; heap_size]))
  = ()
