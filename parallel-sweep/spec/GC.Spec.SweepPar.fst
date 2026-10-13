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
/// It is proved below (the proof uses only `valid_bounds`, not the rest of
/// the precondition); see docs/parallel-sweep-phase1.md.
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
module SCH = GC.Spec.SweepCoalesce.Helpers
module FA = GC.Spec.SweepCoalesce.FlushAgree

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
/// is in the run, and the heads agree or `p` is not a link word written.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let flush_agree_at (h1 h2: heap) (r: run) (run_end: nat) (fp1 fp2: U64.t) (p: hp_addr)
  : Lemma (requires run_geom r run_end /\
                    (read_word h1 p == read_word h2 p \/
                     (r.rw > 0 /\ U64.v r.fb - U64.v mword <= U64.v p /\ U64.v p < run_end)) /\
                    (fp1 == fp2 \/ p <> r.fb \/ r.rw < 2))
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
/// Proof, part 4: one segment against the sequential pass
/// ---------------------------------------------------------------------------
///
/// The sequential pass enters a segment at its first boundary `lo` with a
/// heap `h`, a pending run `c0` ending at `lo`, and a head `p0`.  The
/// segment's own run starts from the input heap `g`, no run and head 0UL.
///
/// Lead phase (before the first survivor): neither side writes.  The
/// sequential run is `join c0 lead`.
///
/// At the first survivor, whose header is at `e`, the sequential pass
/// flushes `join c0 lead` with `p0`, giving (h1, f1).  The segment flushes
/// nothing.  Both whiten the survivor.
///
/// Seen phase (after it): both run the same steps on the same objects.  Their
/// heaps agree at and above `e`, except at the segment's first linked block
/// `a`, whose link word holds f1 in the sequential heap and 0UL in the
/// segment's.  Below `e` the sequential heap is h1 and the segment's is `g`.
///
/// Every write lands at or above `wlo`: the pending run's first word, or the
/// cursor when there is no run.  So facts about words below `wlo` persist.

/// Joining a run that ends where the next one starts.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 1"
let join_geom (a b: run) (m n: nat)
  : Lemma (requires run_geom a m /\ run_geom b n /\
                    (b.rw > 0 ==> U64.v b.fb - U64.v mword == m) /\
                    (b.rw = 0 ==> n == m))
          (ensures run_geom (join a b) n)
  = ()

let join_extend (a b: run) (obj: obj_addr) (ws: nat)
  : Lemma (extend (join a b) obj ws == join a (extend b obj ws))
  = ()

let join_no_run (a: run)
  : Lemma (requires a.rw = 0 ==> a == no_run)
          (ensures join a no_run == a)
  = ()
#pop-options

/// The first word any later step can write.
let wlo (cur: run) (c: nat) : int =
  if cur.rw > 0 then U64.v cur.fb - U64.v mword else c

let seen_inv (g: heap) (hi e: nat) (h1: heap) (f1: U64.t)
    (c: nat) (hs gs: heap) (cur: run) (fs fl: U64.t) (first: option U64.t) : prop =
  c % 8 == 0 /\ e <= c /\ c <= hi /\ hi <= heap_size /\ reach g c hi /\
  run_geom cur c /\ e <= wlo cur c /\
  (match first with
   | None -> fs == f1 /\ fl == 0UL
   | Some a -> fs == fl /\ e <= U64.v a /\ U64.v a >= U64.v mword /\ U64.v a % 8 == 0 /\
              U64.v a + U64.v mword <= wlo cur c) /\
  (forall (a: hp_addr). first == Some (a <: U64.t) ==> read_word hs a == f1) /\
  (forall (p: hp_addr). U64.v p < e ==>
     read_word hs p == read_word h1 p /\ read_word gs p == read_word g p) /\
  (forall (p: hp_addr). U64.v p >= e /\ first <> Some (p <: U64.t) ==>
     read_word hs p == read_word gs p) /\
  (forall (p: hp_addr). U64.v p >= wlo cur c ==>
     read_word hs p == read_word g p /\ read_word gs p == read_word g p)

let seen_post (g: heap) (hi e: nat) (h1: heap) (f1: U64.t) (lead: run)
    (o: seg_out) (hs: heap) (r: run) (fs: U64.t) : prop =
  o.all_free == false /\ o.lead == lead /\ r == o.trail /\
  (hi < heap_size ==> run_geom r hi) /\
  (match o.first_link with
   | None -> fs == f1
   | Some a -> fs == o.local_head /\ e <= U64.v a /\ U64.v a >= U64.v mword /\
              U64.v a % 8 == 0 /\ U64.v a + U64.v mword <= hi) /\
  (forall (a: hp_addr). o.first_link == Some (a <: U64.t) ==> read_word hs a == f1) /\
  (forall (p: hp_addr). U64.v p < e ==>
     read_word hs p == read_word h1 p /\ read_word o.sheap p == read_word g p) /\
  (forall (p: hp_addr). U64.v p >= e /\ o.first_link <> Some (p <: U64.t) ==>
     read_word hs p == read_word o.sheap p) /\
  (forall (p: hp_addr). U64.v p >= hi ==>
     read_word hs p == read_word g p /\ read_word o.sheap p == read_word g p)

/// Seen phase, a free object: the run grows, nothing is written.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let seen_free (g: heap) (hi e: nat) (h1: heap) (f1: U64.t)
    (c: nat) (hs gs: heap) (cur: run) (fs fl: U64.t) (first: option U64.t)
  : Lemma (requires seen_inv g hi e h1 f1 c hs gs cur fs fl first /\ c < hi /\
                    Seq.length (seg_rest g c hi) > 0)
          (ensures (let obj = Seq.head (seg_rest g c hi) in
                    let ws = U64.v (wosize_of_object obj g) in
                    seen_inv g hi e h1 f1 (c + (ws + 1) * 8) hs gs (extend cur obj ws) fs fl first))
  = seg_step g c hi;
    let obj = Seq.head (seg_rest g c hi) in
    let ws = U64.v (wosize_of_object obj g) in
    let next = c + (ws + 1) * 8 in
    assert (wlo (extend cur obj ws) next == wlo cur c)
#pop-options

/// Seen phase, a survivor: flush the pending run on both sides (with the
/// two heads), then whiten.  The first block linked becomes `a`.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let seen_black (g: heap) (hi e: nat) (h1: heap) (f1: U64.t)
    (c: nat) (hs gs: heap) (cur: run) (fs fl: U64.t) (first: option U64.t)
  : Lemma (requires seen_inv g hi e h1 f1 c hs gs cur fs fl first /\ c < hi /\
                    Seq.length (seg_rest g c hi) > 0)
          (ensures (let obj = Seq.head (seg_rest g c hi) in
                    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
                    let hf = SC.flush_blue hs cur.fb cur.rw fs in
                    let gf = SC.flush_blue gs cur.fb cur.rw fl in
                    let first' = match first with
                                 | Some _ -> first
                                 | None -> if snd gf <> fl then Some (snd gf) else None in
                    seen_inv g hi e h1 f1 next (makeWhite obj (fst hf)) (makeWhite obj (fst gf))
                      no_run (snd hf) (snd gf) first'))
  = seg_step g c hi;
    let obj = Seq.head (seg_rest g c hi) in
    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
    let hf = SC.flush_blue hs cur.fb cur.rw fs in
    let gf = SC.flush_blue gs cur.fb cur.rw fl in
    let hs1 = fst hf in
    let gs1 = fst gf in
    flush_head hs cur c fs;
    flush_head gs cur c fl;
    let first' = match first with
                 | Some _ -> first
                 | None -> if snd gf <> fl then Some (snd gf) else None in
    let hs2 = makeWhite obj hs1 in
    let gs2 = makeWhite obj gs1 in
    let cc : hp_addr = hd_address obj in
    flush_outside hs cur c fs cc;
    flush_outside gs cur c fl cc;
    white_same hs1 gs1 obj;
    if cur.rw >= 2 then begin
      flush_link_word hs cur c fs;
      white_other hs1 obj (cur.fb <: hp_addr)
    end;
    (match first with
     | Some a -> flush_outside hs cur c fs (a <: hp_addr); white_other hs1 obj (a <: hp_addr)
     | None -> ());
    let below (p: hp_addr)
      : Lemma (U64.v p < e ==>
               read_word hs2 p == read_word h1 p /\ read_word gs2 p == read_word g p)
      = if U64.v p < e then begin
          flush_outside hs cur c fs p; flush_outside gs cur c fl p;
          white_other hs1 obj p; white_other gs1 obj p
        end in
    let mid (p: hp_addr)
      : Lemma (U64.v p >= e /\ first' <> Some (p <: U64.t) ==>
               read_word hs2 p == read_word gs2 p)
      = if U64.v p >= e && first' <> Some (p <: U64.t) && p <> cc then begin
          white_other hs1 obj p; white_other gs1 obj p;
          flush_agree_at hs gs cur c fs fl p
        end in
    let above (p: hp_addr)
      : Lemma (U64.v p >= next ==>
               read_word hs2 p == read_word g p /\ read_word gs2 p == read_word g p)
      = if U64.v p >= next then begin
          flush_outside hs cur c fs p; flush_outside gs cur c fl p;
          white_other hs1 obj p; white_other gs1 obj p
        end in
    FStar.Classical.forall_intro below;
    FStar.Classical.forall_intro mid;
    FStar.Classical.forall_intro above
#pop-options

/// The seen phase, to the end of the segment.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec seen_phase (g: heap) (hi e: nat) (h1: heap) (f1: U64.t) (lead: run)
    (c: nat) (hs gs: heap) (cur: run) (fs fl: U64.t) (first: option U64.t)
  : Lemma (requires seen_inv g hi e h1 f1 c hs gs cur fs fl first)
          (ensures (let (hs', r', fs') = fsteps g hs (seg_rest g c hi) cur fs in
                    seen_post g hi e h1 f1 lead
                      (seg_aux g gs (seg_rest g c hi) true lead cur fl first) hs' r' fs'))
          (decreases Seq.length (seg_rest g c hi))
  = let objs = seg_rest g c hi in
    if Seq.length objs = 0 then begin
      if hi < heap_size then seg_empty_end g c hi
    end else begin
      seg_step g c hi;
      let obj = Seq.head objs in
      let ws = U64.v (wosize_of_object obj g) in
      let next = c + (ws + 1) * 8 in
      if is_black obj g then begin
        seen_black g hi e h1 f1 c hs gs cur fs fl first;
        let hf = SC.flush_blue hs cur.fb cur.rw fs in
        let gf = SC.flush_blue gs cur.fb cur.rw fl in
        let first' = match first with
                     | Some _ -> first
                     | None -> if snd gf <> fl then Some (snd gf) else None in
        seen_phase g hi e h1 f1 lead next
          (makeWhite obj (fst hf)) (makeWhite obj (fst gf)) no_run (snd hf) (snd gf) first'
      end else begin
        seen_free g hi e h1 f1 c hs gs cur fs fl first;
        seen_phase g hi e h1 f1 lead next hs gs (extend cur obj ws) fs fl first
      end
    end
#pop-options

let lead_inv (g: heap) (lo: hp_addr) (hi: nat) (h: heap) (c0: run) (c: nat) (lead: run) : prop =
  c % 8 == 0 /\ U64.v lo <= c /\ c <= hi /\ hi <= heap_size /\ reach g c hi /\
  run_geom c0 (U64.v lo) /\ run_geom lead c /\
  (lead.rw = 0 ==> c == U64.v lo) /\
  (lead.rw > 0 ==> U64.v lead.fb == U64.v lo + U64.v mword) /\
  (forall (p: hp_addr). U64.v p >= U64.v lo ==> read_word h p == read_word g p)

/// What a segment's result says about the sequential pass over it.
let seg_post (g h: heap) (c0: run) (p0: U64.t) (lo: hp_addr) (hi: nat)
    (o: seg_out) (hs: heap) (r: run) (fs: U64.t) : prop =
  (o.all_free == true ==>
     hs == h /\ r == join c0 o.lead /\ fs == p0 /\ o.sheap == g /\
     (hi < heap_size ==> run_geom r hi)) /\
  (o.all_free == false ==>
     (let e = U64.v lo + o.lead.rw * U64.v mword in
      let run = join c0 o.lead in
      let fl = SC.flush_blue h run.fb run.rw p0 in
      run_geom run e /\ e <= hi /\
      seen_post g hi e (fst fl) (snd fl) o.lead o hs r fs))

/// The first survivor: the sequential pass flushes the edge run, the
/// segment does not; both whiten.  The seen phase starts at `e = c`.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let lead_black (g h: heap) (c0: run) (p0: U64.t) (lo: hp_addr) (hi: nat) (c: nat) (lead: run)
  : Lemma (requires lead_inv g lo hi h c0 c lead /\ c < hi /\ Seq.length (seg_rest g c hi) > 0)
          (ensures (let obj = Seq.head (seg_rest g c hi) in
                    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
                    let run = join c0 lead in
                    let fl = SC.flush_blue h run.fb run.rw p0 in
                    run_geom run c /\
                    seen_inv g hi c (fst fl) (snd fl) next
                      (makeWhite obj (fst fl)) (makeWhite obj g) no_run (snd fl) 0UL None))
  = seg_step g c hi;
    let obj = Seq.head (seg_rest g c hi) in
    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
    join_geom c0 lead (U64.v lo) c;
    let run = join c0 lead in
    let h1 = fst (SC.flush_blue h run.fb run.rw p0) in
    let cc : hp_addr = hd_address obj in
    flush_outside h run c p0 cc;
    white_same h1 g obj;
    let below (p: hp_addr)
      : Lemma (U64.v p < c ==>
               read_word (makeWhite obj h1) p == read_word h1 p /\
               read_word (makeWhite obj g) p == read_word g p)
      = if U64.v p < c then begin white_other h1 obj p; white_other g obj p end in
    let at_or_above (p: hp_addr)
      : Lemma (U64.v p >= c ==>
               read_word (makeWhite obj h1) p == read_word (makeWhite obj g) p /\
               (U64.v p >= next ==>
                 read_word (makeWhite obj h1) p == read_word g p /\
                 read_word (makeWhite obj g) p == read_word g p))
      = if U64.v p >= c && p <> cc then begin
          white_other h1 obj p; white_other g obj p;
          flush_outside h run c p0 p
        end in
    FStar.Classical.forall_intro below;
    FStar.Classical.forall_intro at_or_above
#pop-options

/// The lead phase, to the first survivor or the end of the segment.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec lead_phase (g h: heap) (c0: run) (p0: U64.t) (lo: hp_addr) (hi: nat) (c: nat) (lead: run)
  : Lemma (requires lead_inv g lo hi h c0 c lead)
          (ensures (let (hs, r, fs) = fsteps g h (seg_rest g c hi) (join c0 lead) p0 in
                    seg_post g h c0 p0 lo hi
                      (seg_aux g g (seg_rest g c hi) false lead no_run 0UL None) hs r fs))
          (decreases Seq.length (seg_rest g c hi))
  = let objs = seg_rest g c hi in
    if Seq.length objs = 0 then begin
      if hi < heap_size then seg_empty_end g c hi;
      join_geom c0 lead (U64.v lo) c
    end else begin
      seg_step g c hi;
      let obj = Seq.head objs in
      let ws = U64.v (wosize_of_object obj g) in
      let next = c + (ws + 1) * 8 in
      if is_black obj g then begin
        lead_black g h c0 p0 lo hi c lead;
        let run = join c0 lead in
        let fl = SC.flush_blue h run.fb run.rw p0 in
        seen_phase g hi c (fst fl) (snd fl) lead next
          (makeWhite obj (fst fl)) (makeWhite obj g) no_run (snd fl) 0UL None
      end else begin
        join_extend c0 lead obj ws;
        lead_phase g h c0 p0 lo hi next (extend lead obj ws)
      end
    end
#pop-options

/// One segment, from its first boundary.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let segment_correct (g h: heap) (c0: run) (p0: U64.t) (lo: hp_addr) (hi: nat)
  : Lemma (requires U64.v lo < hi /\ hi <= heap_size /\ reach g (U64.v lo) hi /\
                    run_geom c0 (U64.v lo) /\
                    (forall (p: hp_addr). U64.v p >= U64.v lo ==> read_word h p == read_word g p))
          (ensures (let (hs, r, fs) = fsteps g h (seg_objects g lo hi) c0 p0 in
                    seg_post g h c0 p0 lo hi (sweep_segment g lo hi) hs r fs))
  = join_no_run c0;
    U64.v_inj (mk_hp_addr (U64.v lo)) lo;
    assert (seg_rest g (U64.v lo) hi == seg_objects g lo hi);
    lead_phase g h c0 p0 lo hi (U64.v lo) no_run
#pop-options

/// ---------------------------------------------------------------------------
/// Proof, part 5: splicing
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let splice_index (base src: heap) (lo: nat) (hi: nat{lo <= hi /\ hi <= heap_size})
    (i: nat{i < heap_size})
  : Lemma (Seq.index (splice base src lo hi) i ==
           (if lo <= i && i < hi then Seq.index src i else Seq.index base i))
  = ()
#pop-options

/// A word of a splice comes from `src` inside [lo, hi) and from `base`
/// outside (both ends are word-aligned, so no word straddles them).
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let splice_read (base src: heap) (lo: nat) (hi: nat{lo <= hi /\ hi <= heap_size}) (p: hp_addr)
  : Lemma (requires lo % 8 == 0 /\ hi % 8 == 0)
          (ensures read_word (splice base src lo hi) p ==
                   (if lo <= U64.v p && U64.v p < hi then read_word src p
                    else read_word base p))
  = let s = splice base src lo hi in
    let a = U64.v p in
    assert (a + 8 <= heap_size);
    read_word_spec s p; read_word_spec src p; read_word_spec base p;
    splice_index base src lo hi a;
    splice_index base src lo hi (a + 1);
    splice_index base src lo hi (a + 2);
    splice_index base src lo hi (a + 3);
    splice_index base src lo hi (a + 4);
    splice_index base src lo hi (a + 5);
    splice_index base src lo hi (a + 6);
    splice_index base src lo hi (a + 7)
#pop-options

/// Segments from `b` on leave the words below `b` alone.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec splice_all_below (g x: heap) (b: nat) (rest: list nat) (p: hp_addr)
  : Lemma (requires b % 8 == 0 /\ b < heap_size /\ bounds_from g b rest /\ U64.v p < b)
          (ensures read_word (splice_all x (sweep_all g (segments (b :: rest)))) p ==
                   read_word x p)
          (decreases rest)
  = match rest with
    | hi :: rest' ->
      let o = sweep_segment g (U64.uint_to_t b) hi in
      let x' = splice x o.sheap b hi in
      if Cons? rest' then splice_all_below g x' hi rest' p;
      splice_read x o.sheap b hi p
#pop-options

/// Splicing segment [b, hi), then the segments from `hi`.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let splice_seg (g x: heap) (b hi: nat) (rest: list nat) (p: hp_addr)
  : Lemma (requires b % 8 == 0 /\ b < hi /\ hi <= heap_size /\ hi % 8 == 0 /\
                    (hi < heap_size ==> bounds_from g hi rest) /\
                    (hi == heap_size ==> rest == []))
          (ensures (let o = sweep_segment g (U64.uint_to_t b) hi in
                    let x' = splice x o.sheap b hi in
                    (U64.v p < hi ==>
                       read_word (splice_all x' (sweep_all g (segments (hi :: rest)))) p ==
                       read_word x' p) /\
                    (b <= U64.v p /\ U64.v p < hi ==> read_word x' p == read_word o.sheap p) /\
                    (U64.v p < b ==> read_word x' p == read_word x p)))
  = let o = sweep_segment g (U64.uint_to_t b) hi in
    let x' = splice x o.sheap b hi in
    splice_read x o.sheap b hi p;
    if U64.v p < hi && hi < heap_size then splice_all_below g x' hi rest p
#pop-options

/// ---------------------------------------------------------------------------
/// Proof, part 6: one merge-and-link step
/// ---------------------------------------------------------------------------

/// What `link_all` does at one segment.
let link_one (gl: heap) (c: run) (fp: U64.t) (o: seg_out) : heap & run & U64.t =
  if o.all_free then (gl, join c o.lead, fp)
  else
    let run = join c o.lead in
    let (g1, fp1) = flush_blue_x gl run.fb run.rw fp in
    match o.first_link with
    | None -> (g1, o.trail, fp1)
    | Some a -> (patch_link g1 a fp1, o.trail, o.local_head)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let link_all_cons (gl: heap) (c: run) (fp: U64.t) (s: seg) (rs: list seg)
  : Lemma (link_all gl c fp (s :: rs) ==
           (let (g', c', fp') = link_one gl c fp s.out in link_all g' c' fp' rs))
  = ()
#pop-options

/// `sweep_all` and `splice_all`, unfolded at one valid segment.
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let sweep_all_cons (g x: heap) (b hi: nat) (rest: list nat)
  : Lemma (requires b < hi /\ hi <= heap_size /\ b % 8 == 0)
          (ensures (let o = sweep_segment g (U64.uint_to_t b) hi in
                    sweep_all g (segments (b :: hi :: rest)) ==
                      ({ lo = b; hi = hi; out = o } <: seg) :: sweep_all g (segments (hi :: rest)) /\
                    splice_all x (sweep_all g (segments (b :: hi :: rest))) ==
                      splice_all (splice x o.sheap b hi) (sweep_all g (segments (hi :: rest)))))
  = ()
#pop-options

/// The patch writes exactly the block's link word.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let patch_read (g: heap) (a: U64.t) (v: U64.t) (p: hp_addr)
  : Lemma (requires U64.v a >= U64.v mword /\ U64.v a % 8 == 0 /\
                    U64.v a + U64.v mword <= heap_size)
          (ensures read_word (patch_link g a v) p ==
                   (if U64.v p = U64.v a then v else read_word g p))
  = let ah : hp_addr = a in
    hd_address_spec (a <: obj_addr);
    let fa = U64.add (hd_address (a <: obj_addr)) (U64.mul mword 1UL) in
    U64.v_inj fa ah;
    if U64.v p = U64.v a then read_write_same g ah v
    else read_write_different g ah p v
#pop-options

/// The walk from boundary `b` on.
let objs_from (g: heap) (b: nat) : GTot (seq obj_addr) =
  if b < heap_size && b % 8 = 0 then objects (mk_hp_addr b) g else Seq.empty

/// At boundary `b`: the sequential heap `h` is still the input from `b` up;
/// the link heap `gl` equals `h` below `b` and the spliced segments from `b`
/// up; the carried run ends at `b`.
let link_inv (g: heap) (b: nat) (rest: list nat) (h gl: heap) (c: run) (x: heap) : prop =
  b % 8 == 0 /\ b <= heap_size /\
  (b < heap_size ==>
     CC.walk_visits g zero_addr (mk_hp_addr b) /\ bounds_from g b rest /\ run_geom c b) /\
  (b == heap_size ==> rest == []) /\
  (forall (p: hp_addr). U64.v p >= b ==> read_word h p == read_word g p) /\
  (forall (p: hp_addr). U64.v p < b ==> read_word gl p == read_word h p) /\
  (forall (p: hp_addr). U64.v p >= b ==>
     read_word gl p == read_word (splice_all x (sweep_all g (segments (b :: rest)))) p)

/// The boundaries after `b`, unfolded once.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let bounds_next (g: heap) (b hi: nat) (rest: list nat)
  : Lemma (requires bounds_from g b (hi :: rest))
          (ensures b < hi /\ hi <= heap_size /\ hi % 8 == 0 /\
                   (hi == heap_size <==> rest == []) /\
                   (hi < heap_size ==>
                      CC.walk_visits g zero_addr (mk_hp_addr hi) /\ bounds_from g hi rest))
  = match rest with
    | [] -> ()
    | _ :: _ -> ()
#pop-options

/// The step's walk facts: the sequential walk from `b` is the segment, then
/// the walk from `hi`; the segment's walk lands on `hi`.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let walk_step (g: heap) (b hi: nat) (rest: list nat)
  : Lemma (requires b % 8 == 0 /\ b < heap_size /\
                    CC.walk_visits g zero_addr (mk_hp_addr b) /\ bounds_from g b (hi :: rest))
          (ensures reach g b hi /\
                   objs_from g b == Seq.append (seg_objects g (mk_hp_addr b) hi) (objs_from g hi))
  = bounds_next g b hi rest;
    let lo = mk_hp_addr b in
    if hi < heap_size then begin
      let hh = mk_hp_addr hi in
      CC.walk_visits_prefix g lo hh;
      objects_seg_split g lo hh
    end else begin
      objects_seg_last g lo;
      Seq.append_empty_r (seg_objects g lo hi)
    end
#pop-options

/// An all-free segment: nothing written, the carried run grows.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 1"
let link_step_free (g: heap) (b hi: nat) (rest: list nat) (h gl: heap) (c: run) (fp: U64.t) (x: heap)
  : Lemma (requires link_inv g b (hi :: rest) h gl c x /\ b < heap_size /\
                    b < hi /\ hi <= heap_size /\ hi % 8 == 0 /\
                    (let lo = mk_hp_addr b in
                     let o = sweep_segment g lo hi in
                     let (hs, r, fs) = fsteps g h (seg_objects g lo hi) c fp in
                     o.all_free == true /\ seg_post g h c fp lo hi o hs r fs))
          (ensures (let lo = mk_hp_addr b in
                    let o = sweep_segment g lo hi in
                    let (hs, r, fs) = fsteps g h (seg_objects g lo hi) c fp in
                    let (gl', c', fp') = link_one gl c fp o in
                    c' == r /\ fp' == fs /\
                    link_inv g hi rest hs gl' c' (splice x o.sheap b hi)))
  = bounds_next g b hi rest;
    sweep_all_cons g x b hi rest;
    let lo = mk_hp_addr b in
    let o = sweep_segment g lo hi in
    let aux (p: hp_addr)
      : Lemma ((U64.v p < hi ==> read_word gl p == read_word h p) /\
               (U64.v p >= hi ==>
                  read_word gl p ==
                  read_word (splice_all (splice x o.sheap b hi)
                               (sweep_all g (segments (hi :: rest)))) p))
      = splice_seg g x b hi rest p in
    FStar.Classical.forall_intro aux
#pop-options

/// A segment with a survivor: flush the edge run once, patch the segment's
/// first linked block to the head after that flush.
#push-options "--z3rlimit 80 --fuel 0 --ifuel 1"
let link_step_used (g: heap) (b hi: nat) (rest: list nat) (h gl: heap) (c: run) (fp: U64.t) (x: heap)
  : Lemma (requires link_inv g b (hi :: rest) h gl c x /\ b < heap_size /\
                    b < hi /\ hi <= heap_size /\ hi % 8 == 0 /\
                    (let lo = mk_hp_addr b in
                     let o = sweep_segment g lo hi in
                     let (hs, r, fs) = fsteps g h (seg_objects g lo hi) c fp in
                     o.all_free == false /\ seg_post g h c fp lo hi o hs r fs))
          (ensures (let lo = mk_hp_addr b in
                    let o = sweep_segment g lo hi in
                    let (hs, r, fs) = fsteps g h (seg_objects g lo hi) c fp in
                    let (gl', c', fp') = link_one gl c fp o in
                    c' == r /\ fp' == fs /\
                    link_inv g hi rest hs gl' c' (splice x o.sheap b hi)))
  = bounds_next g b hi rest;
    sweep_all_cons g x b hi rest;
    let lo = mk_hp_addr b in
    let o = sweep_segment g lo hi in
    let hs = Mktuple3?._1 (fsteps g h (seg_objects g lo hi) c fp) in
    let e = b + o.lead.rw * 8 in
    let run = join c o.lead in
    let hf = SC.flush_blue h run.fb run.rw fp in
    let gf = SC.flush_blue gl run.fb run.rw fp in
    SCH.flush_blue_snd_heap_independent gl h run.fb run.rw fp;
    let gl' = Mktuple3?._1 (link_one gl c fp o) in
    let at (p: hp_addr)
      : Lemma ((U64.v p < hi ==> read_word gl' p == read_word hs p) /\
               (U64.v p >= hi ==>
                  read_word gl' p ==
                  read_word (splice_all (splice x o.sheap b hi)
                               (sweep_all g (segments (hi :: rest)))) p))
      = splice_seg g x b hi rest p;
        (match o.first_link with
         | Some a -> patch_read (fst gf) a (snd gf) p
         | None -> ());
        if U64.v p < e then flush_agree_at gl h run e fp fp p
        else flush_outside gl run e fp p in
    FStar.Classical.forall_intro at
#pop-options

/// One step: from boundary `b` to the next boundary `hi`.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let link_step (g: heap) (b hi: nat) (rest: list nat) (h gl: heap) (c: run) (fp: U64.t) (x: heap)
  : Lemma (requires link_inv g b (hi :: rest) h gl c x /\ b < heap_size)
          (ensures (let lo = mk_hp_addr b in
                    let o = sweep_segment g lo hi in
                    let (hs, r, fs) = fsteps g h (seg_objects g lo hi) c fp in
                    let (gl', c', fp') = link_one gl c fp o in
                    b < hi /\ hi <= heap_size /\
                    sweep_all g (segments (b :: hi :: rest)) ==
                      ({ lo = b; hi = hi; out = o } <: seg) :: sweep_all g (segments (hi :: rest)) /\
                    c' == r /\ fp' == fs /\
                    link_inv g hi rest hs gl' c' (splice x o.sheap b hi) /\
                    Defs.fused_aux g h (objs_from g b) c.fb c.rw fp ==
                      Defs.fused_aux g hs (objs_from g hi) r.fb r.rw fs))
  = bounds_next g b hi rest;
    sweep_all_cons g x b hi rest;
    walk_step g b hi rest;
    let lo = mk_hp_addr b in
    fused_aux_append g h (seg_objects g lo hi) (objs_from g hi) c fp;
    segment_correct g h c fp lo hi;
    let o = sweep_segment g lo hi in
    if o.all_free then link_step_free g b hi rest h gl c fp x
    else link_step_used g b hi rest h gl c fp x
#pop-options

/// The end of the heap: both sides flush the carried run on equal heaps.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let link_base (g: heap) (h gl: heap) (c: run) (fp: U64.t) (x: heap)
  : Lemma (requires link_inv g heap_size [] h gl c x)
          (ensures link_all gl c fp (sweep_all g (segments [heap_size])) ==
                   Defs.fused_aux g h (objs_from g heap_size) c.fb c.rw fp)
  = FA.heaps_word_agree_implies_equal gl h
#pop-options

/// The start: boundary `zero_addr`, both heaps the input.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let link_start (g: heap) (rest: list nat)
  : Lemma (requires valid_bounds g (U64.v zero_addr :: rest))
          (ensures link_inv g (U64.v zero_addr) rest g
                     (splice_all g (sweep_all g (segments (U64.v zero_addr :: rest)))) no_run g /\
                   objs_from g (U64.v zero_addr) == objects zero_addr g)
  = U64.v_inj (mk_hp_addr (U64.v zero_addr)) zero_addr;
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (splice_all_below g g (U64.v zero_addr) rest))
#pop-options

/// ---------------------------------------------------------------------------
/// Proof, part 7: two segments
/// ---------------------------------------------------------------------------

/// The sequential pass over two adjacent segments [zero_addr, b) and
/// [b, heap_size) equals the two segment results, with the run that crosses
/// `b` (the first segment's trailing run joined with the second's leading
/// run) flushed once.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let sweep_par_two (b: nat) (g: heap)
  : Lemma (requires valid_bounds g [U64.v zero_addr; b; heap_size])
          (ensures sweep_par [U64.v zero_addr; b; heap_size] g == Defs.fused_sweep_coalesce g)
  = let z = U64.v zero_addr in
    let rs = sweep_all g (segments [z; b; heap_size]) in
    let gl0 = splice_all g rs in
    link_start g [b; heap_size];
    link_step g z b [heap_size] g gl0 no_run 0UL g;
    let o1 = sweep_segment g (mk_hp_addr z) b in
    let (h1, c1, f1) = fsteps g g (seg_objects g (mk_hp_addr z) b) no_run 0UL in
    let (gl1, _, _) = link_one gl0 no_run 0UL o1 in
    let x1 = splice g o1.sheap z b in
    link_all_cons gl0 no_run 0UL (List.Tot.hd rs) (List.Tot.tl rs);
    link_step g b heap_size [] h1 gl1 c1 f1 x1;
    let o2 = sweep_segment g (mk_hp_addr b) heap_size in
    let (h2, c2, f2) = fsteps g h1 (seg_objects g (mk_hp_addr b) heap_size) c1 f1 in
    let (gl2, _, _) = link_one gl1 c1 f1 o2 in
    let x2 = splice x1 o2.sheap b heap_size in
    link_all_cons gl1 c1 f1 (List.Tot.hd (List.Tot.tl rs)) [];
    link_base g h2 gl2 c2 f2 x2
#pop-options

/// ---------------------------------------------------------------------------
/// Proof, part 8: any number of segments
/// ---------------------------------------------------------------------------

/// From boundary `b` to the end of the heap, by induction over the
/// remaining boundaries: one `link_step` per segment, then `link_base`.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec link_correct (g: heap) (b: nat) (rest: list nat)
    (h gl: heap) (c: run) (fp: U64.t) (x: heap)
  : Lemma (requires link_inv g b rest h gl c x)
          (ensures link_all gl c fp (sweep_all g (segments (b :: rest))) ==
                   Defs.fused_aux g h (objs_from g b) c.fb c.rw fp)
          (decreases rest)
  = if b = heap_size then link_base g h gl c fp x
    else match rest with
    | [] -> ()
    | hi :: rest' ->
      link_step g b hi rest' h gl c fp x;
      let lo = mk_hp_addr b in
      let o = sweep_segment g lo hi in
      let (hs, r, fs) = fsteps g h (seg_objects g lo hi) c fp in
      let (gl', c', fp') = link_one gl c fp o in
      link_all_cons gl c fp ({ lo = b; hi = hi; out = o } <: seg)
        (sweep_all g (segments (hi :: rest')));
      link_correct g hi rest' hs gl' c' fp' (splice x o.sheap b hi)
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

let sweep_par_correct bs g =
  match bs with
  | _ :: rest ->
    link_start g rest;
    link_correct g (U64.v zero_addr) rest
      g (splice_all g (sweep_all g (segments bs))) no_run 0UL g

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
