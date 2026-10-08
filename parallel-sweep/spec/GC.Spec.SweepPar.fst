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
    walk_visits g zero_addr (U64.uint_to_t b) &&
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
