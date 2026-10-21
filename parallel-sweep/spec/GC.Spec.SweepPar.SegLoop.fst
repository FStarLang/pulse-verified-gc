/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPar.SegLoop — the loop of GC.Impl.SweepSegment, on the model
///
/// The Pulse loop of `sweep_segment` keeps the model's `seg_aux` state: the
/// cursor `c`, the segment's copy of the heap `h`, whether a survivor has
/// been passed, the leading and current runs, the local head and the first
/// linked block.  `seg_inv` says that running `seg_aux` from that state over
/// the rest of the segment gives the model's result, and holds the facts
/// that keep every read and write inside [lo, hi).  One lemma per case of
/// the loop body takes it one object further.
/// ---------------------------------------------------------------------------
module GC.Spec.SweepPar.SegLoop

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.SweepPar.Exec
open GC.Spec.SweepPar

module SC = GC.Spec.Coalesce
module CC = GC.Spec.Coalesce.Correct
module CL = GC.Impl.Coalesce.Lemmas
module FL = GC.Impl.FusedSweepCoalesce.Lemmas
module Header = GC.Lib.Header
module IO = GC.Impl.Object

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// A pending run inside [lo, c): it ends at the cursor.
let run_in (lo: nat) (c: nat) (r: run) : prop =
  r.rw > 0 ==>
    U64.v r.fb >= 8 /\ U64.v r.fb < heap_size /\ U64.v r.fb % 8 == 0 /\
    lo <= U64.v r.fb - 8 /\ U64.v r.fb - 8 + r.rw * 8 == c

let seg_inv (g: heap) (lo: hp_addr) (hi: nat) (c: nat) (h: heap)
    (seen: bool) (lead cur: run) (fp: U64.t) (first: option U64.t) : prop =
  U64.v lo <= c /\ c <= hi /\ hi <= heap_size /\ c % 8 == 0 /\ hi % 8 == 0 /\
  reach g c hi /\
  seg_aux g h (seg_rest g c hi) seen lead cur fp first == sweep_segment g lo hi /\
  (forall (p: hp_addr). U64.v p >= c ==> read_word h p == read_word g p) /\
  lead.rw * 8 <= c - U64.v lo /\
  cur.rw * 8 <= c - U64.v lo /\
  run_in (U64.v lo) c cur /\
  (seen == false ==> cur.rw == 0) /\
  (lead.rw > 0 ==> U64.v lead.fb == U64.v lo + 8 /\ U64.v lo + 8 < heap_size) /\
  (seen == false ==> U64.v lo + lead.rw * 8 == c)

/// ---------------------------------------------------------------------------
/// Entry
/// ---------------------------------------------------------------------------

/// The segment's pair is consecutive boundaries, so the walk from `lo`
/// lands on `hi`.
#push-options "--fuel 2 --ifuel 1"
let rec seg_mem_reach (g: heap) (prev: nat) (bs: list nat) (lo hi: nat)
  : Lemma (requires prev % 8 == 0 /\ prev < heap_size /\
                    CC.walk_visits g zero_addr (mk_hp_addr prev) /\
                    bounds_from g prev bs /\
                    List.Tot.memP (lo, hi) (segments (prev :: bs)))
          (ensures lo < hi /\ hi <= heap_size /\ hi % 8 == 0 /\ lo % 8 == 0 /\
                   lo < heap_size /\ reach g lo hi)
          (decreases bs)
  = match bs with
    | b :: rest ->
      bounds_next g prev b rest;
      if lo = prev && hi = b then walk_step g prev b rest
      else seg_mem_reach g b rest lo hi
#pop-options

/// The entry state of a segment the walk from `lo` reaches.
let seg_entry_reach (g: heap) (lo: hp_addr) (hi: nat)
  : Lemma (requires reach g (U64.v lo) hi /\ U64.v lo < hi /\ hi <= heap_size /\ hi % 8 == 0)
          (ensures seg_inv g lo hi (U64.v lo) g false no_run no_run 0UL None)
  = assert (mk_hp_addr (U64.v lo) == lo)

let seg_entry (g: heap) (bs: list nat) (lo: hp_addr) (hi: nat)
  : Lemma (requires valid_bounds g bs /\ List.Tot.memP (U64.v lo, hi) (segments bs) /\
                    hi <= heap_size)
          (ensures seg_inv g lo hi (U64.v lo) g false no_run no_run 0UL None)
  = match bs with
    | b0 :: rest ->
      seg_mem_reach g b0 rest (U64.v lo) hi;
      seg_entry_reach g lo hi

/// ---------------------------------------------------------------------------
/// The loop test
/// ---------------------------------------------------------------------------

/// The segment still has an object at the cursor exactly when the cursor is
/// below `hi`, a header fits, and the object ends inside the heap.
#push-options "--fuel 1 --ifuel 0"
let seg_more (g: heap) (c: nat) (hi: nat)
  : Lemma (requires c % 8 == 0)
          (ensures (Seq.length (seg_rest g c hi) > 0 <==>
                    (c < hi /\ c + 8 < heap_size /\
                     c + (U64.v (getWosize (read_word g (mk_hp_addr c))) + 1) * 8 <= heap_size)))
  = if c < hi && c + 8 < heap_size then begin
      let cc = mk_hp_addr c in
      let wz = getWosize (read_word g cc) in
      let next = c + (U64.v wz + 1) * 8 in
      aligned_plus_mul8 c (U64.v wz + 1);
      if next <= heap_size then begin
        f_address_spec cc;
        let o : obj_addr = f_address cc in
        let tl = if next < heap_size then seg_objects g (mk_hp_addr next) hi else Seq.empty in
        assert (seg_objects g cc hi == Seq.cons o tl)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// One object
/// ---------------------------------------------------------------------------

/// Two aligned positions, one below the other, are a word apart at least.
let aligned_lt (c hi: nat)
  : Lemma (requires c % 8 == 0 /\ hi % 8 == 0 /\ c < hi) (ensures c + 8 <= hi)
  = FStar.Math.Lemmas.lemma_div_exact c 8;
    FStar.Math.Lemmas.lemma_div_exact hi 8

/// The facts the loop body reads off the header at the cursor.
let head_facts (g: heap) (lo: hp_addr) (hi: nat) (c: nat) (h: heap)
    (seen: bool) (lead cur: run) (fp: U64.t) (first: option U64.t) (hdr: U64.t)
  : Lemma (requires seg_inv g lo hi c h seen lead cur fp first /\
                    c < hi /\ c + 8 < heap_size /\
                    hdr == read_word h (mk_hp_addr c))
          (ensures hdr == read_word g (mk_hp_addr c) /\
                   c + 8 <= hi /\
                   (let obj : obj_addr = U64.uint_to_t (c + 8) in
                    hd_address obj == mk_hp_addr c /\
                    (is_black obj g <==> IO.getColor hdr == Header.Black) /\
                    wosize_of_object obj g == getWosize hdr))
  = let cc = mk_hp_addr c in
    f_address_spec cc;
    hd_f_roundtrip cc;
    let obj = f_address cc in
    assert (obj == U64.uint_to_t (c + 8));
    color_of_object_spec obj g;
    is_black_iff obj g;
    IO.getColor_eq hdr;
    wosize_of_object_spec obj g;
    aligned_lt c hi

/// pow2 57 is heap_size's bound, and 8 * pow2 54.
let pow2_57 () : Lemma (pow2 57 == 8 * pow2 54) = assert_norm (pow2 57 == 8 * pow2 54)

/// A free object: it joins the leading run before the first survivor, and
/// the current run after it.  Nothing is written.
#push-options "--fuel 1 --ifuel 1"
let step_free (g: heap) (lo: hp_addr) (hi: nat) (c: nat) (h: heap)
    (seen: bool) (lead cur: run) (fp: U64.t) (first: option U64.t)
  : Lemma (requires seg_inv g lo hi c h seen lead cur fp first /\
                    Seq.length (seg_rest g c hi) > 0 /\
                    c + 8 < heap_size /\
                    ~(is_black (U64.uint_to_t (c + 8)) g))
          (ensures (let obj : obj_addr = U64.uint_to_t (c + 8) in
                    let ws = U64.v (wosize_of_object obj g) in
                    let next = c + (ws + 1) * 8 in
                    seg_inv g lo hi next h seen
                      (if seen then lead else extend lead obj ws)
                      (if seen then extend cur obj ws else cur) fp first))
  = seg_step g c hi;
    let objs = seg_rest g c hi in
    let obj : obj_addr = U64.uint_to_t (c + 8) in
    U64.v_inj (Seq.head objs) obj;
    let ws = U64.v (wosize_of_object obj g) in
    let next = c + (ws + 1) * 8 in
    let lead' = if seen then lead else extend lead obj ws in
    let cur' = if seen then extend cur obj ws else cur in
    assert (Seq.tail objs == seg_rest g next hi);
    assert (is_black_x obj g == false);
    assert (seg_aux g h objs seen lead cur fp first ==
            seg_aux g h (seg_rest g next hi) seen lead' cur' fp first);
    assert (lead'.rw * 8 <= next - U64.v lo);
    assert (cur'.rw * 8 <= next - U64.v lo);
    assert (run_in (U64.v lo) next cur')
#pop-options

/// The first survivor: whitened, and the leading run stays unflushed.
#push-options "--fuel 1 --ifuel 1"
let step_black_first (g: heap) (lo: hp_addr) (hi: nat) (c: nat) (h: heap)
    (lead cur: run) (fp: U64.t) (first: option U64.t)
  : Lemma (requires seg_inv g lo hi c h false lead cur fp first /\
                    Seq.length (seg_rest g c hi) > 0 /\
                    c + 8 < heap_size /\
                    is_black (U64.uint_to_t (c + 8)) g)
          (ensures (let obj : obj_addr = U64.uint_to_t (c + 8) in
                    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
                    is_black obj h /\
                    seg_inv g lo hi next (makeWhite obj h) true lead no_run fp first))
  = seg_step g c hi;
    let obj : obj_addr = U64.uint_to_t (c + 8) in
    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
    FL.is_black_from_original g h obj (mk_hp_addr c);
    hd_address_spec obj;
    FL.makeWhite_suffix_preserved h obj next
#pop-options

/// A later survivor: the current run is flushed, then the survivor whitened.
#push-options "--fuel 1 --ifuel 1"
let step_black_seen (g: heap) (lo: hp_addr) (hi: nat) (c: nat) (h: heap)
    (lead cur: run) (fp: U64.t) (first: option U64.t)
  : Lemma (requires seg_inv g lo hi c h true lead cur fp first /\
                    Seq.length (seg_rest g c hi) > 0 /\
                    c + 8 < heap_size /\
                    is_black (U64.uint_to_t (c + 8)) g)
          (ensures (let obj : obj_addr = U64.uint_to_t (c + 8) in
                    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
                    let (h1, fp') = SC.flush_blue h cur.fb cur.rw fp in
                    let first' =
                      match first with
                      | Some _ -> first
                      | None -> if fp' <> fp then Some fp' else None in
                    is_black obj h1 /\
                    seg_inv g lo hi next (makeWhite obj h1) true lead no_run fp' first'))
  = seg_step g c hi;
    let obj : obj_addr = U64.uint_to_t (c + 8) in
    let next = c + (U64.v (wosize_of_object obj g) + 1) * 8 in
    CL.flush_blue_suffix_preserved h cur.fb cur.rw fp c;
    let (h1, _) = SC.flush_blue h cur.fb cur.rw fp in
    FL.is_black_from_original g h1 obj (mk_hp_addr c);
    hd_address_spec obj;
    FL.makeWhite_suffix_preserved h1 obj next
#pop-options

/// ---------------------------------------------------------------------------
/// Exit
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1"
let seg_exit (g: heap) (lo: hp_addr) (hi: nat) (c: nat) (h: heap)
    (seen: bool) (lead cur: run) (fp: U64.t) (first: option U64.t)
  : Lemma (requires seg_inv g lo hi c h seen lead cur fp first /\
                    Seq.length (seg_rest g c hi) == 0)
          (ensures sweep_segment g lo hi ==
                   { sheap = h; all_free = not seen; lead = lead; trail = cur;
                     first_link = first; local_head = fp })
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// Where a segment's runs lie
/// ---------------------------------------------------------------------------

/// The merge flushes these runs, so it needs them inside the heap.  The
/// leading run starts at the segment's first object and ends by `hi`; the
/// trailing run lies in [lo, hi); an all-free segment has no trailing run.
let out_geom (lo hi: nat) (o: seg_out) : prop =
  run_in lo (lo + o.lead.rw * 8) o.lead /\ lo + o.lead.rw * 8 <= hi /\
  (o.trail.rw > 0 ==>
     U64.v o.trail.fb >= 8 /\ U64.v o.trail.fb < heap_size /\ U64.v o.trail.fb % 8 == 0 /\
     lo <= U64.v o.trail.fb - 8 /\ U64.v o.trail.fb - 8 + o.trail.rw * 8 <= hi) /\
  (o.all_free ==> o.trail.rw == 0)

/// From any state of the loop, by running it to the end.
#push-options "--fuel 0 --ifuel 1"
let rec seg_geom_from (g: heap) (lo: hp_addr) (hi: nat) (c: nat) (h: heap)
    (seen: bool) (lead cur: run) (fp: U64.t) (first: option U64.t)
  : Lemma (requires seg_inv g lo hi c h seen lead cur fp first)
          (ensures out_geom (U64.v lo) hi (sweep_segment g lo hi))
          (decreases (heap_size - c))
  = if Seq.length (seg_rest g c hi) = 0 then
      seg_exit g lo hi c h seen lead cur fp first
    else begin
      seg_more g c hi;
      let obj : obj_addr = U64.uint_to_t (c + 8) in
      let ws = U64.v (wosize_of_object obj g) in
      let next = c + (ws + 1) * 8 in
      if is_black obj g then begin
        if seen then begin
          step_black_seen g lo hi c h lead cur fp first;
          let (h1, fp') = SC.flush_blue h cur.fb cur.rw fp in
          let first' =
            match first with
            | Some _ -> first
            | None -> if fp' <> fp then Some fp' else None in
          seg_geom_from g lo hi next (makeWhite obj h1) true lead no_run fp' first'
        end else begin
          step_black_first g lo hi c h lead cur fp first;
          seg_geom_from g lo hi next (makeWhite obj h) true lead no_run fp first
        end
      end else begin
        step_free g lo hi c h seen lead cur fp first;
        seg_geom_from g lo hi next h seen
          (if seen then lead else extend lead obj ws)
          (if seen then extend cur obj ws else cur) fp first
      end
    end
#pop-options

/// A segment the walk from `lo` reaches.
let seg_geom (g: heap) (lo: hp_addr) (hi: nat)
  : Lemma (requires reach g (U64.v lo) hi /\ U64.v lo < hi /\ hi <= heap_size /\ hi % 8 == 0)
          (ensures out_geom (U64.v lo) hi (sweep_segment g lo hi))
  = seg_entry_reach g lo hi;
    seg_geom_from g lo hi (U64.v lo) g false no_run no_run 0UL None

/// ---------------------------------------------------------------------------
/// The loop's own variables
/// ---------------------------------------------------------------------------
///
/// The Pulse loop holds machine values: each run as a first block and a
/// U64 word count, and the first linked block as a flag and a value (0UL
/// while unset).  `loop_inv` is `seg_inv` on those values.  It is opaque, so
/// the Pulse proof carries it as one fact; the lemmas below are the only
/// way in and out.

let mk_run (fb rw: U64.t) : run = { fb = fb; rw = U64.v rw }

let opt_link (has: bool) (a: U64.t) : option U64.t = if has then Some a else None

[@@"opaque_to_smt"]
let loop_inv (g: heap) (lo: hp_addr) (hi: nat) (c: U64.t) (h: heap) (seen: bool)
    (lfb lrw cfb crw fp: U64.t) (has: bool) (fl: U64.t) : prop =
  seg_inv g lo hi (U64.v c) h seen (mk_run lfb lrw) (mk_run cfb crw) fp (opt_link has fl) /\
  (has == false ==> fl == 0UL)

let loop_entry (g: heap) (bs: list nat) (lo: hp_addr) (hi: U64.t)
  : Lemma (requires valid_bounds g bs /\ List.Tot.memP (U64.v lo, U64.v hi) (segments bs) /\
                    U64.v hi <= heap_size)
          (ensures loop_inv g lo (U64.v hi) lo g false 0UL 0UL 0UL 0UL 0UL false 0UL)
  = seg_entry g bs lo (U64.v hi);
    reveal_opaque (`%loop_inv) loop_inv

/// What the loop body needs to know about its own variables.
let loop_facts (g: heap) (lo: hp_addr) (hi: nat) (c: U64.t) (h: heap) (seen: bool)
    (lfb lrw cfb crw fp: U64.t) (has: bool) (fl: U64.t)
  : Lemma (requires loop_inv g lo hi c h seen lfb lrw cfb crw fp has fl)
          (ensures U64.v lo <= U64.v c /\ U64.v c <= hi /\ hi <= heap_size /\
                   U64.v c % 8 == 0 /\ hi % 8 == 0 /\
                   U64.v lrw < pow2 54 /\ U64.v crw < pow2 54 /\
                   (U64.v crw > 0 ==>
                      U64.v cfb >= 8 /\ U64.v cfb < heap_size /\ U64.v cfb % 8 == 0 /\
                      U64.v lo <= U64.v cfb - 8 /\ U64.v cfb - 8 + U64.v crw * 8 <= hi) /\
                   (seen == false ==> U64.v crw == 0))
  = reveal_opaque (`%loop_inv) loop_inv;
    pow2_57 ()

/// The loop test: whether the segment has another object at the cursor.
let loop_more (g: heap) (lo: hp_addr) (hi: nat) (c: U64.t) (h: heap) (seen: bool)
    (lfb lrw cfb crw fp: U64.t) (has: bool) (fl: U64.t)
  : Lemma (requires loop_inv g lo hi c h seen lfb lrw cfb crw fp has fl /\
                    ~(U64.v c < hi /\ U64.v c + 8 < heap_size))
          (ensures Seq.length (seg_rest g (U64.v c) hi) == 0)
  = reveal_opaque (`%loop_inv) loop_inv;
    seg_more g (U64.v c) hi

/// The header at the cursor, read from the segment's copy, is g's; from it
/// the loop decides whether there is an object, and whether it survives.
let loop_head (g: heap) (lo: hp_addr) (hi: nat) (c: U64.t) (h: heap) (seen: bool)
    (lfb lrw cfb crw fp: U64.t) (has: bool) (fl: U64.t) (hdr: U64.t)
  : Lemma (requires loop_inv g lo hi c h seen lfb lrw cfb crw fp has fl /\
                    U64.v c % 8 == 0 /\ U64.v c < hi /\ U64.v c + 8 < heap_size /\
                    hdr == read_word h (mk_hp_addr (U64.v c)))
          (ensures (let wz = IO.getWosize hdr in
                    let obj : obj_addr = U64.uint_to_t (U64.v c + 8) in
                    U64.v c + 8 <= hi /\
                    (Seq.length (seg_rest g (U64.v c) hi) > 0 <==>
                       U64.v c + (U64.v wz + 1) * 8 <= heap_size) /\
                    (is_black obj g <==> IO.getColor hdr == Header.Black)))
  = reveal_opaque (`%loop_inv) loop_inv;
    head_facts g lo hi (U64.v c) h seen (mk_run lfb lrw) (mk_run cfb crw) fp
      (opt_link has fl) hdr;
    IO.getWosize_eq hdr;
    seg_more g (U64.v c) hi

/// A free object.  `nrw` is the grown run's word count.
let loop_free (g: heap) (lo: hp_addr) (hi: nat) (c: U64.t) (h: heap) (seen: bool)
    (lfb lrw cfb crw fp: U64.t) (has: bool) (fl: U64.t) (hdr: U64.t)
    (obj next nrw: U64.t)
  : Lemma (requires loop_inv g lo hi c h seen lfb lrw cfb crw fp has fl /\
                    U64.v c % 8 == 0 /\ U64.v c < hi /\ U64.v c + 8 < heap_size /\
                    hdr == read_word h (mk_hp_addr (U64.v c)) /\
                    U64.v c + (U64.v (IO.getWosize hdr) + 1) * 8 <= heap_size /\
                    ~(IO.getColor hdr == Header.Black) /\
                    U64.v obj == U64.v c + 8 /\
                    U64.v next == U64.v c + (U64.v (IO.getWosize hdr) + 1) * 8 /\
                    U64.v nrw == (if seen then U64.v crw else U64.v lrw) +
                                 U64.v (IO.getWosize hdr) + 1)
          (ensures (if seen
                    then loop_inv g lo hi next h seen lfb lrw
                           (if U64.v crw = 0 then obj else cfb) nrw fp has fl
                    else loop_inv g lo hi next h seen
                           (if U64.v lrw = 0 then obj else lfb) nrw cfb crw fp has fl))
  = reveal_opaque (`%loop_inv) loop_inv;
    let cu = U64.v c in
    head_facts g lo hi cu h seen (mk_run lfb lrw) (mk_run cfb crw) fp (opt_link has fl) hdr;
    IO.getWosize_eq hdr;
    seg_more g cu hi;
    U64.v_inj obj (U64.uint_to_t (cu + 8));
    step_free g lo hi cu h seen (mk_run lfb lrw) (mk_run cfb crw) fp (opt_link has fl)

/// The first survivor.  The current run is empty, so it is reset to 0UL.
let loop_black_first (g: heap) (lo: hp_addr) (hi: nat) (c: U64.t) (h: heap)
    (lfb lrw cfb crw fp: U64.t) (has: bool) (fl: U64.t) (hdr: U64.t)
    (obj: obj_addr) (next: U64.t)
  : Lemma (requires loop_inv g lo hi c h false lfb lrw cfb crw fp has fl /\
                    U64.v c % 8 == 0 /\ U64.v c < hi /\ U64.v c + 8 < heap_size /\
                    hdr == read_word h (mk_hp_addr (U64.v c)) /\
                    U64.v c + (U64.v (IO.getWosize hdr) + 1) * 8 <= heap_size /\
                    IO.getColor hdr == Header.Black /\
                    U64.v obj == U64.v c + 8 /\
                    U64.v next == U64.v c + (U64.v (IO.getWosize hdr) + 1) * 8)
          (ensures is_black obj h /\ U64.v obj - 8 + 8 <= hi /\ U64.v lo <= U64.v obj - 8 /\
                   loop_inv g lo hi next (makeWhite obj h) true lfb lrw 0UL 0UL fp has fl)
  = reveal_opaque (`%loop_inv) loop_inv;
    let cu = U64.v c in
    head_facts g lo hi cu h false (mk_run lfb lrw) (mk_run cfb crw) fp (opt_link has fl) hdr;
    IO.getWosize_eq hdr;
    seg_more g cu hi;
    U64.v_inj obj (U64.uint_to_t (cu + 8));
    step_black_first g lo hi cu h (mk_run lfb lrw) (mk_run cfb crw) fp (opt_link has fl)

/// A later survivor, after its run is flushed: `h1` and `fp'` are the
/// flush's result, `has'` and `fl'` the first-link record updated by it.
let loop_black_seen (g: heap) (lo: hp_addr) (hi: nat) (c: U64.t) (h: heap)
    (lfb lrw cfb crw fp: U64.t) (has: bool) (fl: U64.t) (hdr: U64.t)
    (obj: obj_addr) (next: U64.t) (h1: heap) (fp': U64.t) (has': bool) (fl': U64.t)
  : Lemma (requires loop_inv g lo hi c h true lfb lrw cfb crw fp has fl /\
                    U64.v c % 8 == 0 /\ U64.v c < hi /\ U64.v c + 8 < heap_size /\
                    hdr == read_word h (mk_hp_addr (U64.v c)) /\
                    U64.v c + (U64.v (IO.getWosize hdr) + 1) * 8 <= heap_size /\
                    IO.getColor hdr == Header.Black /\
                    U64.v obj == U64.v c + 8 /\
                    U64.v next == U64.v c + (U64.v (IO.getWosize hdr) + 1) * 8 /\
                    h1 == fst (SC.flush_blue h cfb (U64.v crw) fp) /\
                    fp' == snd (SC.flush_blue h cfb (U64.v crw) fp) /\
                    has' == (has || fp' <> fp) /\
                    fl' == (if not has && fp' <> fp then fp' else fl))
          (ensures is_black obj h1 /\ U64.v obj - 8 + 8 <= hi /\ U64.v lo <= U64.v obj - 8 /\
                   loop_inv g lo hi next (makeWhite obj h1) true lfb lrw 0UL 0UL fp' has' fl')
  = reveal_opaque (`%loop_inv) loop_inv;
    let cu = U64.v c in
    head_facts g lo hi cu h true (mk_run lfb lrw) (mk_run cfb crw) fp (opt_link has fl) hdr;
    IO.getWosize_eq hdr;
    seg_more g cu hi;
    U64.v_inj obj (U64.uint_to_t (cu + 8));
    step_black_seen g lo hi cu h (mk_run lfb lrw) (mk_run cfb crw) fp (opt_link has fl)

/// The end of the segment: the loop's variables are the model's outputs.
let loop_exit (g: heap) (lo: hp_addr) (hi: nat) (c: U64.t) (h: heap) (seen: bool)
    (lfb lrw cfb crw fp: U64.t) (has: bool) (fl: U64.t)
  : Lemma (requires loop_inv g lo hi c h seen lfb lrw cfb crw fp has fl /\
                    Seq.length (seg_rest g (U64.v c) hi) == 0)
          (ensures (let o = sweep_segment g lo hi in
                    o.sheap == h /\ o.all_free == not seen /\
                    o.lead == mk_run lfb lrw /\ o.trail == mk_run cfb crw /\
                    o.first_link == opt_link has fl /\ o.local_head == fp /\
                    (has == false ==> fl == 0UL)))
  = reveal_opaque (`%loop_inv) loop_inv;
    seg_exit g lo hi (U64.v c) h seen (mk_run lfb lrw) (mk_run cfb crw) fp (opt_link has fl)

/// ---------------------------------------------------------------------------
/// Non-vacuity
/// ---------------------------------------------------------------------------

/// The loop lemmas, called in the order the loop calls them, from the entry
/// state of the whole heap as one segment.  The entry and the first header
/// need nothing of the heap; each later case is guarded by the shape that
/// leads to it (the first object free and filling the heap; the first two
/// objects black).  `seg_inv`'s lemmas are reached through these.
#push-options "--fuel 2 --ifuel 1"
let seg_witness (g: heap) : unit =
  let z = zero_addr in
  let hi = heap_size_u64 in
  whole_heap_bounds_valid g;
  assert (List.Tot.memP (U64.v z, heap_size) (segments [U64.v z; heap_size]));
  loop_entry g [U64.v z; heap_size] z hi;
  loop_facts g z heap_size z g false 0UL 0UL 0UL 0UL 0UL false 0UL;
  let hdr = read_word g z in
  assert (mk_hp_addr (U64.v z) == z);
  loop_head g z heap_size z g false 0UL 0UL 0UL 0UL 0UL false 0UL hdr;
  let wz = IO.getWosize hdr in
  let nx = U64.v z + (U64.v wz + 1) * 8 in
  if nx <= heap_size then begin
    aligned_plus_mul8 (U64.v z) 1;
    let obj : obj_addr = U64.uint_to_t (U64.v z + 8) in
    let next = U64.uint_to_t nx in
    if IO.getColor hdr = Header.Black then begin
      loop_black_first g z heap_size z g 0UL 0UL 0UL 0UL 0UL false 0UL hdr obj next;
      let h1 = makeWhite obj g in
      if nx + 8 < heap_size then begin
        aligned_plus_mul8 (U64.v z) (U64.v wz + 1);
        loop_facts g z heap_size next h1 true 0UL 0UL 0UL 0UL 0UL false 0UL;
        let hdr2 = read_word h1 (mk_hp_addr nx) in
        loop_head g z heap_size next h1 true 0UL 0UL 0UL 0UL 0UL false 0UL hdr2;
        let nx2 = nx + (U64.v (IO.getWosize hdr2) + 1) * 8 in
        if nx2 <= heap_size && IO.getColor hdr2 = Header.Black then begin
          aligned_plus_mul8 nx 1;
          let (h2, fp2) = SC.flush_blue h1 0UL 0 0UL in
          loop_black_seen g z heap_size next h1 0UL 0UL 0UL 0UL 0UL false 0UL hdr2
            (U64.uint_to_t (nx + 8)) (U64.uint_to_t nx2) h2 fp2
            (false || fp2 <> 0UL) (if fp2 <> 0UL then fp2 else 0UL)
        end
      end
    end else begin
      let nrw = U64.uint_to_t (U64.v wz + 1) in
      loop_free g z heap_size z g false 0UL 0UL 0UL 0UL 0UL false 0UL hdr obj next nrw;
      if nx = heap_size then begin
        loop_more g z heap_size next g false obj nrw 0UL 0UL 0UL false 0UL;
        loop_exit g z heap_size next g false obj nrw 0UL 0UL 0UL false 0UL
      end
    end
  end
#pop-options
