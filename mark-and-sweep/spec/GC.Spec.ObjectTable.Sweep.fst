/// ---------------------------------------------------------------------------
/// GC.Spec.ObjectTable.Sweep - the walk the fused sweep leaves, and its table
/// ---------------------------------------------------------------------------
///
/// The fused sweep-and-coalesce pass (`GC.Spec.SweepCoalesce.Lists`) visits
/// the walk of the marked heap `g` in ascending order.  The walk positions of
/// its output are exactly
///
///   * every black object (a survivor, whitened in place), and
///   * the first object of every run of non-black objects (the run is
///     flushed into one free block whose header is that object's).
///
/// `out_emit` lists them in that order, and `fused_objects` proves that it is
/// the output's walk.  The headers absorbed into a run are not walk positions
/// of the output, so a table rebuilt from `out_emit` names none of them
/// (docs/allocator-table-and-size-lists.md, C3).
///
/// The pass decides that an object is an output position at the object
/// itself -- a black object, or a non-black one that starts a run (`rw = 0`)
/// -- which is where the Pulse sweep writes the table (`cursor`).

module GC.Spec.ObjectTable.Sweep

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.ObjectTable

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecCoalesce = GC.Spec.Coalesce
module SCL = GC.Spec.SweepCoalesce.Lists
module FLs = GC.Spec.FreeLists

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The output positions
/// ---------------------------------------------------------------------------

/// The output walk positions of the pass over `objs`, given that a run of
/// non-black objects is pending exactly when `rw > 0` (its first object is
/// then already listed).
let rec out_emit (g0: heap) (objs: seq obj_addr) (rw: nat)
  : GTot (seq obj_addr) (decreases Seq.length objs)
  = if Seq.length objs = 0 then Seq.empty
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_black obj g0 then Seq.cons obj (out_emit g0 rest 0)
      else
        let ws = U64.v (wosize_of_object obj g0) in
        if rw = 0 then Seq.cons obj (out_emit g0 rest (ws + 1))
        else out_emit g0 rest (rw + ws + 1)

/// One step of `out_emit` at a walk position, as the Pulse loop takes it.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let out_emit_step (g0: heap) (v: hp_addr) (rw: nat)
  : Lemma (requires Seq.length (objects v g0) > 0)
          (ensures (let obj = f_address v in
                    let ws = U64.v (wosize_of_object obj g0) in
                    let next = U64.v v + (ws + 1) * 8 in
                    U64.v obj == U64.v v + 8 /\
                    ws == U64.v (getWosize (read_word g0 v)) /\
                    next <= heap_size /\ next % 8 == 0 /\
                    out_emit g0 (objs_from g0 (U64.v v)) rw ==
                      (if is_black obj g0 then Seq.cons obj (out_emit g0 (objs_from g0 next) 0)
                       else if rw = 0 then Seq.cons obj (out_emit g0 (objs_from g0 next) (ws + 1))
                       else out_emit g0 (objs_from g0 next) (rw + ws + 1))))
  = walk_shape v g0;
    let obj = f_address v in
    wosize_of_object_spec obj g0;
    hd_address_spec obj;
    U64.v_inj (hd_address obj) v;
    U64.v_inj (mk_hp_addr (U64.v v)) v
#pop-options

/// Past the last walk position there is nothing to emit.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let out_emit_end (g0: heap) (v: nat) (rw: nat)
  : Lemma (requires v <= heap_size /\ v % 8 == 0 /\ v + 8 >= heap_size)
          (ensures out_emit g0 (objs_from g0 v) rw == Seq.empty)
  = if v < heap_size then begin
      let s = objects (mk_hp_addr v) g0 in
      assert (Seq.length s == 0)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Walks that agree from a position on
/// ---------------------------------------------------------------------------

let agree_from (g1 g2: heap) (s: nat) : prop =
  forall (a: hp_addr). U64.v a >= s ==> read_word g1 a == read_word g2 a

let agree_below (g1 g2: heap) (s: nat) : prop =
  forall (a: hp_addr). U64.v a + 8 <= s ==> read_word g1 a == read_word g2 a

/// The walk from `start` reads only words at or above `start`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec objects_agree_from (start: hp_addr) (g1 g2: heap)
  : Lemma (requires agree_from g1 g2 (U64.v start))
          (ensures objects start g1 == objects start g2)
          (decreases (heap_size - U64.v start))
  = if U64.v start + 8 >= heap_size then ()
    else begin
      let wz = getWosize (read_word g1 start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size || next >= pow2 64 || next >= heap_size then ()
      else objects_agree_from (U64.uint_to_t next) g1 g2
    end
#pop-options

let objs_from_agree (g1 g2: heap) (s: nat)
  : Lemma (requires agree_from g1 g2 s)
          (ensures objs_from g1 s == objs_from g2 s)
  = if s < heap_size && s % 8 = 0 then objects_agree_from (mk_hp_addr s) g1 g2

/// A block whose header says wosize `w` at `s`: the walk from `s` is the block
/// followed by the walk from its end.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let walk_cons (s: hp_addr) (g: heap)
  : Lemma (requires (let w = U64.v (getWosize (read_word g s)) in
                     U64.v s + 8 < heap_size /\ U64.v s + (w + 1) * 8 <= heap_size))
          (ensures (let w = U64.v (getWosize (read_word g s)) in
                    U64.v (f_address s) == U64.v s + 8 /\
                    objects s g == Seq.cons (f_address s) (objs_from g (U64.v s + (w + 1) * 8))))
  = f_address_spec s;
    let w = U64.v (getWosize (read_word g s)) in
    let next = U64.v s + (w + 1) * 8 in
    aligned_plus_mul8 (U64.v s) (w + 1);
    if next >= heap_size then objects_cons_end s g
    else objects_cons_step_to s g (mk_hp_addr next)
#pop-options

/// ---------------------------------------------------------------------------
/// The induction over the pass
/// ---------------------------------------------------------------------------

/// The state of the pass: `objs` is the rest of the input walk, from
/// `start`; the heap agrees with the input from `start` on; a pending run
/// covers `[fb - 8, start)`.
let fw_inv (g0 g: heap) (start: nat) (objs: seq obj_addr) (fb: U64.t) (rw: nat) : prop =
  start <= heap_size /\ start % 8 == 0 /\
  objs == objs_from g0 start /\
  agree_from g g0 start /\
  (rw > 0 ==> U64.v fb >= 8 /\ U64.v fb < heap_size /\ U64.v fb % 8 == 0 /\
              U64.v fb - 8 + rw * 8 == start)

/// Where the output walk of the rest of the pass begins.
let sync_of (start: nat) (fb: U64.t) (rw: nat) : nat =
  if rw > 0 && U64.v fb >= 8 then U64.v fb - 8 else start

/// The pending run's first object, prepended.
let cons_run (fb: U64.t) (rw: nat) (s: seq obj_addr) : seq obj_addr =
  if rw > 0 && U64.v fb >= 8 && U64.v fb < heap_size && U64.v fb % 8 = 0
  then Seq.cons (fb <: obj_addr) s
  else s

/// A flush writes only inside the run.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let flush_frame (g: heap) (fb: U64.t) (rw: nat) (fp: U64.t) (start: nat)
  : Lemma (requires rw > 0 ==> U64.v fb >= 8 /\ U64.v fb < heap_size /\ U64.v fb % 8 == 0 /\
                               U64.v fb - 8 + rw * 8 == start)
          (ensures (let g' = fst (SpecCoalesce.flush_blue g fb rw fp) in
                    agree_from g' g start /\ agree_below g' g (sync_of start fb rw)))
  = let aux (a: hp_addr)
      : Lemma ((U64.v a >= start \/ U64.v a + 8 <= sync_of start fb rw) ==>
               read_word (fst (SpecCoalesce.flush_blue g fb rw fp)) a == read_word g a)
      = if U64.v a >= start || U64.v a + 8 <= sync_of start fb rw then
          SpecCoalesce.flush_blue_preserves_outside g fb rw fp a
    in
    FStar.Classical.forall_intro aux
#pop-options

/// The flushed run's header.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let flush_header (g: heap) (fb: U64.t) (rw: nat) (fp: U64.t) (start: nat)
  : Lemma (requires rw > 0 /\ U64.v fb >= 8 /\ U64.v fb < heap_size /\ U64.v fb % 8 == 0 /\
                    U64.v fb - 8 + rw * 8 == start /\ start <= heap_size)
          (ensures (let g' = fst (SpecCoalesce.flush_blue g fb rw fp) in
                    let s = mk_hp_addr (U64.v fb - 8) in
                    U64.v (getWosize (read_word g' s)) == rw - 1))
  = let fbo : obj_addr = fb in
    hd_address_spec fbo;
    assert_norm (pow2 57 / 8 == pow2 54);
    FStar.Math.Lemmas.lemma_div_le (rw * 8) heap_size 8;
    SpecCoalesce.flush_blue_header_spec g fbo rw fp;
    let wz : wosize = U64.uint_to_t (rw - 1) in
    makeHeader_getWosize wz Blue 0UL;
    U64.v_inj (hd_address fbo) (mk_hp_addr (U64.v fb - 8))
#pop-options

/// makeWhite writes one header and keeps its wosize.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let white_frame (g: heap) (obj: obj_addr)
  : Lemma (let g' = makeWhite obj g in
           let h = hd_address obj in
           getWosize (read_word g' h) == getWosize (read_word g h) /\
           (forall (a: hp_addr). a <> h ==> read_word g' a == read_word g a))
  = makeWhite_spec obj g;
    let h = hd_address obj in
    let v = colorHeader (read_word g h) White in
    read_write_same g h v;
    colorHeader_preserves_wosize (read_word g h) White;
    write_word_locality g h v
#pop-options

/// One step of the pass on a black object.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let fused_black_unfold (g0 g: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fls: FLs.fl_state)
  : Lemma (requires Seq.length objs > 0 /\ is_black (Seq.head objs) g0)
          (ensures (let r = SCL.flush_blue_lists g fb rw fls in
                    SCL.fused_aux_lists g0 g objs fb rw fls ==
                    SCL.fused_aux_lists g0 (makeWhite (Seq.head objs) (fst r)) (Seq.tail objs)
                      0UL 0 (snd r) /\
                    fst r == fst (SpecCoalesce.flush_blue g fb rw
                                   (FLs.fls_head fls (SCL.run_class rw)))))
  = ()

let fused_nonblack_unfold (g0 g: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fls: FLs.fl_state)
  : Lemma (requires Seq.length objs > 0 /\ not (is_black (Seq.head objs) g0))
          (ensures (let obj = Seq.head objs in
                    let ws = U64.v (wosize_of_object obj g0) in
                    let new_fb : U64.t = if rw = 0 then obj else fb in
                    SCL.fused_aux_lists g0 g objs fb rw fls ==
                    SCL.fused_aux_lists g0 g (Seq.tail objs) new_fb (rw + ws + 1) fls))
  = ()

let fused_empty_unfold (g0 g: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat) (fls: FLs.fl_state)
  : Lemma (requires Seq.length objs == 0)
          (ensures fst (SCL.fused_aux_lists g0 g objs fb rw fls) ==
                   fst (SpecCoalesce.flush_blue g fb rw (FLs.fls_head fls (SCL.run_class rw))))
  = ()

let out_emit_nil (g0: heap) (objs: seq obj_addr) (rw: nat)
  : Lemma (requires Seq.length objs == 0)
          (ensures out_emit g0 objs rw == Seq.empty)
  = ()

let out_emit_unfold (g0: heap) (objs: seq obj_addr) (rw: nat)
  : Lemma (requires Seq.length objs > 0)
          (ensures (let obj = Seq.head objs in
                    let rest = Seq.tail objs in
                    let ws = U64.v (wosize_of_object obj g0) in
                    out_emit g0 objs rw ==
                      (if is_black obj g0 then Seq.cons obj (out_emit g0 rest 0)
                       else if rw = 0 then Seq.cons obj (out_emit g0 rest (ws + 1))
                       else out_emit g0 rest (rw + ws + 1))))
  = ()
#pop-options

/// The run's block, in the output: its header, then the walk from `start`.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let run_block (gF: heap) (fb: U64.t) (rw: nat) (start: nat)
  : Lemma (requires rw > 0 /\ U64.v fb >= 8 /\ U64.v fb < heap_size /\ U64.v fb % 8 == 0 /\
                    U64.v fb - 8 + rw * 8 == start /\ start <= heap_size /\
                    U64.v (getWosize (read_word gF (mk_hp_addr (U64.v fb - 8)))) == rw - 1)
          (ensures objs_from gF (U64.v fb - 8) == cons_run fb rw (objs_from gF start))
  = let s = mk_hp_addr (U64.v fb - 8) in
    walk_cons s gF;
    U64.v_inj (f_address s) fb;
    U64.v_inj (mk_hp_addr (U64.v s)) s
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let rec fused_walk (g0 g: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat)
                   (fls: FLs.fl_state) (start: nat)
  : Lemma (requires fw_inv g0 g start objs fb rw)
          (ensures (let gF = fst (SCL.fused_aux_lists g0 g objs fb rw fls) in
                    let sy = sync_of start fb rw in
                    agree_below gF g sy /\
                    objs_from gF sy == cons_run fb rw (out_emit g0 objs rw)))
          (decreases Seq.length objs)
  = let gF = fst (SCL.fused_aux_lists g0 g objs fb rw fls) in
    if Seq.length objs = 0 then begin
      fused_empty_unfold g0 g objs fb rw fls;
      let fp = FLs.fls_head fls (SCL.run_class rw) in
      flush_frame g fb rw fp start;
      // the rest of the input walk is empty, and so is the output's
      objs_from_agree gF g0 start;
      out_emit_nil g0 objs rw;
      Seq.lemma_empty objs;
      if rw > 0 then begin
        flush_header g fb rw fp start;
        run_block gF fb rw start
      end
    end
    else begin
      let v = mk_hp_addr start in
      walk_shape v g0;
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      out_emit_step g0 v rw;
      out_emit_unfold g0 objs rw;
      let ws = U64.v (wosize_of_object obj g0) in
      let next = start + (ws + 1) * 8 in
      assert (rest == objs_from g0 next);
      if is_black obj g0 then begin
        fused_black_unfold g0 g objs fb rw fls;
        let r = SCL.flush_blue_lists g fb rw fls in
        let fp = FLs.fls_head fls (SCL.run_class rw) in
        let g' = fst r in
        flush_frame g fb rw fp start;
        let g'' = makeWhite obj g' in
        white_frame g' obj;
        hd_address_spec obj;
        U64.v_inj (hd_address obj) v;
        assert (agree_from g'' g0 next);
        fused_walk g0 g'' rest 0UL 0 (snd r) next;
        assert (gF == fst (SCL.fused_aux_lists g0 g'' rest 0UL 0 (snd r)));
        // the survivor's header keeps its wosize
        assert (read_word gF v == read_word g'' v);
        assert (getWosize (read_word gF v) == getWosize (read_word g0 v));
        walk_cons v gF;
        U64.v_inj (f_address v) obj;
        assert (objs_from gF start == Seq.cons obj (objs_from gF next));
        if rw > 0 then begin
          let s = mk_hp_addr (U64.v fb - 8) in
          flush_header g fb rw fp start;
          assert (read_word gF s == read_word g'' s);
          assert (read_word g'' s == read_word g' s);
          run_block gF fb rw start
        end
      end
      else begin
        fused_nonblack_unfold g0 g objs fb rw fls;
        let new_fb : U64.t = if rw = 0 then obj else fb in
        let new_rw = rw + ws + 1 in
        hd_address_spec obj;
        fused_walk g0 g rest new_fb new_rw fls next
      end
    end
#pop-options

/// **The output walk of the fused pass.**
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let fused_objects (g: heap)
  : Lemma (objects zero_addr (fst (SCL.fused_sweep_coalesce_lists g)) ==
           out_emit g (objects zero_addr g) 0)
  = U64.v_inj (mk_hp_addr (U64.v zero_addr)) zero_addr;
    fused_walk g g (objects zero_addr g) 0UL 0 FLs.fls_empty (U64.v zero_addr)
#pop-options

/// **The rebuilt table is the table of the output.**
let fused_table (g: heap) (t: seq U64.t)
  : Lemma (requires Seq.length t == n_windows)
          (ensures table_matches (fst (SCL.fused_sweep_coalesce_lists g))
                     (cursor (out_emit g (objects zero_addr g) 0) zero_addr 0 t))
  = fused_objects g;
    cursor_matches_seq (fst (SCL.fused_sweep_coalesce_lists g))
                       (out_emit g (objects zero_addr g) 0) t

/// ---------------------------------------------------------------------------
/// The rebuild, step by step, as the Pulse sweep takes it
/// ---------------------------------------------------------------------------

/// At a walk position `v` of the input: an output position (a black object,
/// or a non-black one with no run pending) emits its header; any other
/// object only extends the pending run.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let cursor_out_emit_step (g0: heap) (v: hp_addr) (rw: nat) (prev: U64.t) (k: nat)
                         (t: seq U64.t)
  : Lemma (requires Seq.length (objects v g0) > 0)
          (ensures (let obj = f_address v in
                    let ws = U64.v (wosize_of_object obj g0) in
                    let next = U64.v v + (ws + 1) * 8 in
                    let bl = is_black obj g0 in
                    U64.v obj == U64.v v + 8 /\
                    ws == U64.v (getWosize (read_word g0 v)) /\
                    next <= heap_size /\ next % 8 == 0 /\
                    cursor (out_emit g0 (objs_from g0 (U64.v v)) rw) prev k t ==
                      (if bl || rw = 0 then
                         (let r = emit t k prev (U64.v v) in
                          cursor (out_emit g0 (objs_from g0 next) (if bl then 0 else ws + 1))
                                 v (snd r) (fst r))
                       else cursor (out_emit g0 (objs_from g0 next) (rw + ws + 1)) prev k t)))
  = out_emit_step g0 v rw;
    let obj = f_address v in
    let ws = U64.v (wosize_of_object obj g0) in
    let next = U64.v v + (ws + 1) * 8 in
    let bl = is_black obj g0 in
    if bl || rw = 0 then begin
      let tl = out_emit g0 (objs_from g0 next) (if bl then 0 else ws + 1) in
      Seq.lemma_tl obj tl;
      Seq.head_cons obj tl;
      U64.v_inj (hd_of obj) v
    end
#pop-options

/// Past the last walk position, the rebuild fills the remaining windows.
let cursor_out_emit_end (g0: heap) (v: nat) (rw: nat) (prev: U64.t) (k: nat) (t: seq U64.t)
  : Lemma (requires v <= heap_size /\ v % 8 == 0 /\ v + 8 >= heap_size)
          (ensures cursor (out_emit g0 (objs_from g0 v) rw) prev k t ==
                   fst (emit t k prev heap_size))
  = out_emit_end g0 v rw;
    cursor_empty prev k t

/// ---------------------------------------------------------------------------
/// After a collection
/// ---------------------------------------------------------------------------

module Corr = GC.Spec.Correctness
module SpecSweep = GC.Spec.Sweep
module HA = GC.Spec.HeapAgree
module CDense = GC.Spec.Coalesce.Dense

/// The heap a collection leaves tiles the heap, so a table that matches its
/// walk is `table_ok`.  Density comes from the coalescer's heap, which the
/// collector's agrees with up to free blocks' bodies and links.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let collect_table_ok (h_init h_mark: heap) (roots: seq obj_addr) (s2: heap) (t: seq U64.t)
  : Lemma (requires Corr.mark_post h_init h_mark roots 0UL /\
                    HA.heaps_agree_mod_free_links s2
                      (fst (SpecCoalesce.coalesce (fst (SpecSweep.sweep h_mark 0UL)))) /\
                    table_matches s2 t)
          (ensures table_ok s2 t)
  = let g = fst (SpecSweep.sweep h_mark 0UL) in
    Corr.sweep_post_sweep_strong_gen h_init h_mark roots 0UL;
    Corr.coalesce_precondition_bridge_gen h_init h_mark roots 0UL;
    CDense.coalesce_dense g;
    HA.agree_dense_links s2 (fst (SpecCoalesce.coalesce g));
    table_ok_intro s2 t
#pop-options
