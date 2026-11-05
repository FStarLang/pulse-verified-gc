module GC.Gen.MarkState

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GMM = GC.Gen.MarkPhase.Minor
module MM = GC.Spec.MarkPhase.Mutator
module SPM = GC.Spec.SweepPhase.Mutator
module Promote = GC.Gen.Promote
module Mark = GC.Spec.Mark
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let mark_cache_marking g st ov = reveal_opaque (`%mark_cache_ok) (mark_cache_ok g Ph.Marking st ov)

let mark_cache_not_marking g ph st ov = reveal_opaque (`%mark_cache_ok) (mark_cache_ok g ph st ov)

let mark_cache_empty g ph =
  reveal_opaque (`%mark_cache_ok) (mark_cache_ok g ph Seq.empty false)

let mark_cache_off g g' ph ph' st ov =
  mark_cache_not_marking g ph st ov;
  mark_cache_not_marking g' ph' st ov

let mark_cache_same_greys g g' ph st ov =
  reveal_opaque (`%mark_cache_ok) (mark_cache_ok g ph st ov);
  reveal_opaque (`%mark_cache_ok) (mark_cache_ok g' ph st ov)

let mark_cache_write g ph st ov x a v =
  MM.write_heads g x a v;
  mark_cache_same_greys g (write_word g a v) ph st ov

/// Greying the white block `t` greys `t` and nothing else.
let grey_greys (g: heap) (t: obj_addr)
  : Lemma (requires Seq.mem t (objects zero_addr g) /\ is_white t g)
          (ensures (forall (y: obj_addr). grey_obj (makeGray t g) y <==> (y == t \/ grey_obj g y)) /\
                   ~(grey_obj g t))
  = let g1 = makeGray t g in
    makeGray_eq t g;
    makeGray_is_gray t g;
    color_change_preserves_objects g t Header.Gray;
    Mark.colors_exclusive t g;
    let col (y: obj_addr)
      : Lemma (y <> t ==> (is_gray y g1 <==> is_gray y g))
      = if y <> t then begin
          color_change_preserves_other_color t y g Header.Gray;
          is_gray_iff y g; is_gray_iff y g1
        end
    in
    FStar.Classical.forall_intro col

#push-options "--z3rlimit 20"
let mark_cache_darken g st ov w cap =
  mark_cache_marking g st ov;
  let ov' = ov || Seq.length st = cap in
  if darken_target g w then begin
    let t = resolve_object (w <: obj_addr) g in
    let st' = if Seq.length st < cap then Seq.cons t st else st in
    let g1 = makeGray t g in
    grey_greys g t;
    let mem_cons (y: obj_addr)
      : Lemma (Seq.mem y st' <==> ((Seq.length st < cap /\ y == t) \/ Seq.mem y st))
      = if Seq.length st < cap then Seq.mem_cons t st
    in
    FStar.Classical.forall_intro mem_cons;
    assert (MM.darken g w == g1);
    mark_cache_marking g1 st' ov'
  end else begin
    assert (MM.darken g w == g);
    mark_cache_marking g st ov'
  end
#pop-options

let mark_cache_minor minor g fp roots st ov =
  let g' = (GMM.collect_marking minor g fp roots).Promote.mc_major in
  FStar.Classical.forall_intro (GMM.minor_keeps_greys minor g fp roots);
  mark_cache_same_greys g g' Ph.Marking st ov
