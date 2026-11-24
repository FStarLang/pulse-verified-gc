/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Run - rewriting a free block of a swept run
/// ---------------------------------------------------------------------------
///
/// The large allocator carves an object out of a free block of a swept run,
/// and unlinking a block writes the link of the block before it on the list.
/// Both rewrite one free block `[a, e)` of the run into blocks that are white
/// or blue, no two blue ones adjacent.  `run_after_replace` shows the run
/// then keeps its shape (L6) and its swept clause (L7):
///   - the walk still steps over the run;
///   - a new blue block lies inside the old free block, which covered no
///     whole page, so it covers none either;
///   - the old free block's neighbours were not blue (L7), so a new blue
///     block at either end of the stretch has no blue neighbour.

module GC.Spec.Pages.Run

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Replace

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The new blocks of `[a, e)` are white or blue, and no two blue ones are
/// adjacent.
let layout_ok (g': heap) (a e: nat) : prop =
  (forall (b: nat). steps_to g' a b /\ b < e ==>
     color_at g' b == White \/ color_at g' b == Blue) /\
  (forall (b: nat). steps_to g' a b /\ b < e /\ color_at g' b == Blue /\
     b + words_at g' b * 8 < e ==> color_at g' (b + words_at g' b * 8) =!= Blue)

/// The setting: `[a, e)` is one free block of the swept run at page `h`.
let run_ctx (g g': heap) (pm: page_map) (h: nat{h < n_pages}) (a e: nat) : prop =
  LargeHead? (entry pm h).kind /\ (entry pm h).swept == true /\
  (let n = run_len (entry pm h).kind in
   run_shape g h n /\ run_swept_ok g pm h /\
   replaces g g' a e /\
   page_base h <= a /\ e <= page_base (h + n) /\ steps_to g (page_base h) a /\
   color_at g a == Blue /\ e == a + words_at g a * 8 /\
   layout_ok g' a e)

let run_shape_after (g g': heap) (pm: page_map) (h: nat{h < n_pages}) (a e: nat)
  : Lemma (requires run_ctx g g' pm h a e)
          (ensures run_shape g' h (run_len (entry pm h).kind))
  = let n = run_len (entry pm h).kind in
    let s = page_base h in
    let t = page_base (h + n) in
    steps_to_frame g g' s a;
    steps_to_det g s a t;
    steps_to_refl g a;
    block_before g a a t;
    steps_to_frame g g' e t;
    steps_to_trans g' s a e;
    steps_to_trans g' s e t

/// The facts of L7 at one block of the old run.
let old_block (g: heap) (pm: page_map) (h: nat{h < n_pages}) (b: nat)
  : Lemma (requires LargeHead? (entry pm h).kind /\ (entry pm h).swept == true /\
                    run_swept_ok g pm h /\ run_block g h (run_len (entry pm h).kind) b)
          (ensures (let n = run_len (entry pm h).kind in
                    (color_at g b == White \/ color_at g b == Blue) /\
                    (color_at g b == Blue /\ b + words_at g b * 8 < page_base (h + n) ==>
                       color_at g (b + words_at g b * 8) =!= Blue) /\
                    (color_at g b == Blue ==>
                       (forall (j: nat). h <= j /\ j < h + n ==>
                          ~(b <= page_base j /\ page_base (j + 1) <= b + words_at g b * 8)))))
  = ()

/// The L7 clauses at block `b` of the run of `n` pages at `h`.
let l7_at (g: heap) (h: nat) (n: pos) (b: nat) : prop =
  (color_at g b == White \/ color_at g b == Blue) /\
  (color_at g b == Blue /\ b + words_at g b * 8 < page_base (h + n) ==>
     color_at g (b + words_at g b * 8) =!= Blue) /\
  (color_at g b == Blue ==>
     (forall (j: nat). h <= j /\ j < h + n ==>
        ~(b <= page_base j /\ page_base (j + 1) <= b + words_at g b * 8)))

let before_core (g g': heap) (h: nat) (n: pos) (a b: nat)
  : Lemma (requires l7_at g h n b /\ color_at g a == Blue /\ a < page_base (h + n) /\
                    hdr g' b == hdr g b /\ b + words_at g b * 8 <= a /\
                    (b + words_at g b * 8 < a ==>
                       hdr g' (b + words_at g b * 8) == hdr g (b + words_at g b * 8)))
          (ensures l7_at g' h n b)
  = ()

/// A block of the new run before the stretch.
let before_block (g g': heap) (pm: page_map) (h: nat{h < n_pages}) (a e b: nat)
  : Lemma (requires run_ctx g g' pm h a e /\ run_block g' h (run_len (entry pm h).kind) b /\ b < a)
          (ensures l7_at g' h (run_len (entry pm h).kind) b)
  = let s = page_base h in
    steps_to_frame g g' s b;
    old_block g pm h b;
    block_before g s b a;
    let nx = b + words_at g b * 8 in
    if nx < a then steps_to_le g nx a;
    before_core g g' h (run_len (entry pm h).kind) a b

let after_core (g g': heap) (h: nat) (n: pos) (b: nat)
  : Lemma (requires l7_at g h n b /\ hdr g' b == hdr g b /\
                    (b + words_at g b * 8 < page_base (h + n) ==>
                       hdr g' (b + words_at g b * 8) == hdr g (b + words_at g b * 8)))
          (ensures l7_at g' h n b)
  = ()

/// A block of the new run after the stretch.
let after_block (g g': heap) (pm: page_map) (h: nat{h < n_pages}) (a e b: nat)
  : Lemma (requires run_ctx g g' pm h a e /\ run_block g' h (run_len (entry pm h).kind) b /\ b >= e)
          (ensures l7_at g' h (run_len (entry pm h).kind) b)
  = let n = run_len (entry pm h).kind in
    let s = page_base h in
    steps_to_frame g g' s a;
    steps_to_trans g' s a e;
    steps_to_det g' s e b;
    steps_to_frame g g' e b;
    steps_to_trans g s a e;
    steps_to_trans g s e b;
    old_block g pm h b;
    steps_to_le g e b;
    after_core g g' h n b

let inside_core (g g': heap) (h: nat) (n: pos) (a e b: nat)
  : Lemma (requires l7_at g h n a /\ color_at g a == Blue /\ e == a + words_at g a * 8 /\
                    a <= b /\ b + words_at g' b * 8 <= e /\
                    (color_at g' b == White \/ color_at g' b == Blue) /\
                    (color_at g' b == Blue /\ b + words_at g' b * 8 < e ==>
                       color_at g' (b + words_at g' b * 8) =!= Blue) /\
                    (e < page_base (h + n) ==> hdr g' e == hdr g e))
          (ensures l7_at g' h n b)
  = ()

/// A block of the stretch.
let inside_block (g g': heap) (pm: page_map) (h: nat{h < n_pages}) (a e b: nat)
  : Lemma (requires run_ctx g g' pm h a e /\ run_block g' h (run_len (entry pm h).kind) b /\
                    a <= b /\ b < e)
          (ensures l7_at g' h (run_len (entry pm h).kind) b)
  = let n = run_len (entry pm h).kind in
    let s = page_base h in
    steps_to_frame g g' s a;
    steps_to_det g' s a b;
    block_before g' a b e;
    steps_to_refl g a;
    old_block g pm h a;
    inside_core g g' h n a e b

/// **A swept run keeps L6 and L7 when one of its free blocks is rewritten.**
let run_after_replace (g g': heap) (pm: page_map) (h: nat{h < n_pages}) (a e: nat)
  : Lemma (requires run_ctx g g' pm h a e)
          (ensures run_shape g' h (run_len (entry pm h).kind) /\ run_swept_ok g' pm h)
  = run_shape_after g g' pm h a e;
    let n = run_len (entry pm h).kind in
    let aux (b: nat)
      : Lemma (requires run_block g' h n b)
              (ensures l7_at g' h n b)
      = if b < a then before_block g g' pm h a e b
        else if b < e then inside_block g g' pm h a e b
        else after_block g g' pm h a e b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
