/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Cells - #46's free lists as lists of cells
/// ---------------------------------------------------------------------------
///
/// #46 states its free lists with fuel: `fl_valid`, `fl_chain_terminates` and
/// `chain_avoids` follow the links for `heap_words` steps.  The page allocator
/// unlinks a block from the middle of the large list and pushes blocks on it,
/// and both are plain list operations once the chain is a list.
///
/// `cells g fp cs` says the chain from `fp` visits exactly the cells `cs`, in
/// order, and then stops.  `cells_of` reads such a list off #46's predicates,
/// and `cells_valid` gives them back; both also say that `chain_avoids` and
/// `reachable_on_fl` are list membership.
///
/// `lview` is `large_ok` (L9) in these terms: list 0 is a list of free,
/// listable blocks that holds every free listable block, and the exact-fit
/// lists 1..16 are empty, since every listable block is larger than they hold
/// (condition C5).  `large_ok_lview` and `lview_large_ok` go back and forth.

module GC.Spec.Pages.Cells

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module FL = GC.Spec.FreeList
module FLs = GC.Spec.FreeLists
module AL = GC.Spec.Allocator.Lemmas
module Chain = GC.Spec.Allocator.Lemmas.Chain

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// An address the chain can visit.
let node (x: U64.t) : bool = U64.v x >= 8 && U64.v x < heap_size && U64.v x % 8 = 0

#push-options "--fuel 1"
let rec cells (g: heap) (fp: U64.t) (cs: list obj_addr) : Tot prop (decreases cs) =
  match cs with
  | [] -> ~(node fp)
  | c :: cs' ->
    fp == (c <: U64.t) /\ Seq.mem c (objects zero_addr g) /\
    U64.v (wosize_of_object c g) >= 1 /\
    cells g (read_word g (c <: hp_addr)) cs'
#pop-options

/// `chain_avoids` and `reachable_on_fl` are membership in `cs`.
let chain_is (g: heap) (fp: U64.t) (n: nat) (cs: list obj_addr) : prop =
  (forall (y: obj_addr). AL.chain_avoids g fp (y <: U64.t) n == not (L.mem y cs)) /\
  (forall (y: obj_addr). FL.reachable_on_fl g fp (y <: U64.t) <==> L.mem y cs)

let node_fl_node (x: U64.t)
  : Lemma (node x <==> FL.fl_node x)
  = assert (heap_size % 8 == 0)

let not_node_unreachable (g: heap) (fp y: U64.t)
  : Lemma (requires ~(node fp)) (ensures ~(FL.reachable_on_fl g fp y))
  = node_fl_node fp;
    introduce forall (n: nat). ~(FL.on_fl g fp y n)
    with (assert_norm (FL.on_fl g fp y n == (if n = 0 then false
                         else if not (FL.fl_node fp) then false
                         else if fp = y then true
                         else FL.on_fl g (FL.fl_next g fp) y (n - 1))))

/// A node visits itself first.
let head_not_avoided (g: heap) (fp: U64.t) (n: nat)
  : Lemma (requires node fp /\ n > 0) (ensures AL.chain_avoids g fp fp n = false)
  = if AL.chain_avoids g fp fp n then Chain.chain_avoids_head_ne g fp fp n

/// One step of both relations at a node.
let chain_step (g: heap) (fp: U64.t) (n: nat) (y: obj_addr)
  : Lemma (requires node fp /\ n > 0 /\ fp <> (y <: U64.t))
          (ensures AL.chain_avoids g fp (y <: U64.t) n ==
                     AL.chain_avoids g (read_word g (fp <: hp_addr)) (y <: U64.t) (n - 1) /\
                   (FL.reachable_on_fl g fp (y <: U64.t) <==>
                     FL.reachable_on_fl g (read_word g (fp <: hp_addr)) (y <: U64.t)))
  = let c : obj_addr = fp in
    hd_address_spec c;
    Chain.chain_avoids_unfold_step g fp (y <: U64.t) n;
    node_fl_node fp;
    assert (FL.fl_next g fp == read_word g (fp <: hp_addr));
    if FL.reachable_on_fl g fp (y <: U64.t) then FL.reachable_uncons g fp (y <: U64.t);
    if FL.reachable_on_fl g (FL.fl_next g fp) (y <: U64.t) then FL.reachable_cons g fp (y <: U64.t)

let chain_head (g: heap) (fp: U64.t) (n: nat)
  : Lemma (requires node fp /\ n > 0)
          (ensures AL.chain_avoids g fp fp n = false /\ FL.reachable_on_fl g fp fp)
  = head_not_avoided g fp n;
    node_fl_node fp;
    FL.reachable_head g fp

/// ---------------------------------------------------------------------------
/// From #46's predicates to a list
/// ---------------------------------------------------------------------------

/// The cells the chain from `fp` visits in `n` steps.
#push-options "--fuel 1"
let rec walk (g: heap) (fp: U64.t) (n: nat) : GTot (list obj_addr) (decreases n) =
  if n = 0 || not (node fp) then []
  else (fp <: obj_addr) :: walk g (read_word g (fp <: hp_addr)) (n - 1)
#pop-options

#push-options "--fuel 1 --z3rlimit 40"
let rec cells_of (g: heap) (fp: U64.t) (n: nat)
  : Lemma (requires AL.fl_valid g fp n /\ AL.fl_chain_terminates g fp n)
          (ensures (let cs = walk g fp n in
                    cells g fp cs /\ L.noRepeats cs /\ L.length cs <= n /\ chain_is g fp n cs))
          (decreases n)
  = if not (node fp) then begin
      let aux (y: obj_addr)
        : Lemma (AL.chain_avoids g fp (y <: U64.t) n == true /\ ~(FL.reachable_on_fl g fp (y <: U64.t)))
        = Chain.chain_avoids_terminal g fp (y <: U64.t) n;
          not_node_unreachable g fp (y <: U64.t)
      in
      FStar.Classical.forall_intro aux
    end else begin
      if n = 0 then Chain.fl_chain_terminates_valid_zero g fp;
      let c : obj_addr = fp in
      hd_address_spec c;
      AL.fl_valid_elim g fp n;
      Chain.fl_chain_terminates_elim g fp n;
      let nx = read_word g (fp <: hp_addr) in
      cells_of g nx (n - 1);
      let cs' = walk g nx (n - 1) in
      Chain.fl_chain_predecessor_not_in_suffix_b g fp n;
      Chain.not_in_fl_chain_b_is_chain_avoids g nx fp (n - 1);
      assert (not (L.mem c cs'));
      chain_head g fp n;
      let aux (y: obj_addr)
        : Lemma (AL.chain_avoids g fp (y <: U64.t) n == not (L.mem y (c :: cs')) /\
                 (FL.reachable_on_fl g fp (y <: U64.t) <==> L.mem y (c :: cs')))
        = if (y <: U64.t) = fp then () else chain_step g fp n y
      in
      FStar.Classical.forall_intro aux
    end
#pop-options

/// ---------------------------------------------------------------------------
/// From a list to #46's predicates
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --z3rlimit 40"
let rec cells_valid (g: heap) (fp: U64.t) (cs: list obj_addr) (n: nat)
  : Lemma (requires cells g fp cs /\ L.noRepeats cs /\ L.length cs <= n)
          (ensures AL.fl_valid g fp n /\ AL.fl_chain_terminates g fp n /\ chain_is g fp n cs)
          (decreases cs)
  = match cs with
    | [] ->
      if n = 0 then AL.fl_valid_zero g fp else AL.fl_valid_terminal g fp n;
      AL.fl_chain_terminates_terminal g fp n;
      let aux (y: obj_addr)
        : Lemma (AL.chain_avoids g fp (y <: U64.t) n == true /\ ~(FL.reachable_on_fl g fp (y <: U64.t)))
        = Chain.chain_avoids_terminal g fp (y <: U64.t) n;
          not_node_unreachable g fp (y <: U64.t)
      in
      FStar.Classical.forall_intro aux
    | c :: cs' ->
      hd_address_spec c;
      let nx = read_word g (c <: hp_addr) in
      cells_valid g nx cs' (n - 1);
      (match cs' with
       | [] -> ()
       | d :: _ -> assert (nx == (d <: U64.t)));
      AL.fl_valid_step g fp n;
      AL.fl_chain_terminates_step g fp n;
      chain_head g fp n;
      let aux (y: obj_addr)
        : Lemma (AL.chain_avoids g fp (y <: U64.t) n == not (L.mem y cs) /\
                 (FL.reachable_on_fl g fp (y <: U64.t) <==> L.mem y cs))
        = if (y <: U64.t) = fp then () else chain_step g fp n y
      in
      FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

/// The chain is the same in a heap that keeps every cell, its size class
/// floor and its link.
#push-options "--fuel 1"
let rec cells_frame (g g': heap) (fp: U64.t) (cs: list obj_addr)
  : Lemma (requires cells g fp cs /\
                    (forall (c: obj_addr). L.mem c cs ==>
                       Seq.mem c (objects zero_addr g') /\
                       U64.v (wosize_of_object c g') >= 1 /\
                       read_word g' (c <: hp_addr) == read_word g (c <: hp_addr)))
          (ensures cells g' fp cs)
          (decreases cs)
  = match cs with
    | [] -> ()
    | c :: cs' -> cells_frame g g' (read_word g (c <: hp_addr)) cs'
#pop-options

/// Every cell is an object with a link.
#push-options "--fuel 1"
let rec cells_mem (g: heap) (fp: U64.t) (cs: list obj_addr) (c: obj_addr)
  : Lemma (requires cells g fp cs /\ L.mem c cs)
          (ensures Seq.mem c (objects zero_addr g) /\ U64.v (wosize_of_object c g) >= 1)
          (decreases cs)
  = match cs with
    | d :: cs' -> if c = d then () else cells_mem g (read_word g (d <: hp_addr)) cs' c
#pop-options

/// ---------------------------------------------------------------------------
/// The large lists
/// ---------------------------------------------------------------------------

/// A listable block is on list 0 (C5).
let listable_class (g: heap) (pm: page_map) (y: obj_addr)
  : Lemma (requires large_listable g pm y)
          (ensures size_class (U64.v (wosize_of_object y g)) == 0 /\
                   U64.v (wosize_of_object y g) >= 1)
  = params_ok ()

let large_head (st: pstate) : U64.t = FLs.fls_head st.large 0

/// L9 as a list: list 0 is the cells `cs`, free and listable, and holds every
/// free listable block; the other lists are empty.
let lview (g: heap) (st: pstate) (cs: list obj_addr) : prop =
  Seq.length st.large == n_lists /\
  (forall (i: nat). 0 < i /\ i < n_lists ==> ~(node (FLs.fls_head st.large i))) /\
  cells g (large_head st) cs /\ L.noRepeats cs /\ L.length cs <= heap_words /\
  (forall (y: obj_addr). L.mem y cs ==> is_blue y g /\ large_listable g st.pm y) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\
     large_listable g st.pm y ==> L.mem y cs)

let heap_words_pos () : Lemma (heap_words > 0) = ()

/// An exact-fit list of a valid state is empty.
let small_list_empty (g: heap) (st: pstate) (i: nat)
  : Lemma (requires large_ok g st /\ 0 < i /\ i < n_lists)
          (ensures ~(node (FLs.fls_head st.large i)))
  = let h = FLs.fls_head st.large i in
    if node h then begin
      FLs.fls_valid_elim g st.large;
      let y : obj_addr = h in
      AL.fl_valid_gives_mem g h heap_words;
      head_not_avoided g h heap_words;
      FLs.fls_avoids_iff g st.large (y <: U64.t);
      assert (large_listable g st.pm y);
      listable_class g st.pm y;
      assert (FLs.chain_class g h i)
    end

let large_ok_lview (g: heap) (st: pstate)
  : Lemma (requires large_ok g st)
          (ensures lview g st (walk g (large_head st) heap_words))
  = let h = large_head st in
    FLs.fls_valid_elim g st.large;
    FLs.fls_terminates_elim g st.large;
    cells_of g h heap_words;
    let cs = walk g h heap_words in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (small_list_empty g st));
    let member (y: obj_addr)
      : Lemma (L.mem y cs ==> is_blue y g /\ large_listable g st.pm y)
      = if L.mem y cs then begin
          cells_mem g h cs y;
          assert (FL.fl_sound g (FLs.fls_head st.large 0));
          FLs.fls_avoids_iff g st.large (y <: U64.t)
        end
    in
    let complete (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g) /\ is_blue y g /\ large_listable g st.pm y)
              (ensures L.mem y cs)
      = listable_class g st.pm y
    in
    FStar.Classical.forall_intro member;
    FStar.Classical.forall_intro (FStar.Classical.move_requires complete)

let lview_large_ok (g: heap) (st: pstate) (cs: list obj_addr)
  : Lemma (requires lview g st cs)
          (ensures large_ok g st)
  = let fls = st.large in
    let h = large_head st in
    cells_valid g h cs heap_words;
    let per_list (i: nat)
      : Lemma (i < n_lists ==>
                 AL.fl_valid g (FLs.fls_head fls i) heap_words /\
                 FLs.chain_class g (FLs.fls_head fls i) i /\
                 AL.fl_chain_terminates g (FLs.fls_head fls i) heap_words /\
                 FL.fl_sound g (FLs.fls_head fls i))
      = if i < n_lists then begin
          let hi = FLs.fls_head fls i in
          if i = 0 then begin
            let cls0 (y: obj_addr)
              : Lemma (Seq.mem y (objects zero_addr g) /\ size_class (U64.v (wosize_of_object y g)) <> 0 ==>
                       AL.chain_avoids g hi (y <: U64.t) heap_words = true)
              = if L.mem y cs then listable_class g st.pm y
            in
            FStar.Classical.forall_intro cls0;
            let snd (y: U64.t)
              : Lemma (requires FL.reachable_on_fl g hi y)
                      (ensures
                       (FL.fl_node y /\
                        (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
                        Seq.mem (y <: obj_addr) (objects zero_addr g) /\
                        is_blue (y <: obj_addr) g /\
                        U64.v (wosize_of_object (y <: obj_addr) g) >= 1))
              = FL.reachable_is_node g hi y;
                node_fl_node y;
                let y' : obj_addr = y in
                cells_mem g h cs y'
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires snd)
          end else begin
            AL.fl_valid_terminal g hi heap_words;
            AL.fl_chain_terminates_terminal g hi heap_words;
            let av (y: obj_addr) : Lemma (AL.chain_avoids g hi (y <: U64.t) heap_words = true)
              = Chain.chain_avoids_terminal g hi (y <: U64.t) heap_words
            in
            FStar.Classical.forall_intro av;
            FStar.Classical.forall_intro (FStar.Classical.move_requires (not_node_unreachable g hi))
          end
        end
    in
    FStar.Classical.forall_intro per_list;
    FLs.fls_valid_intro g fls;
    FLs.fls_terminates_intro g fls;
    let avoid (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g) /\ ~(large_listable g st.pm y) ==>
               FLs.fls_avoids g fls (y <: U64.t))
      = FLs.fls_avoids_iff g fls (y <: U64.t);
        let l (i: nat) : Lemma (i < n_lists /\ ~(large_listable g st.pm y) ==>
                                AL.chain_avoids g (FLs.fls_head fls i) (y <: U64.t) heap_words = true)
          = if i > 0 && i < n_lists then
              Chain.chain_avoids_terminal g (FLs.fls_head fls i) (y <: U64.t) heap_words
        in
        FStar.Classical.forall_intro l
    in
    FStar.Classical.forall_intro avoid;
    let complete (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g) /\ is_blue y g /\ large_listable g st.pm y)
              (ensures FL.reachable_on_fl g (FLs.fls_head fls (size_class (U64.v (wosize_of_object y g)))) y)
      = listable_class g st.pm y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires complete)
