/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.MidSweepAlloc - allocation keeps the mid-sweep invariant
/// ---------------------------------------------------------------------------
///
/// Plan §20.4.  From `MidSweep.pages_ok_sw`, the `Sweeping` allocator
/// (white, swept pages only) gives:
///
///   - **`alloc_sw_ok`**: `alloc_ok`'s guarantees, and every heap the caller
///     makes by writing the new object's fields with values that are not
///     free mid-sweep (`field_ok_with (free_sw pm)`) satisfies `pages_ok_sw`;
///   - main's five allocator facts (plan §20.1): the colour (`colour_at`:
///     white, the new object being in a swept page), only the new object
///     comes into use, every other block is kept, the walk reaches the end
///     of the heap, and the invariant is kept;
///   - **`pages_allocator_sw`**: the page allocator as an `AllocIface`
///     instance whose `Sweeping` invariant is `pages_ok_sw`, with
///     `allocator_ok_with` at `free_sw` while sweeping.
///
/// The caller's heap is related to the surrogate's (`MidSweep.alloc_relate`):
/// scrubbing the dead objects of the caller's heap gives a heap the caller
/// of the surrogate's allocation could have written, so `alloc_correct`
/// gives it `pages_ok` and `well_formed_heap`, which carry back to all but
/// the pointer clauses.  Those follow from the blocks in use being those of
/// `g` and the new object (`NewOnly`), through main's `wf_transport`.

module GC.Spec.Pages.MidSweepAlloc

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
open GC.Spec.Pages.MidSweep

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module G = GC.Spec.Pages.Graft
module Sc = GC.Spec.Pages.Scrub
module NO = GC.Spec.Pages.NewOnly
module A = GC.Spec.Pages.Alloc
module Th = GC.Spec.Pages.Theorems
module F = GC.Spec.Pages.Fill
module R = GC.Spec.Pages.Replace
module SPI = GC.Spec.SweepPhase.Intrinsic
module FT = GC.Spec.FieldTarget
module I = GC.Spec.AllocIface

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The caller's heap and the surrogate's
/// ---------------------------------------------------------------------------

/// The setting after a successful allocation `x` from `g`, and the caller's
/// writes `g''`; `gk` is the surrogate, `gk'` its allocation.
let after (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr) : prop =
  sctx g st zs /\ gk == Sc.scrub g zs /\
  pages_ok gk st /\ well_formed_heap gk /\ Th.alloc_ok gk gk' st st' (U64.v (wosize_of_object x g')) x /\
  Sc.objs gk' zs /\ Sc.objs g zs /\ same_objs gk g /\ same_objs g' gk' /\
  (forall (z: obj_addr). L.mem z zs ==> read_word gk' (hd_address z) == read_word g (hd_address z)) /\
  (forall (a: hp_addr). G.uw st.pm (U64.v a) ==> read_word g' a == read_word g a) /\
  (forall (a: hp_addr). ~(Sc.in_fields gk' zs (U64.v a)) ==> read_word g' a == read_word gk' a) /\
  same_swept st.pm st'.pm /\
  Seq.mem x (objects zero_addr g') /\ is_white x g' /\ ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
  (forall (a: nat). U64.v x - 8 <= a /\ a < F.fields_end g' x ==> not (G.uw st.pm a)) /\
  NO.new_only g g' x /\ Th.others_unchanged g g' /\ Th.unswept_unchanged g g' st st' /\
  I.fields_written_with (free_sw st.pm) g' g'' x

/// The writes keep the objects and the headers.
let after_objs (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x)
          (ensures F.fctx g' g'' x /\ same_objs g'' g' /\ Sc.objs g'' zs /\
                   (forall (z: obj_addr). L.mem z zs ==> read_word g'' (hd_address z) == read_word g (hd_address z)))
  = let one (y: obj_addr)
      : Lemma ((Seq.mem y (objects zero_addr g'') <==> Seq.mem y (objects zero_addr g')) /\
               (Seq.mem y (objects zero_addr g'') ==> read_word g'' (hd_address y) == read_word g' (hd_address y)))
      = F.obj_same g' g'' x y
    in
    FStar.Classical.forall_intro one;
    let z1 (z: obj_addr) : Lemma (L.mem z zs ==> ~(is_blue z g''))
      = if L.mem z zs then begin color_of_header_eq z g'' g'; color_of_header_eq z g' gk' end
    in
    FStar.Classical.forall_intro z1

/// The fields of `x` and of a dead object are apart.
let x_not_dead (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr) (a: nat)
  : Lemma (requires after g gk gk' g' g'' st st' zs x /\ U64.v x <= a /\ a < F.fields_end g'' x)
          (ensures ~(Sc.in_fields g'' zs a))
  = after_objs g gk gk' g' g'' st st' zs x;
    let none (z: obj_addr) : Lemma (~(L.mem z zs /\ U64.v z <= a /\ a < F.fields_end g'' z))
      = if L.mem z zs then begin
          color_of_header_eq z g gk;
          F.other_apart g'' z x
        end
    in
    FStar.Classical.forall_intro none

/// The surrogate of the caller's heap is a heap the surrogate's caller could
/// have written.
#push-options "--z3rlimit 40"
let after_written (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x)
          (ensures Th.fields_written gk' (Sc.scrub g'' zs) x)
  = let gk'' = Sc.scrub g'' zs in
    let pm = st.pm in
    after_objs g gk gk' g' g'' st st' zs x;
    Sc.scrub_facts g'' zs;
    Sc.scrub_facts g zs;
    pages_ok_sw_elim g st;
    wosize_of_object_spec x g';
    wosize_of_object_spec x gk';
    wosize_of_object_spec x g'';
    assert (read_word g'' (hd_address x) == read_word gk' (hd_address x));
    assert (F.fields_end g'' x == U64.v x + U64.v (wosize_of_object x gk') * 8);
    color_of_header_eq x g' gk';
    let outside (a: hp_addr)
      : Lemma (U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x gk') * 8 ==>
               read_word gk'' a == read_word gk' a)
      = if U64.v a < U64.v x || U64.v a >= U64.v x + U64.v (wosize_of_object x gk') * 8 then begin
          in_fields_same g'' gk' zs (U64.v a);
          in_fields_same g gk' zs (U64.v a);
          if FStar.IndefiniteDescription.strong_excluded_middle (Sc.in_fields g zs (U64.v a)) then begin
            dead_fields_uw g pm zs (U64.v a);
            reveal_opaque (`%G.uw) G.uw;
            page_of_spec (U64.v a);
            assert (Th.page_kept gk gk' (page_of (U64.v a)))
          end
        end
    in
    FStar.Classical.forall_intro outside;
    let inside (a: hp_addr)
      : Lemma (U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x gk') * 8 ==>
               Th.field_ok gk'' (read_word gk'' a))
      = if U64.v x <= U64.v a && U64.v a < U64.v x + U64.v (wosize_of_object x gk') * 8 then begin
          x_not_dead g gk gk' g' g'' st st' zs x (U64.v a);
          let v = read_word g'' a in
          assert (I.field_ok_with (free_sw pm) g'' v);
          if is_pointer v then begin
            let t : obj_addr = v in
            let r = resolve_object t g'' in
            if L.mem r zs then color_of_header_eq r g'' g
            else begin
              Sc.scrub_facts g'' zs;
              target_fill g'' zs (fun _ -> 0UL) t;
              color_of_header_eq r g'' gk''
            end
          end
        end
    in
    FStar.Classical.forall_intro inside
#pop-options

/// ---------------------------------------------------------------------------
/// The invariant after the writes
/// ---------------------------------------------------------------------------

let after_core (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x)
          (ensures Sc.core g'' st' /\ well_formed_heap (Sc.scrub g'' zs) /\ same_objs (Sc.scrub g'' zs) g'')
  = after_objs g gk gk' g' g'' st st' zs x;
    after_written g gk gk' g' g'' st st' zs x;
    let gk'' = Sc.scrub g'' zs in
    assert (pages_ok gk'' st' /\ well_formed_heap gk'');
    Sc.core_of_ok gk'' st';
    Sc.core_scrub g'' zs st';
    same_objs_fill g'' zs (fun _ -> 0UL)

/// The words the caller's writes keep.
let after_words (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr) (a: hp_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x /\
                    (U64.v a < U64.v x \/ U64.v a >= F.fields_end g' x))
          (ensures read_word g'' a == read_word g' a)
  = wosize_of_object_spec x g'

let after_grey (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x /\ map_ok st'.pm)
          (ensures no_grey_unswept g'' st'.pm)
  = pages_ok_sw_elim g st;
    let w (a: hp_addr) : Lemma (G.uw st'.pm (U64.v a) ==> read_word g'' a == read_word g a)
      = uw_same st.pm st'.pm (U64.v a);
        if G.uw st'.pm (U64.v a) then begin
          if U64.v x - 8 <= U64.v a && U64.v a < F.fields_end g' x then ()
          else after_words g gk gk' g' g'' st st' zs x a
        end
    in
    FStar.Classical.forall_intro w;
    no_grey_frame g g'' st.pm st'.pm

/// What counts as free while the new object is counted in use but its
/// fields are not yet bound: as mid-sweep, and the new object.
let free_x (pm: page_map) (x: obj_addr) : free_def = fun h y -> free_sw pm h y || y = x

let free_x_ok (pm: page_map) (x: obj_addr) : Lemma (free_def_ok (free_x pm x))
  = reveal_opaque (`%free_def_ok) free_def_ok;
    let det (g g': heap) (y: obj_addr)
      : Lemma ((is_block g y <==> is_block g' y) /\ read_word g (hd_address y) == read_word g' (hd_address y) ==>
               free_x pm x g y == free_x pm x g' y)
      = if read_word g (hd_address y) = read_word g' (hd_address y) then color_of_header_eq y g g'
    in
    FStar.Classical.forall_intro_3 det

/// **Only the new object comes into use**, through the writes.
let after_use (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr) (y: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x)
          (ensures in_use (free_x st'.pm x) g'' y == in_use (free_sw st.pm) g y /\
                   in_use (free_sw st'.pm) g'' y == (in_use (free_sw st.pm) g y || y = x))
  = after_objs g gk gk' g' g'' st st' zs x;
    uw_same st.pm st'.pm (U64.v y - 8);
    if y = x then begin
      color_of_header_eq x g'' g';
      is_white_iff x g'';
      is_blue_iff x g''
    end
    else begin
      if Seq.mem y (objects zero_addr g) && not (is_blue y g) then begin
        hd_address_spec y;
        R.hdr_obj g y;
        color_of_header_eq y g g'';
        assert (read_word g'' (hd_address y) == read_word g' (hd_address y))
      end;
      if Seq.mem y (objects zero_addr g'') && not (is_blue y g'') then begin
        color_of_header_eq y g'' g';
        assert (Seq.mem y (objects zero_addr g) /\ ~(is_blue y g));
        color_of_header_eq y g g''
      end
    end

let aligned_gt (p q: nat)
  : Lemma (requires p % 8 == 0 /\ q % 8 == 0 /\ p < q) (ensures p + 8 <= q)
  = FStar.Math.Lemmas.lemma_div_mod p 8;
    FStar.Math.Lemmas.lemma_div_mod q 8

/// Every block in use keeps its block.
let after_block (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr) (y: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x /\ in_use (free_sw st.pm) g y)
          (ensures SPI.same_block g g'' (hd_address y))
  = after_objs g gk gk' g' g'' st st' zs x;
    free_sw_ok st.pm;
    in_use_not_blue (free_sw st.pm) g y;
    hd_address_spec y;
    assert (Seq.mem y (objects zero_addr g') /\ read_word g' (hd_address y) == read_word g (hd_address y));
    assert (Seq.mem y (objects zero_addr g'') /\ read_word g'' (hd_address y) == read_word g (hd_address y));
    wosize_of_object_spec y g;
    wosize_of_object_spec y g'';
    wosize_of_object_spec x g';
    wosize_of_object_spec x g'';
    assert (y <> x);
    F.other_apart g'' x y;
    let wy = U64.v (wosize_of_object y g) in
    assert (GC.Spec.Walk.bnext g (hd_address y) == U64.v (hd_address y) + (wy + 1) * 8);
    FStar.Math.Lemmas.distributivity_add_left wy 1 8;
    assert (GC.Spec.Walk.bnext g (hd_address y) == U64.v y + wy * 8);
    let body (a: hp_addr)
      : Lemma (U64.v (hd_address y) < U64.v a /\ U64.v a < GC.Spec.Walk.bnext g (hd_address y) ==>
               read_word g'' a == read_word g a)
      = if U64.v (hd_address y) < U64.v a && U64.v a < GC.Spec.Walk.bnext g (hd_address y) then begin
          aligned_gt (U64.v (hd_address y)) (U64.v a);
          assert (U64.v y <= U64.v a /\ U64.v a < U64.v y + U64.v (wosize_of_object y g) * 8);
          after_words g gk gk' g' g'' st st' zs x a
        end
    in
    FStar.Classical.forall_intro body

let after_infix (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x)
          (ensures no_infix_block g'')
  = after_core g gk gk' g' g'' st st' zs x;
    let gk'' = Sc.scrub g'' zs in
    wf_parts ();
    let one (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr g'') ==> ~(is_infix y g''))
      = if Seq.mem y (objects zero_addr g'') then resolve_object_locality y g'' gk''
    in
    FStar.Classical.forall_intro one

/// A field of the new object holds a value that is not free mid-sweep.
let x_field (g' g'': heap) (pm pm': page_map) (x: obj_addr) (j: nat)
  : Lemma (requires I.fields_written_with (free_sw pm) g' g'' x /\ same_swept pm pm' /\
                    read_word g'' (hd_address x) == read_word g' (hd_address x) /\
                    j < U64.v (wosize_of_object x g'') /\ U64.v x + j * 8 + 8 <= heap_size)
          (ensures (let w = read_word g'' (U64.uint_to_t (U64.v x + j * 8)) in
                    is_pointer w ==>
                    in_use (free_sw pm') g'' (resolve_object (w <: obj_addr) g'') /\
                    infix_addr_wf g'' (objects zero_addr g'') (w <: obj_addr)))
  = let a = R.field_addr x j in
    assert (U64.uint_to_t (U64.v x + j * 8) == a);
    wosize_of_object_spec x g';
    wosize_of_object_spec x g'';
    assert (I.field_ok_with (free_sw pm) g'' (read_word g'' a));
    let w = read_word g'' a in
    if is_pointer w then uw_same pm pm' (U64.v (resolve_object (w <: obj_addr) g'') - 8)

/// A field of another block in use: from well-formedness with the new
/// object counted free.
let other_field (g'': heap) (pm': page_map) (x src: obj_addr) (j: nat)
  : Lemma (requires well_formed_heap_with (free_x pm' x) g'' /\ in_use (free_sw pm') g'' src /\ src <> x /\
                    ~(is_no_scan src g'') /\
                    j < U64.v (wosize_of_object src g'') /\ U64.v src + j * 8 + 8 <= heap_size)
          (ensures (let w = read_word g'' (U64.uint_to_t (U64.v src + j * 8)) in
                    is_pointer w ==>
                    in_use (free_sw pm') g'' (resolve_object (w <: obj_addr) g'') /\
                    infix_addr_wf g'' (objects zero_addr g'') (w <: obj_addr)))
  = free_x_ok pm' x;
    let w = read_word g'' (U64.uint_to_t (U64.v src + j * 8)) in
    if is_pointer w then FT.wf_with_field (free_x pm' x) g'' src j

/// From the new object counted free to the new object in use: its fields
/// hold values that are not free.
let wf_close (g' g'': heap) (pm pm': page_map) (x: obj_addr)
  : Lemma (requires I.fields_written_with (free_sw pm) g' g'' x /\ same_swept pm pm' /\
                    read_word g'' (hd_address x) == read_word g' (hd_address x) /\
                    well_formed_heap_with (free_x pm' x) g'')
          (ensures well_formed_heap_with (free_sw pm') g'')
  = wf_with_parts ();
    free_sw_ok pm';
    free_def_ok_elim (free_sw pm');
    let closure (src: obj_addr) (j: nat)
      : Lemma (requires in_use (free_sw pm') g'' src /\ ~(is_no_scan src g'') /\
                        j < U64.v (wosize_of_object src g'') /\ U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let w = read_word g'' (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer w ==>
                        in_use (free_sw pm') g'' (resolve_object (w <: obj_addr) g'') /\
                        infix_addr_wf g'' (objects zero_addr g'') (w <: obj_addr)))
      = if src = x then x_field g' g'' pm pm' x j
        else other_field g'' pm' x src j
    in
    pointer_clauses_from_field_closure (free_sw pm') g'' closure

/// **Well formed mid-sweep, after the writes.**
let after_wf (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x)
          (ensures well_formed_heap_with (free_sw st'.pm) g'')
  = let pm = st.pm in
    let pm' = st'.pm in
    pages_ok_sw_elim g st;
    after_infix g gk gk' g' g'' st st' zs x;
    after_objs g gk gk' g' g'' st st' zs x;
    free_sw_ok pm;
    free_x_ok pm' x;
    FStar.Classical.forall_intro (after_use g gk gk' g' g'' st st' zs x);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (after_block g gk gk' g' g'' st st' zs x));
    SPI.wf_transport g g'' (free_sw pm) (free_x pm' x);
    wf_close g' g'' pm pm' x

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

let after_ok (g gk gk' g' g'': heap) (st st': pstate) (zs: list obj_addr) (x: obj_addr)
  : Lemma (requires after g gk gk' g' g'' st st' zs x)
          (ensures pages_ok_sw g'' st' /\ GC.Spec.Pages.WalkEnd.walk_end g'' zero_addr + 8 >= heap_size)
  = after_core g gk gk' g' g'' st st' zs x;
    Sc.core_shape g'' st';
    after_grey g gk gk' g' g'' st st' zs x;
    after_wf g gk gk' g' g'' st st' zs x;
    pages_ok_sw_intro g'' st';
    heap_tiled g'' st'.pm

/// The blocks in use after an allocation, in any heap with its objects and
/// headers.
let use_eq (g g' h: heap) (pm pm': page_map) (x: obj_addr) (y: obj_addr)
  : Lemma (requires same_objs h g' /\ NO.new_only g g' x /\ Th.others_unchanged g g' /\ same_swept pm pm' /\
                    Seq.mem x (objects zero_addr g') /\ is_white x g' /\ not (unswept_at pm x) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))
          (ensures in_use (free_sw pm') h y == (in_use (free_sw pm) g y || y = x))
  = uw_same pm pm' (U64.v y - 8);
    if y = x then begin
      color_of_header_eq x h g';
      is_white_iff x h;
      is_blue_iff x h
    end
    else begin
      if Seq.mem y (objects zero_addr g) && not (is_blue y g) then begin
        hd_address_spec y;
        color_of_header_eq y g h
      end;
      if Seq.mem y (objects zero_addr h) && not (is_blue y h) then begin
        color_of_header_eq y h g';
        color_of_header_eq y g h
      end
    end

/// The `Sweeping` allocator is the white one: the new header is white
/// already.
let sweeping_alloc (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires (let (g', _, o) = A.alloc g st wz in
                     o =!= 0UL ==> U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                                   is_white (o <: obj_addr) g'))
          (ensures GC.Spec.Pages.Allocator.alloc I.Sweeping g st wz == A.alloc g st wz)
  = let (g', st', o) = A.alloc g st wz in
    if o <> 0UL then begin
      let x : obj_addr = o in
      GC.Spec.Pages.Recolour.hx_word x;
      R.hdr_obj g' x;
      is_white_iff x g';
      GC.Spec.Pages.Recolour.colorHeader_same (hdr g' (U64.v x - 8)) White;
      let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                                read_word (GC.Spec.Pages.AllocPhase.recolour g' o White) (U64.uint_to_t b) ==
                                read_word g' (U64.uint_to_t b))
        = if b < heap_size && b % 8 = 0 then
            GC.Spec.Pages.Blocks.wr_read g' (U64.v x - 8) (hdr g' (U64.v x - 8)) (U64.uint_to_t b)
      in
      FStar.Classical.forall_intro aux;
      GC.Gen.HeapExtensional.heap_read_word_ext (GC.Spec.Pages.AllocPhase.recolour g' o White) g'
    end

/// **Allocation during an incremental sweep.**  From the mid-sweep
/// invariant, the `Sweeping` allocator:
///   - on failure changes nothing;
///   - on success returns an object of the heap, of wosize `wz`, white
///     (`colour_at`: its header lies in a swept page), that was not in use;
///   - brings no other block into use (plan §20.1, fact 2);
///   - keeps every block that is not free, with its header and fields
///     (fact 3), and every unswept page and its entry, and every swept bit;
///   - leaves to the caller a heap that, once the new object's fields hold
///     values that are not free mid-sweep, satisfies the mid-sweep
///     invariant (fact 5), and whose walk reaches the end of the heap
///     (fact 4).
/// The context of a successful allocation, for the caller's heap `g''`.
#push-options "--z3rlimit 40"
let after_intro (g: heap) (st: pstate) (wz: nat) (g'': heap)
  : Lemma (requires pages_ok_sw g st /\
                    (let (g', _, o) = A.alloc g st wz in
                     o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                     I.fields_written_with (free_sw st.pm) g' g'' (o <: obj_addr)))
          (ensures (let zs = dead_list g st.pm in
                    let gk = Sc.scrub g zs in
                    let (gk', st', o) = A.alloc gk st wz in
                    let (g', _, _) = A.alloc g st wz in
                    U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    after g gk gk' g' g'' st st' zs (o <: obj_addr)))
  = let zs = dead_list g st.pm in
    let gk = Sc.scrub g zs in
    alloc_relate g st zs wz;
    alloc_facts g st zs wz;
    let (gk', st', o) = A.alloc gk st wz in
    let (g', _, _) = A.alloc g st wz in
    let x : obj_addr = o in
    same_objs_fill gk' zs (reader g');
    color_of_header_eq x g' gk';
    wosize_of_object_spec x g';
    wosize_of_object_spec x gk'
#pop-options

/// The caller's heap is in the mid-sweep invariant.
#push-options "--z3rlimit 40"
let alloc_sw_fill (g: heap) (st: pstate) (wz: nat) (g'': heap)
  : Lemma (requires pages_ok_sw g st /\
                    (let (g', _, o) = A.alloc g st wz in
                     o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                     I.fields_written_with (free_sw st.pm) g' g'' (o <: obj_addr)))
          (ensures (let (_, st', _) = A.alloc g st wz in
                    pages_ok_sw g'' st' /\ GC.Spec.Pages.WalkEnd.walk_end g'' zero_addr + 8 >= heap_size))
  = let zs = dead_list g st.pm in
    let gk = Sc.scrub g zs in
    after_intro g st wz g'';
    alloc_relate g st zs wz;
    let (gk', st', o) = A.alloc gk st wz in
    let (g', _, _) = A.alloc g st wz in
    after_ok g gk gk' g' g'' st st' zs (o <: obj_addr)
#pop-options

/// The basic facts of an allocation from the mid-sweep invariant.
#push-options "--z3rlimit 40"
let alloc_sw_basic (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok_sw g st)
          (ensures (let (g', st', o) = A.alloc g st wz in
                    same_swept st.pm st'.pm /\
                    (o == 0UL ==> g' == g /\ st' == st /\ (wz + 1 < pow2 54 ==> Th.no_fit g st (wz + 1))) /\
                    (o =!= 0UL ==>
                       U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                       (let x : obj_addr = o in
                        Seq.mem x (objects zero_addr g') /\ U64.v (wosize_of_object x g') == wz /\
                        is_white x g' /\ not (unswept_at st.pm x) /\
                        ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                        NO.new_only g g' o)) /\
                    Th.others_unchanged g g' /\ Th.unswept_unchanged g g' st st'))
  = let zs = dead_list g st.pm in
    let gk = Sc.scrub g zs in
    alloc_relate g st zs wz;
    alloc_facts g st zs wz;
    let (gk', st', o) = A.alloc gk st wz in
    if o = 0UL then begin
      let lst (y: obj_addr)
        : Lemma (Seq.mem y (objects zero_addr gk) ==> is_blue y gk == is_blue y g /\ whsize gk y == whsize g y)
        = if Seq.mem y (objects zero_addr gk) then begin
            color_of_header_eq y gk g;
            wosize_of_object_spec y gk;
            wosize_of_object_spec y g
          end
      in
      FStar.Classical.forall_intro lst
    end
#pop-options

/// **Allocation during an incremental sweep.**  From the mid-sweep
/// invariant, the `Sweeping` allocator:
///   - on failure changes nothing, and there was no room (`no_fit`);
///   - on success returns an object of the heap, of wosize `wz`, white
///     (`colour_at`: its header lies in a swept page), that was not in use;
///   - brings no other block into use (plan §20.1, fact 2);
///   - keeps every block that is not free, with its header and fields
///     (fact 3), and every unswept page and its entry, and every swept bit;
///   - leaves to the caller a heap that, once the new object's fields hold
///     values that are not free mid-sweep, satisfies the mid-sweep
///     invariant (fact 5), and whose walk reaches the end of the heap
///     (fact 4).
let alloc_sw_ok (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok_sw g st)
          (ensures (let (g', st', o) = GC.Spec.Pages.Allocator.alloc I.Sweeping g st wz in
                    same_swept st.pm st'.pm /\
                    (o == 0UL ==> g' == g /\ st' == st /\ (wz + 1 < pow2 54 ==> Th.no_fit g st (wz + 1))) /\
                    (o =!= 0UL ==>
                       U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                       (let x : obj_addr = o in
                        Seq.mem x (objects zero_addr g') /\ U64.v (wosize_of_object x g') == wz /\
                        is_white x g' /\ not (unswept_at st.pm x) /\
                        ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                        (forall (y: obj_addr). in_use (free_sw st'.pm) g' y == (in_use (free_sw st.pm) g y || y = x)) /\
                        (forall (g'': heap). I.fields_written_with (free_sw st.pm) g' g'' x ==>
                           pages_ok_sw g'' st' /\ GC.Spec.Pages.WalkEnd.walk_end g'' zero_addr + 8 >= heap_size))) /\
                    Th.others_unchanged g g' /\ Th.unswept_unchanged g g' st st'))
  = alloc_sw_basic g st wz;
    let (g', st', o) = A.alloc g st wz in
    sweeping_alloc g st wz;
    if o <> 0UL then begin
      let x : obj_addr = o in
      FStar.Classical.forall_intro (use_eq g g' g' st.pm st'.pm x);
      let fill (g'': heap)
        : Lemma (I.fields_written_with (free_sw st.pm) g' g'' x ==>
                 pages_ok_sw g'' st' /\ GC.Spec.Pages.WalkEnd.walk_end g'' zero_addr + 8 >= heap_size)
        = if FStar.IndefiniteDescription.strong_excluded_middle (I.fields_written_with (free_sw st.pm) g' g'' x)
          then alloc_sw_fill g st wz g''
      in
      FStar.Classical.forall_intro fill
    end

/// ---------------------------------------------------------------------------
/// The page allocator, with the mid-sweep invariant, through the interface
/// ---------------------------------------------------------------------------

module PA = GC.Spec.Pages.Allocator

/// As `PA.inv`, but while sweeping the mid-sweep invariant.
let inv_sw (ph: I.phase) (g: heap) (st: pstate) : prop =
  match ph with
  | I.Sweeping -> pages_ok_sw g st
  | _ -> PA.inv ph g st

/// What the collector counts as free, by phase.
let free_ph (ph: I.phase) (st: pstate) : free_def =
  match ph with
  | I.Sweeping -> free_sw st.pm
  | _ -> free_stw

let pages_allocator_sw : I.allocator = {
  I.ast = pstate;
  I.inv = inv_sw;
  I.alloc = PA.alloc;
  I.unswept = PA.unswept;
  I.pending = PA.unswept;
}

let sweeping_post (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok_sw g st)
          (ensures (let (g', st', o) = PA.alloc I.Sweeping g st wz in
                    I.alloc_post_with (free_sw st.pm) pages_allocator_sw I.Sweeping g st wz g' st' o))
  = alloc_sw_ok g st wz;
    let (g', st', o) = PA.alloc I.Sweeping g st wz in
    let pend (b: hp_addr) : Lemma (PA.unswept st b ==> read_word g' b == read_word g b)
      = if FStar.IndefiniteDescription.strong_excluded_middle (PA.unswept st b) then
          eliminate exists (i: nat{i < n_pages}).
            not (entry st.pm i).swept /\ page_base i <= U64.v b /\ U64.v b < page_base (i + 1)
          with assert (Th.page_kept g g' i)
    in
    FStar.Classical.forall_intro pend;
    if o <> 0UL then begin
      let x : obj_addr = o in
      hd_address_spec x;
      unswept_uw st (hd_address x);
      is_white_iff x g';
      assert (I.colour_at pages_allocator_sw st I.Sweeping x == White)
    end

let ok_elim (a: I.allocator) (ph: I.phase) (g: heap) (s: a.I.ast) (wz: nat)
  : Lemma (requires I.allocator_ok a /\ a.I.inv ph g s)
          (ensures (let (g', s', obj) = a.I.alloc ph g s wz in I.alloc_post a ph g s wz g' s' obj))
  = ()

let other_post (ph: I.phase) (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires ph =!= I.Sweeping /\ PA.inv ph g st)
          (ensures (let (g', st', o) = PA.alloc ph g st wz in
                    I.alloc_post_with free_stw pages_allocator_sw ph g st wz g' st' o))
  = PA.pages_allocator_ok ();
    ok_elim PA.pages_allocator ph g st wz;
    match ph with
    | I.Idle -> ()
    | I.Marking -> ()

/// **The page allocator meets the interface with the mid-sweep invariant**,
/// with free meaning `free_sw` while sweeping, and its invariant follows
/// the collector's phase.
let pages_allocator_sw_ok ()
  : Lemma (I.allocator_ok_with pages_allocator_sw free_ph /\ I.phase_ok pages_allocator_sw)
  = let ok (ph: I.phase) (g: heap) (s: pstate) (wz: nat)
      : Lemma (inv_sw ph g s ==>
               (let (g', s', obj) = PA.alloc ph g s wz in
                I.alloc_post_with (free_ph ph s) pages_allocator_sw ph g s wz g' s' obj))
      = if FStar.IndefiniteDescription.strong_excluded_middle (inv_sw ph g s) then
          match ph with
          | I.Sweeping -> sweeping_post g s wz
          | _ -> other_post ph g s wz
    in
    FStar.Classical.forall_intro_4 ok;
    assert (I.allocator_ok_with pages_allocator_sw free_ph);
    PA.pages_allocator_ok ();
    let enter (g: heap) (s: pstate)
      : Lemma (pages_allocator_sw.I.inv I.Idle g s ==> pages_allocator_sw.I.inv I.Marking g s)
      = assert (PA.pages_allocator.I.inv I.Idle g s ==> PA.pages_allocator.I.inv I.Marking g s)
    in
    FStar.Classical.forall_intro_2 enter;
    let mark (g: heap) (s: pstate) (x: obj_addr) (c: color)
      : Lemma (pages_allocator_sw.I.inv I.Marking g s /\ I.live g x /\ c <> Blue ==>
               pages_allocator_sw.I.inv I.Marking (set_object_color x g c) s)
      = assert (PA.pages_allocator.I.inv I.Marking g s /\ I.live g x /\ c <> Blue ==>
                PA.pages_allocator.I.inv I.Marking (set_object_color x g c) s)
    in
    FStar.Classical.forall_intro_4 mark
