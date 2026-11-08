/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Replace - rewriting a stretch of free blocks
/// ---------------------------------------------------------------------------
///
/// Every step of the page allocator rewrites one stretch `[a, e)` of the heap
/// that the walk covers with free (blue) blocks only: a free slot, a free
/// large block, a run of free pages.  It lays new blocks over the stretch,
/// which the walk again covers exactly, and leaves every other word alone.
/// `replaces g g' a e` states that, together with two facts about the new
/// blocks: none is infix, and a block that is not blue has no pointer field.
///
/// `replace_ok` derives everything the heap-level part of `alloc_ok` needs
/// from it, once:
///   - the walk, and so `objects`, is unchanged outside the stretch;
///   - inside it, the objects are exactly the new blocks;
///   - `well_formed_heap` and `no_pointer_to_blue` are kept;
///   - every object that was not free keeps its place, header and fields.
///
/// The argument rests on the walk being deterministic (`steps_to_det`): two
/// positions the walk reaches are reached one from the other, so an object
/// outside the stretch has its whole block outside it.

module GC.Spec.Pages.Replace

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape

module U64 = FStar.UInt64
module Seq = FStar.Seq
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let z : nat = U64.v zero_addr

/// ---------------------------------------------------------------------------
/// The walk is deterministic
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1"
let rec steps_to_det (g: heap) (s a b: nat)
  : Lemma (requires steps_to g s a /\ steps_to g s b /\ a <= b)
          (ensures steps_to g a b)
          (decreases (if s <= a then a - s else 0))
  = steps_to_le g s a;
    if s = a then ()
    else begin
      steps_to_le g s b;
      let sa = mk_hp_addr s in
      steps_to_next g sa a;
      steps_to_next g sa b;
      steps_to_det g (s + block_bytes g sa) a b
    end
#pop-options

let block_bytes_words (g: heap) (b: nat)
  : Lemma (requires b % 8 == 0 /\ b < heap_size)
          (ensures block_bytes g (mk_hp_addr b) == words_at g b * 8)
  = ()

/// A position the walk reaches before another one: its whole block lies
/// before it, and the walk goes on from the block's end.
let block_before (g: heap) (s b x: nat)
  : Lemma (requires steps_to g s b /\ steps_to g s x /\ b < x)
          (ensures b % 8 == 0 /\ b < heap_size /\
                   b + words_at g b * 8 <= x /\
                   steps_to g (b + words_at g b * 8) x)
  = steps_to_det g s b x;
    steps_to_le g b x;
    steps_to_next g (mk_hp_addr b) x;
    block_bytes_words g b

/// The header of an object, as `hdr` reads it.
let hdr_obj (g: heap) (x: obj_addr)
  : Lemma (U64.v x - 8 >= 0 /\ hdr g (U64.v x - 8) == read_word g (hd_address x) /\
           words_at g (U64.v x - 8) == U64.v (wosize_of_object x g) + 1 /\
           color_at g (U64.v x - 8) == color_of_object x g /\
           getTag (hdr g (U64.v x - 8)) == tag_of_object x g)
  = hd_address_spec x;
    assert (mk_hp_addr (U64.v x - 8) == hd_address x);
    wosize_of_object_spec x g;
    color_of_object_spec x g;
    tag_of_object_spec x g

/// An object is a position the walk reaches whose block fits in the heap.
let obj_iff (g: heap) (x: obj_addr)
  : Lemma (Seq.mem x (objects zero_addr g) <==>
           (let h = U64.v x - 8 in
            steps_to g z h /\ h + 8 < heap_size /\ h + words_at g h * 8 <= heap_size))
  = hd_address_spec x;
    hdr_obj g x;
    let h = U64.v x - 8 in
    if Seq.mem x (objects zero_addr g) then begin
      objects_steps_to g zero_addr x;
      objects_member_size_bound zero_addr g x
    end;
    if steps_to g z h && h + 8 < heap_size && h + words_at g h * 8 <= heap_size then begin
      block_bytes_words g h;
      steps_to_objects g zero_addr (hd_address x) (h + words_at g h * 8);
      f_hd_roundtrip x
    end

/// ---------------------------------------------------------------------------
/// Replacing a stretch
/// ---------------------------------------------------------------------------

/// A new block: not infix, and if it is not free, no field is a pointer.
let new_block_ok (g': heap) (b: nat) : prop =
  getTag (hdr g' b) <> infix_tag /\
  (color_at g' b =!= Blue ==>
     (forall (x: hp_addr). b < U64.v x /\ U64.v x < b + words_at g' b * 8 ==>
        not (is_pointer (read_word g' x))))

let replaces (g g': heap) (a e: nat) : prop =
  a < e /\ e <= heap_size /\
  steps_to g z a /\ steps_to g a e /\ steps_to g' a e /\
  (forall (x: hp_addr). U64.v x < a \/ U64.v x >= e ==> read_word g' x == read_word g x) /\
  (forall (b: nat). steps_to g a b /\ b < e ==> color_at g b == Blue) /\
  (forall (b: nat). steps_to g' a b /\ b < e ==> new_block_ok g' b)

let replaces_frame_prefix (g g': heap) (a e: nat)
  : Lemma (requires replaces g g' a e) (ensures steps_to g' z a)
  = steps_to_frame g g' z a

/// Outside the stretch, both walks reach the same positions.
let replace_walk (g g': heap) (a e: nat) (b: nat)
  : Lemma (requires replaces g g' a e /\ (b <= a \/ b >= e))
          (ensures steps_to g z b <==> steps_to g' z b)
  = replaces_frame_prefix g g' a e;
    if b <= a then steps_to_frame g g' z b
    else begin
      steps_to_frame g g' e b;
      if steps_to g z b then begin
        steps_to_trans g z a e;
        steps_to_det g z e b;
        steps_to_trans g' a e b;
        steps_to_trans g' z a b
      end;
      if steps_to g' z b then begin
        steps_to_trans g' z a e;
        steps_to_det g' z e b;
        steps_to_trans g a e b;
        steps_to_trans g z a b
      end
    end

/// Inside the stretch, the positions reached are those reached from `a`.
let inside_walk (g: heap) (a e b: nat)
  : Lemma (requires steps_to g z a /\ a <= b)
          (ensures steps_to g z b <==> steps_to g a b)
  = if steps_to g z b then steps_to_det g z a b;
    if steps_to g a b then steps_to_trans g z a b

/// An object outside the stretch is an object of both heaps or of neither,
/// with the same block.
let replace_obj_out (g g': heap) (a e: nat) (x: obj_addr)
  : Lemma (requires replaces g g' a e /\ (U64.v x - 8 < a \/ U64.v x - 8 >= e))
          (ensures (Seq.mem x (objects zero_addr g) <==> Seq.mem x (objects zero_addr g')) /\
                   (Seq.mem x (objects zero_addr g) ==>
                      (forall (y: hp_addr). U64.v x - 8 <= U64.v y /\
                         U64.v y < U64.v x - 8 + words_at g (U64.v x - 8) * 8 ==>
                         read_word g' y == read_word g y)))
  = let h = U64.v x - 8 in
    hd_address_spec x;
    replace_walk g g' a e h;
    obj_iff g x;
    obj_iff g' x;
    if h < a && steps_to g z h then block_before g z h a;
    if h < heap_size then assert (hdr g' h == hdr g h)

/// An object inside the stretch is a block the walk from `a` reaches.
let replace_obj_in (g: heap) (a e: nat) (x: obj_addr)
  : Lemma (requires steps_to g z a /\ steps_to g a e /\ e <= heap_size /\
                    a <= U64.v x - 8 /\ U64.v x - 8 < e)
          (ensures Seq.mem x (objects zero_addr g) <==>
                   (steps_to g a (U64.v x - 8) /\ U64.v x < heap_size))
  = let h = U64.v x - 8 in
    hd_address_spec x;
    obj_iff g x;
    inside_walk g a e h;
    if steps_to g a h then block_before g a h e

/// ---------------------------------------------------------------------------
/// What is kept
/// ---------------------------------------------------------------------------

/// The stretch held free blocks only, so an object that was not free lies
/// outside it.
let not_blue_outside (g g': heap) (a e: nat) (x: obj_addr)
  : Lemma (requires replaces g g' a e /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures U64.v x - 8 < a \/ U64.v x - 8 >= e)
  = let h = U64.v x - 8 in
    if a <= h && h < e then begin
      replace_obj_in g a e x;
      hdr_obj g x;
      is_blue_iff x g
    end

let kept (g g': heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem x (objects zero_addr g') /\
                    (forall (y: hp_addr). U64.v x - 8 <= U64.v y /\
                       U64.v y < U64.v x - 8 + words_at g (U64.v x - 8) * 8 ==>
                       read_word g' y == read_word g y))
          (ensures read_word g' (hd_address x) == read_word g (hd_address x) /\
                   (forall (b: hp_addr). U64.v x <= U64.v b /\
                      U64.v b < U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                      read_word g' b == read_word g b))
  = hdr_obj g x;
    hd_address_spec x

/// Every object that was not free keeps its place, header and fields.
let replace_others (g g': heap) (a e: nat) (x: obj_addr)
  : Lemma (requires replaces g g' a e /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures Seq.mem x (objects zero_addr g') /\
                   read_word g' (hd_address x) == read_word g (hd_address x) /\
                   (forall (b: hp_addr). U64.v x <= U64.v b /\
                      U64.v b < U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                      read_word g' b == read_word g b))
  = not_blue_outside g g' a e x;
    replace_obj_out g g' a e x;
    kept g g' x

/// ---------------------------------------------------------------------------
/// Well-formedness
/// ---------------------------------------------------------------------------

let replace_part4 (g g': heap) (a e: nat)
  : Lemma (requires replaces g g' a e /\ well_formed_heap_part4 g)
          (ensures well_formed_heap_part4 g')
  = let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g'))
              (ensures ~(is_infix x g'))
      = let h = U64.v x - 8 in
        hd_address_spec x;
        is_infix_spec x g';
        hdr_obj g' x;
        if a <= h && h < e then begin
          replaces_frame_prefix g g' a e;
          replace_obj_in g' a e x
        end else begin
          replace_obj_out g g' a e x;
          hdr_obj g x;
          resolve_object_locality x g g'
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// The field `j` of `src` holds `v`.
let field_at (g: heap) (src: obj_addr) (j: nat) : prop =
  j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size

let field_addr (src: obj_addr) (j: nat{U64.v src + j * 8 + 8 <= heap_size}) : hp_addr =
  aligned_plus_mul8 (U64.v src) j;
  mk_hp_addr (U64.v src + j * 8)

/// A pointer field of an object of a well-formed heap with no pointer to a
/// free block: its target resolves to an object that is not free.
let old_target (g: heap) (src: obj_addr) (j: nat) (v: obj_addr)
  : Lemma (requires well_formed_heap g /\ Mark.no_pointer_to_blue g /\
                    Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                    field_at g src j /\ read_word g (field_addr src j) == (v <: U64.t) /\
                    is_pointer (v <: U64.t))
          (ensures Seq.mem (resolve_object v g) (objects zero_addr g) /\
                   infix_addr_wf g (objects zero_addr g) v /\
                   ~(is_blue (resolve_object v g) g))
  = wosize_of_object_bound src g;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    FStar.Math.Lemmas.pow2_lt_compat 64 61;
    let k = U64.uint_to_t j in
    assert (U64.v (U64.add_mod src (U64.mul_mod k mword)) == U64.v src + j * 8);
    assert (U64.add_mod src (U64.mul_mod k mword) == field_addr src j);
    hd_address_spec src;
    hd_address_spec v;
    assert (is_pointer_to (read_word g (field_addr src j)) v);
    wf_object_size_bound g src;
    wosize_of_object_bound src g;
    field_read_implies_exists_pointing g src (wosize_of_object src g) k v;
    wf_field_target_in_objects g src v;
    wf_field_target_infix_wf g src v;
    is_blue_iff src g;
    assert (points_to g src v)

/// Resolving a target in the new heap: it lands on the same object, which is
/// still there and still not free.
let new_target (g g': heap) (a e: nat) (v: obj_addr)
  : Lemma (requires replaces g g' a e /\
                    Seq.mem (resolve_object v g) (objects zero_addr g) /\
                    infix_addr_wf g (objects zero_addr g) v /\
                    ~(is_blue (resolve_object v g) g))
          (ensures Seq.mem (resolve_object v g') (objects zero_addr g') /\
                   infix_addr_wf g' (objects zero_addr g') v /\
                   ~(is_blue (resolve_object v g') g'))
  = let r = resolve_object v g in
    replace_others g g' a e r;
    color_of_header_eq r g g';
    hd_address_spec v;
    hd_address_spec r;
    hdr_obj g r;
    if is_infix v g then begin
      infix_addr_wf_elim g (objects zero_addr g) v;
      let w = U64.v (wosize_of_object v g) in
      let p = U64.v v - w * 8 in
      parent_closure_addr_nat_spec v g;
      resolve_infix_spec v g;
      assert (U64.v r == p);
      (* the infix header is a field word of its closure *)
      let hv = hd_address v in
      assert (U64.v r <= U64.v hv /\ U64.v hv < U64.v r + U64.v (wosize_of_object r g) * 8);
      assert (read_word g' hv == read_word g hv);
      resolve_object_locality v g g';
      resolve_object_locality r g g';
      infix_addr_wf_transfer g g' (objects zero_addr g) (objects zero_addr g') v
    end else begin
      resolve_non_infix v g;
      assert (r == v);
      resolve_object_locality v g g';
      resolve_non_infix v g';
      infix_addr_wf_non_infix g' (objects zero_addr g') v
    end

/// A pointer field of an object of the new heap.
let new_field (g g': heap) (a e: nat) (src: obj_addr) (j: nat) (v: obj_addr)
  : Lemma (requires replaces g g' a e /\ well_formed_heap g /\ Mark.no_pointer_to_blue g /\
                    Seq.mem src (objects zero_addr g') /\ fields_constrained g' src /\
                    field_at g' src j /\ read_word g' (field_addr src j) == (v <: U64.t) /\
                    is_pointer (v <: U64.t))
          (ensures Seq.mem (resolve_object v g') (objects zero_addr g') /\
                   infix_addr_wf g' (objects zero_addr g') v /\
                   ~(is_blue (resolve_object v g') g'))
  = let h = U64.v src - 8 in
    hd_address_spec src;
    hdr_obj g' src;
    is_blue_iff src g';
    if a <= h && h < e then begin
      (* a new block that is not free has no pointer field *)
      replaces_frame_prefix g g' a e;
      replace_obj_in g' a e src;
      assert (new_block_ok g' h);
      assert (h < U64.v (field_addr src j));
      assert (is_pointer (read_word g' (field_addr src j)))
    end else begin
      replace_obj_out g g' a e src;
      hdr_obj g src;
      kept g g' src;
      color_of_header_eq src g g';
      is_no_scan_spec src g;
      is_no_scan_spec src g';
      tag_of_object_spec src g;
      tag_of_object_spec src g';
      wosize_of_object_spec src g;
      wosize_of_object_spec src g';
      assert (read_word g (field_addr src j) == read_word g' (field_addr src j));
      old_target g src j v;
      new_target g g' a e v
    end

/// Part 1 holds of every heap: `objects` only lists blocks that fit.
let part1_always (g: heap)
  : Lemma (well_formed_heap_part1 g)
  = let aux (h: obj_addr)
      : Lemma (Seq.mem h (objects zero_addr g) ==>
               U64.v (hd_address h) + 8 + U64.v (wosize_of_object h g) * 8 <= Seq.length g)
      = if Seq.mem h (objects zero_addr g) then begin
          objects_member_size_bound zero_addr g h;
          wosize_of_object_spec h g
        end
    in
    FStar.Classical.forall_intro aux

let replace_part2_3 (g g': heap) (a e: nat)
  : Lemma (requires replaces g g' a e /\ well_formed_heap g /\ Mark.no_pointer_to_blue g /\
                    well_formed_heap_part4 g')
          (ensures well_formed_heap_part2 g' /\ well_formed_heap_part3 g')
  = let closure (src: obj_addr) (j: nat)
      : Lemma (requires Seq.mem src (objects zero_addr g') /\ fields_constrained g' src /\
                        j < U64.v (wosize_of_object src g') /\
                        U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let v = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer v ==>
                        Seq.mem (resolve_object (v <: obj_addr) g') (objects zero_addr g') /\
                        infix_addr_wf g' (objects zero_addr g') (v <: obj_addr)))
      = let v = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
        assert (U64.uint_to_t (U64.v src + j * 8) == field_addr src j);
        if is_pointer v then new_field g g' a e src j v
    in
    part1_always g';
    well_formed_heap_part2_3_from_resolved_field_closure g' closure

let replace_no_blue (g g': heap) (a e: nat)
  : Lemma (requires replaces g g' a e /\ well_formed_heap g /\ Mark.no_pointer_to_blue g)
          (ensures Mark.no_pointer_to_blue g')
  = let field (src: obj_addr) (dst: obj_addr) (j: nat)
      : Lemma (requires Seq.mem src (objects zero_addr g') /\
                        ~(is_blue src g') /\
                        fields_constrained g' src /\
                        j < U64.v (wosize_of_object src g') /\
                        U64.v src + j * 8 + 8 <= heap_size /\
                        is_pointer_to (read_word g' (U64.uint_to_t (U64.v src + j * 8))) dst)
              (ensures ~(is_blue (resolve_object dst g') g'))
      = let v = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
        assert (U64.uint_to_t (U64.v src + j * 8) == field_addr src j);
        hd_address_spec dst;
        hd_address_spec v;
        assert (v == (dst <: U64.t));
        new_field g g' a e src j dst
    in
    part1_always g';
    Mark.no_pointer_to_blue_intro_from_fields g' field

/// **The heap-level facts of a replacement.**
let replace_ok (g g': heap) (a e: nat)
  : Lemma (requires replaces g g' a e /\ well_formed_heap g /\ Mark.no_pointer_to_blue g)
          (ensures well_formed_heap g' /\ Mark.no_pointer_to_blue g' /\
                   (forall (x: obj_addr).
                      Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
                      Seq.mem x (objects zero_addr g') /\
                      read_word g' (hd_address x) == read_word g (hd_address x) /\
                      (forall (b: hp_addr). U64.v x <= U64.v b /\
                         U64.v b < U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                         read_word g' b == read_word g b)))
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    part1_always g';
    replace_part4 g g' a e;
    replace_part2_3 g g' a e;
    replace_no_blue g g' a e;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (replace_others g g' a e))
