/// ---------------------------------------------------------------------------
/// GC.Gen.AllocLists - what allocation from the free lists preserves
/// ---------------------------------------------------------------------------
///
/// The allocator over the size-class free lists, `alloc_lists_spec`
/// (`GC.Spec.Allocator.Lists`), with the same lemma kit the single-list
/// allocator has (`GC.Spec.Allocator.Lemmas`, `GC.Gen.AllocProps`), stated
/// over the whole state: `fl_valid` and `fl_chain_terminates` of the one head
/// become `fls_valid` and `fls_terminates`, and `chain_avoids` becomes
/// `fls_avoids`.  Each lemma keeps the shape of the one it lifts.

module GC.Gen.AllocLists

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FreeLists
open GC.Spec.Allocator.Lists
open GC.Lib.Header

module U64 = FStar.UInt64
module Mark = GC.Spec.Mark
module SC = GC.Spec.SizeClass
module SA = GC.Spec.Allocator
module AL = GC.Spec.Allocator.Lemmas

/// `a` is a word of `x`'s extent: its header or one of its fields.
let in_extent (g: heap) (x: obj_addr) (a: nat) : prop =
  a % 8 == 0 /\
  U64.v (hd_address x) <= a /\ a + 8 <= U64.v x + U64.v (wosize_of_object x g) * 8

/// Words of two distinct objects are distinct.
val extents_apart (g: heap) (x y: obj_addr) (a b: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ Seq.mem y (objects zero_addr g) /\
                    x <> y /\ in_extent g x a /\ in_extent g y b)
          (ensures a + 8 <= b \/ b + 8 <= a)

/// The allocator's entry conditions.
let alloc_lists_pre (g: heap) (fls: fl_state) : prop =
  well_formed_heap_part1 g /\ fls_valid g fls /\ fls_terminates g fls

/// ---------------------------------------------------------------------------
/// The object walk and well-formedness
/// ---------------------------------------------------------------------------

val alloc_lists_preserves_objects_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                      Seq.mem x (objects zero_addr r.heap_out))))

val alloc_lists_preserves_wfh_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls)
          (ensures well_formed_heap_part1 (alloc_lists_spec g fls requested_wz).heap_out)

val alloc_lists_preserves_wfh_part4 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls /\ well_formed_heap_part4 g)
          (ensures well_formed_heap_part4 (alloc_lists_spec g fls requested_wz).heap_out)

val alloc_lists_preserves_no_black_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls /\ Mark.no_black_objects g)
          (ensures Mark.no_black_objects (alloc_lists_spec g fls requested_wz).heap_out)

val alloc_lists_preserves_dense_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls /\ heap_objects_dense g)
          (ensures heap_objects_dense (alloc_lists_spec g fls requested_wz).heap_out)

/// ---------------------------------------------------------------------------
/// The free lists
/// ---------------------------------------------------------------------------

val alloc_lists_preserves_fls_valid_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    fls_valid r.heap_out r.fls_out))

val alloc_lists_preserves_fls_terminates_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    fls_terminates r.heap_out r.fls_out))

/// The allocated object is on no list.
val alloc_lists_obj_not_in_lists_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls /\ requested_wz >= 1 /\
                    (alloc_lists_spec g fls requested_wz).obj_out <> 0UL)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    fls_avoids r.heap_out r.fls_out r.obj_out))

/// An object no list visits stays unvisited.
val alloc_lists_preserves_avoids_other
  (g: heap) (fls: fl_state) (requested_wz: nat) (excl: U64.t)
  : Lemma (requires alloc_lists_pre g fls /\ requested_wz >= 1 /\
                    fls_avoids g fls excl /\
                    U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                    U64.v excl % U64.v mword == 0 /\
                    Seq.mem (excl <: obj_addr) (objects zero_addr g))
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    fls_avoids r.heap_out r.fls_out excl))

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

/// The body of an object no list visits is not written.
val alloc_lists_read_other
  (g: heap) (fls: fl_state) (requested_wz: nat) (other: obj_addr) (addr: hp_addr)
  : Lemma (requires alloc_lists_pre g fls /\ requested_wz >= 1 /\
                    Seq.mem other (objects zero_addr g) /\
                    fls_avoids g fls (other <: U64.t) /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other g) * 8)
          (ensures read_word (alloc_lists_spec g fls requested_wz).heap_out addr ==
                   read_word g addr)

/// Nor is the header of an object no list visits.
val alloc_lists_read_header_other_part1
  (g: heap) (fls: fl_state) (requested_wz: nat) (excl: obj_addr)
  : Lemma (requires alloc_lists_pre g fls /\
                    Seq.mem excl (objects zero_addr g) /\
                    (excl <: U64.t) <> (alloc_lists_spec g fls requested_wz).obj_out /\
                    fls_avoids g fls (excl <: U64.t))
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==>
                    read_word r.heap_out (hd_address excl) == read_word g (hd_address excl)))

/// Out of memory changes nothing.
val alloc_lists_oom_unchanged (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out == 0UL ==> (r.heap_out == g /\ r.fls_out == fls)))

/// ---------------------------------------------------------------------------
/// The allocated object
/// ---------------------------------------------------------------------------

val alloc_lists_obj_valid (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0)))

val alloc_lists_obj_in_objects_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     Seq.mem (r.obj_out <: obj_addr) (objects zero_addr r.heap_out))))

val alloc_lists_obj_body_within_heap (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     (let obj_out : obj_addr = r.obj_out in
                      U64.v obj_out +
                        U64.v (wosize_of_object obj_out r.heap_out) * 8 <= heap_size))))

/// The allocated object declares exactly the requested wosize.
val alloc_lists_obj_wosize_exact_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires fls_valid g fls /\ requested_wz < pow2 54)
          (ensures (let wz = if requested_wz = 0 then 1 else requested_wz in
                    let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     (let obj_out : obj_addr = r.obj_out in
                      U64.v (wosize_of_object obj_out r.heap_out) == wz))))

val alloc_lists_obj_wosize_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires fls_valid g fls)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     U64.v (wosize_of_object (r.obj_out <: obj_addr) r.heap_out) >=
                       (if requested_wz = 0 then 1 else requested_wz))))

val alloc_lists_obj_wosize_upper_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires fls_valid g fls)
          (ensures (let wz = if requested_wz = 0 then 1 else requested_wz in
                    let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword == 0 /\
                     (let obj_out : obj_addr = r.obj_out in
                      U64.v (wosize_of_object obj_out r.heap_out) <= wz))))

/// The allocated object is not an object no list visits.
val alloc_lists_obj_ne_excl (g: heap) (fls: fl_state) (requested_wz: nat) (excl: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\ fls_valid g fls /\
                    fls_avoids g fls excl /\
                    U64.v excl >= U64.v mword /\
                    U64.v excl < heap_size /\
                    U64.v excl % U64.v mword = 0 /\
                    Seq.mem (excl <: obj_addr) (objects zero_addr g))
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==> r.obj_out <> excl))

/// The allocated object is white.
val alloc_lists_obj_not_blue_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL ==>
                    (U64.v r.obj_out >= U64.v mword /\
                     U64.v r.obj_out < heap_size /\
                     U64.v r.obj_out % U64.v mword = 0 /\
                     color_of_object (r.obj_out <: obj_addr) r.heap_out == White)))

/// A blue object other than the allocated one stays blue.
val alloc_lists_preserves_blue_part1
  (g: heap) (fls: fl_state) (requested_wz: nat) (h: obj_addr)
  : Lemma (requires alloc_lists_pre g fls /\ requested_wz >= 1 /\
                    Seq.mem (h <: U64.t) (objects zero_addr g) /\
                    is_blue h g = true)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out <> 0UL /\ (h <: U64.t) <> r.obj_out ==>
                    is_blue h r.heap_out = true))

/// Any object the allocation creates other than the allocated one is blue.
val alloc_lists_new_objects_blue_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls /\ requested_wz >= 1 /\
                    (alloc_lists_spec g fls requested_wz).obj_out <> 0UL)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    forall (x: obj_addr).
                      Seq.mem x (objects zero_addr r.heap_out) /\
                      ~(Seq.mem x (objects zero_addr g)) /\
                      (x <: U64.t) <> r.obj_out ==>
                      is_blue x r.heap_out = true))

/// The only object the allocation creates is the one it returns.
val alloc_lists_only_new_is_obj_out_part1 (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls /\ requested_wz >= 1 /\
                    (alloc_lists_spec g fls requested_wz).obj_out <> 0UL)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    forall (x: obj_addr).
                      Seq.mem x (objects zero_addr r.heap_out) /\
                      ~(Seq.mem x (objects zero_addr g)) ==>
                      (x <: U64.t) == r.obj_out))

/// ---------------------------------------------------------------------------
/// The shape of the lists
/// ---------------------------------------------------------------------------

/// On a list where the single-list first fit finds a block, the allocation
/// finds it too.
val alloc_on_succeeds (g: heap) (fls: fl_state) (j: nat) (wz: pos)
  : Lemma (requires well_formed_heap_part1 g /\ fls_valid g fls /\ j < SC.n_lists /\
                    (SA.alloc_spec g (fls_head fls j) wz).SA.obj_out <> 0UL)
          (ensures (alloc_on g fls j wz).obj_out <> 0UL)

/// After a successful allocation from list `j` (`alloc_lists_list`), list `j`
/// is the single-list allocation's on that list, at the request or, when the
/// remainder moves (`relists`), at the size of the whole block; every other
/// list keeps its cells and its head, but the list a moved block goes on;
/// headers are that allocation's except the block's; and a moved block is on
/// a list, linked to that list's old head, and the rest of the heap is the
/// whole-block allocation's outside the block.
val alloc_lists_struct (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls /\ (alloc_lists_spec g fls requested_wz).obj_out <> 0UL)
          (ensures (let j = alloc_lists_list g fls requested_wz in
                    let wz = req_wz requested_wz in
                    let fp = fls_head fls j in
                    let w = first_fit_size g fp wz heap_words in
                    let rl = relists j w wz in
                    let rS = SA.alloc_spec g fp (if rl then w else wz) in
                    let r = alloc_lists_spec g fls requested_wz in
                    j < SC.n_lists /\
                    rS.SA.obj_out <> 0UL /\
                    (rl ==> w >= 1) /\
                    (not rl ==> rS.SA.obj_out == r.obj_out) /\
                    (SA.alloc_spec g fp wz).SA.obj_out == r.obj_out /\
                    fls_head r.fls_out j == rS.SA.fp_out /\
                    (forall (y: U64.t). AL.chain_avoids r.heap_out rS.SA.fp_out y heap_words ==
                                        AL.chain_avoids rS.SA.heap_out rS.SA.fp_out y heap_words) /\
                    (forall (k: nat) (y: U64.t).
                       k < SC.n_lists /\ k <> j /\
                       AL.chain_avoids g (fls_head fls k) y heap_words = false ==>
                       AL.chain_avoids r.heap_out (fls_head r.fls_out k) y heap_words = false) /\
                    (forall (y: obj_addr).
                       Seq.mem y (objects zero_addr g) /\ (y <: U64.t) <> rS.SA.obj_out ==>
                       read_word r.heap_out (hd_address y) == read_word rS.SA.heap_out (hd_address y)) /\
                    (rl ==> ~(fls_avoids r.heap_out r.fls_out rS.SA.obj_out)) /\
                    (not rl ==> r.heap_out == rS.SA.heap_out) /\
                    (forall (k: nat). k < SC.n_lists /\ k <> j ==>
                       fls_head r.fls_out k == fls_head fls k \/
                       (rl /\ fls_head r.fls_out k == rS.SA.obj_out)) /\
                    (rl ==> U64.v rS.SA.obj_out >= U64.v mword /\ U64.v rS.SA.obj_out < heap_size /\
                            U64.v rS.SA.obj_out % U64.v mword == 0 /\
                            Seq.mem (rS.SA.obj_out <: obj_addr) (objects zero_addr g) /\
                            (forall (a: hp_addr). read_word r.heap_out a <> read_word rS.SA.heap_out a ==>
                               in_extent g (rS.SA.obj_out <: obj_addr) (U64.v a)) /\
                            read_word r.heap_out (rS.SA.obj_out <: hp_addr) ==
                              fls_head fls (SC.size_class (w - wz - 1)))))
