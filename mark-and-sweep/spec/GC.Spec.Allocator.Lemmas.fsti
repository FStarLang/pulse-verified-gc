(*
   GC.Spec.Allocator.Lemmas — Interface for allocator-GC bridge proofs.

   Main theorem: alloc_spec preserves well_formed_heap, so the GC can be
   called after any sequence of allocations.
*)
module GC.Spec.Allocator.Lemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq
module Header = GC.Lib.Header
module Mark = GC.Spec.Mark
/// getWosize of make_header returns the original wosize
val make_header_getWosize : (wz: U64.t{U64.v wz < pow2 54}) ->
                            (c: U64.t{U64.v c < 4}) ->
                            (t: U64.t{U64.v t < 256}) ->
  Lemma (getWosize (make_header wz c t) == wz)

/// getTag of make_header returns the original tag
val make_header_getTag : (wz: U64.t{U64.v wz < pow2 54}) ->
                         (c: U64.t{U64.v c < 4}) ->
                         (t: U64.t{U64.v t < 256}) ->
  Lemma (U64.v (getTag (make_header wz c t)) == U64.v t)

/// alloc_from_block preserves well_formed_heap
val alloc_from_block_preserves_wf :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz) /\
                  (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  well_formed_heap g'))

/// Free-list validity: each node is a valid object with wosize >= 1,
/// no self-loops, and the successor (if any) is also fl_valid.
val fl_valid (g: heap) (fp: U64.t) (fuel: nat) : Tot prop (decreases fuel)

/// fl_valid extractors
val fl_valid_gives_mem : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures Seq.mem fp (objects zero_addr g))

val fl_valid_gives_wosize : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures U64.v (wosize_of_object (fp <: obj_addr) g) >= 1)

/// **Theorem**: alloc_from_block preserves object membership AND the remainder
/// (if split) is in the post-alloc objects list.
val alloc_from_block_objects_facts :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz) /\
                  (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g')) /\
                  (is_pointer_field rem_fp ==> Seq.mem rem_fp (objects zero_addr g'))))

/// **Main theorem**: alloc_spec preserves well_formed_heap.
val alloc_spec_preserves_wf : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap g /\
                  fl_valid g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  well_formed_heap r.heap_out))

/// fl_valid introduction: null pointer terminates the free list.
val fl_valid_null : (g: heap) -> (fuel: nat) ->
  Lemma (requires fuel > 0)
        (ensures fl_valid g 0UL fuel)

/// fl_valid introduction: a valid node with a valid successor.
val fl_valid_step : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  Seq.mem fp (objects zero_addr g) /\
                  U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
                  (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
                    read_word g (fp <: obj_addr) <> fp /\
                    fl_valid g (read_word g (fp <: obj_addr)) (fuel - 1)))
        (ensures fl_valid g fp fuel)

/// fl_valid eliminator: extract all components from fl_valid.
val fl_valid_elim : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures Seq.mem fp (objects zero_addr g) /\
                 U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
                 (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
                   read_word g (fp <: obj_addr) <> fp /\
                   fl_valid g (read_word g (fp <: obj_addr)) (fuel - 1)))

/// fl_valid base case: fuel = 0 makes fl_valid trivially true.
val fl_valid_zero : (g: heap) -> (fp: U64.t) ->
  Lemma (fl_valid g fp 0)

/// fl_valid terminal case: out of bounds, unaligned, or null pointer.
val fl_valid_terminal : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  (fp = 0UL \/ U64.v fp < U64.v mword \/ U64.v fp >= heap_size \/
                   U64.v fp % U64.v mword <> 0))
        (ensures fl_valid g fp fuel)

/// fl_valid monotonicity: more fuel implies less fuel.
val fl_valid_weaken : (g: heap) -> (fp: U64.t) -> (fuel_strong: nat) -> (fuel_weak: nat) ->
  Lemma (requires fl_valid g fp fuel_strong /\ fuel_weak <= fuel_strong)
        (ensures fl_valid g fp fuel_weak)

/// Free-list chain termination: the chain from fp reaches a terminal node
/// (0UL, out of bounds, or unaligned) within the given number of steps.
val fl_chain_terminates (g: heap) (fp: U64.t) (steps: nat) : Tot bool (decreases steps)

/// Terminal base cases: 0UL, out of bounds, or misaligned -> always terminates.
val fl_chain_terminates_terminal (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fp = 0UL \/ U64.v fp < U64.v mword \/ U64.v fp >= heap_size \/ U64.v fp % U64.v mword <> 0)
          (ensures fl_chain_terminates g fp steps = true)

/// Step case: fp is valid, hd + 16 <= heap_size, and the tail terminates.
val fl_chain_terminates_step (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    (let hd = hd_address (fp <: obj_addr) in
                     U64.v hd + 16 <= heap_size ==>
                     fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1)))
          (ensures fl_chain_terminates g fp steps)

/// Elimination: if fl_chain_terminates and fp is valid with hd+16 <= heap_size,
/// then the tail also terminates.
val fl_chain_terminates_elim (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fl_chain_terminates g fp steps /\
                    steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1) = true)

/// Valid fp with 0 steps never terminates.
val fl_chain_terminates_valid_zero (g: heap) (fp: U64.t)
  : Lemma (requires U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0)
          (ensures fl_chain_terminates g fp 0 = false)

/// walk_chain: walk n steps following free-list links (stops at terminal nodes).
val walk_chain (g: heap) (fp: U64.t) (n: nat) : Tot U64.t (decreases n)

/// walk_chain_valid: all intermediate nodes (positions 0..n-1) are valid (non-terminal).
val walk_chain_valid (g: heap) (fp: U64.t) (n: nat) : Tot prop (decreases n)

/// walk_chain_valid prefix: truncating preserves validity.
val walk_chain_valid_prefix (g: heap) (fp: U64.t) (k j: nat)
  : Lemma (requires walk_chain_valid g fp k /\ j <= k)
          (ensures walk_chain_valid g fp j)

/// walk_chain_valid_at: position j (< k) in a valid chain is a valid node.
val walk_chain_valid_at (g: heap) (fp: U64.t) (k j: nat)
  : Lemma (requires walk_chain_valid g fp k /\ j < k)
          (ensures (let node = walk_chain g fp j in
                    U64.v node >= U64.v mword /\ U64.v node < heap_size /\
                    U64.v node % U64.v mword = 0 /\
                    U64.v (hd_address (node <: obj_addr)) + 16 <= heap_size))

/// walk_chain_valid_snoc: extend walk_chain_valid if the endpoint is valid.
val walk_chain_valid_snoc (g: heap) (fp: U64.t) (k: nat)
  : Lemma (requires walk_chain_valid g fp k /\
                    (let node = walk_chain g fp k in
                     U64.v node >= U64.v mword /\ U64.v node < heap_size /\
                     U64.v node % U64.v mword = 0 /\
                     U64.v (hd_address (node <: obj_addr)) + 16 <= heap_size))
          (ensures walk_chain_valid g fp (k + 1))

/// walk_chain_append: composing walks.
val walk_chain_append (g: heap) (fp: U64.t) (m n: nat)
  : Lemma (requires walk_chain_valid g fp m)
          (ensures walk_chain g fp (m + n) = walk_chain g (walk_chain g fp m) n)

/// Unfolding n valid steps of fl_chain_terminates.
val fl_chain_terminates_unfold_steps (g: heap) (fp: U64.t) (n fuel: nat)
  : Lemma (requires n <= fuel /\ walk_chain_valid g fp n)
          (ensures fl_chain_terminates g fp fuel = fl_chain_terminates g (walk_chain g fp n) (fuel - n))

/// A k-cycle prevents termination for any fuel.
val fl_chain_kcycle_not_terminates (g: heap) (fp: U64.t) (k fuel: nat)
  : Lemma (requires k > 0 /\ walk_chain g fp k = fp /\ walk_chain_valid g fp k)
          (ensures fl_chain_terminates g fp fuel = false)

/// alloc_spec preserves fl_valid: the free-list chain remains valid after allocation.
val alloc_spec_preserves_fl_valid : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  fl_valid r.heap_out r.fp_out (heap_size / U64.v mword)))

/// chain_avoids: boolean test for "fp chain does not visit excl".
val chain_avoids (g: heap) (fp excl: U64.t) (steps: nat) : Tot bool

/// chain_avoids_head_ne: if chain_avoids is true and fp is a valid chain node with fuel > 0,
/// then fp ≠ excl.
val chain_avoids_head_ne (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ fuel > 0)
          (ensures fp <> excl)

/// chain_avoids_tail: one-step decomposition of chain_avoids.
/// When chain_avoids is true at a valid node with hd+16 <= heap_size,
/// the successor chain also avoids excl.
val chain_avoids_tail (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ fuel > 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures chain_avoids g (read_word g (fp <: obj_addr)) excl (fuel - 1) = true)

/// chain_avoids_transfer: transfer chain_avoids between heaps when link reads are preserved
/// for chain nodes (objects in objects(g) with wosize >= 1).
val chain_avoids_transfer (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                      U64.v (wosize_of_object a g) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      a <> excl ==>
                        read_word g' a == read_word g a))
          (ensures chain_avoids g' fp excl fuel = true)

/// chain_avoids_weaken: if chain_avoids holds for fuel steps, it also holds for fewer steps.
val chain_avoids_weaken (g: heap) (fp excl: U64.t) (fuel fuel': nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\ fuel' <= fuel)
          (ensures chain_avoids g fp excl fuel' = true)

/// first_hit: position of first occurrence of dst_obj when chain_avoids = false.
val first_hit (g: heap) (fp dst_obj: U64.t) (fuel: nat) : Tot nat

/// first_hit_spec: characterization of first_hit when chain_avoids = false.
val first_hit_spec (g: heap) (fp dst_obj: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp dst_obj fuel = false)
          (ensures walk_chain g fp (first_hit g fp dst_obj fuel) = dst_obj /\
                   first_hit g fp dst_obj fuel <= fuel /\
                   walk_chain_valid g fp (first_hit g fp dst_obj fuel))

/// not_in_fl_chain_b: boolean version of "dst_obj not in chain from fp".
/// (Alias for chain_avoids.)
val not_in_fl_chain_b (g: heap) (fp: U64.t) (dst_obj: U64.t) (fuel: nat) : Tot bool

/// **Theorem**: A node does not appear in the chain starting from its successor.
/// (Boolean version — suitable for direct case analysis.)
val fl_chain_predecessor_not_in_suffix_b (g: heap) (obj: U64.t) (fuel: nat)
  : Lemma (requires fl_chain_terminates g obj fuel /\
                    fl_valid g obj fuel /\
                    U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\ U64.v obj % U64.v mword = 0 /\
                    U64.v (hd_address (obj <: obj_addr)) + 16 <= heap_size /\
                    fuel > 0)
          (ensures not_in_fl_chain_b g (read_word g (obj <: obj_addr)) obj (fuel - 1) = true)

/// alloc_spec preserves fl_chain_terminates: the free-list chain still terminates after allocation.
val alloc_spec_preserves_fl_chain_terminates : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  fl_chain_terminates r.heap_out r.fp_out (heap_size / U64.v mword)))

/// **Theorem**: alloc_spec preserves object membership.
/// Every object that existed before allocation still exists afterward.
val alloc_spec_preserves_objects : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap g /\
                  fl_valid g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                    Seq.mem x (objects zero_addr r.heap_out))))

/// get_color of make_header returns the original color bits
val make_header_getColor : (wz: U64.t{U64.v wz < pow2 54}) ->
                           (c: U64.t{U64.v c < 4}) ->
                           (t: U64.t{U64.v t < 256}) ->
  Lemma (Header.get_color (U64.v (make_header wz c t)) == U64.v c)

/// **Theorem**: alloc_spec preserves no_black_objects.
val alloc_spec_preserves_no_black : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires GC.Spec.Mark.no_black_objects g /\
                  well_formed_heap g /\
                  fl_valid g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  GC.Spec.Mark.no_black_objects r.heap_out))

/// chain_avoids_transfer_excl2: transfer chain_avoids when reads preserved except at excl or excl2.
val chain_avoids_transfer_excl2 (g g': heap) (fp excl excl2: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    chain_avoids g fp excl2 fuel = true /\
                    fl_valid g fp fuel /\
                    (forall (a: U64.t).
                       (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                        Seq.mem a (objects zero_addr g) /\ a <> excl /\ a <> excl2) ==>
                       (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                        U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                          read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
          (ensures chain_avoids g' fp excl fuel = true)

/// chain_avoids_transfer_excl2_obj: variant with forall over obj_addr (avoids coercion issues).
val chain_avoids_transfer_excl2_obj (g g': heap) (fp excl excl2: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    chain_avoids g fp excl2 fuel = true /\
                    fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                      U64.v (wosize_of_object a g) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      (a <: U64.t) <> excl /\ (a <: U64.t) <> excl2 ==>
                        read_word g' a == read_word g a))
          (ensures chain_avoids g' fp excl fuel = true)

/// **Theorem**: alloc_spec removes obj_out from the chain.
val alloc_spec_obj_not_in_chain : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL)
        (ensures (let r = alloc_spec g fp requested_wz in
                  chain_avoids r.heap_out r.fp_out r.obj_out (heap_size / U64.v mword) = true))

/// **Theorem**: alloc_spec preserves object membership under just well_formed_heap_part1.
/// (Weaker precondition than alloc_spec_preserves_objects.)
val alloc_spec_preserves_objects_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                    Seq.mem x (objects zero_addr r.heap_out))))

/// **Theorem**: alloc_spec preserves well_formed_heap_part1.
val alloc_spec_preserves_wfh_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  well_formed_heap_part1 r.heap_out))

/// **Theorem**: alloc_spec preserves fl_valid under well_formed_heap_part1.
val alloc_spec_preserves_fl_valid_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  fl_valid r.heap_out r.fp_out (heap_size / U64.v mword)))

/// **Theorem**: alloc_spec preserves fl_chain_terminates under well_formed_heap_part1.
val alloc_spec_preserves_fl_chain_terminates_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  fl_chain_terminates r.heap_out r.fp_out (heap_size / U64.v mword)))

/// **Theorem**: alloc_spec removes obj_out from the chain, under well_formed_heap_part1.
val alloc_spec_obj_not_in_chain_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL)
        (ensures (let r = alloc_spec g fp requested_wz in
                  chain_avoids r.heap_out r.fp_out r.obj_out (heap_size / U64.v mword) = true))

/// ---------------------------------------------------------------------------
/// Allocation framing: alloc_spec preserves reads in the body of the
/// allocated object (it only modifies headers/links, not the body itself).
/// ---------------------------------------------------------------------------

/// **Theorem**: alloc_spec does not modify the body of the allocated block.
/// For any address in [obj_out, obj_out + requested_wz * 8), the read after
/// allocation equals the read before allocation.
val alloc_spec_read_body : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) -> (addr: hp_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL /\
                  (let r = alloc_spec g fp requested_wz in
                   U64.v addr >= U64.v r.obj_out /\
                   U64.v addr + 8 <= U64.v r.obj_out + requested_wz * 8))
        (ensures (let r = alloc_spec g fp requested_wz in
                  read_word r.heap_out addr == read_word g addr))

/// **Theorem**: alloc_spec does not modify the body of a different object
/// that is separated from the free-list writes.
/// addr is in the body of some already-allocated object (not in the free list).
val alloc_spec_read_other : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
                            (other: obj_addr) -> (addr: hp_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  Seq.mem other (objects zero_addr g) /\
                  // other is NOT in the free-list chain
                  chain_avoids g fp other (heap_size / U64.v mword) = true /\
                  // addr is in the body of other
                  U64.v addr >= U64.v other /\
                  U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other g) * 8)
        (ensures (let r = alloc_spec g fp requested_wz in
                  read_word r.heap_out addr == read_word g addr))

/// **Theorem**: alloc_spec preserves chain_avoids for an excluded object.
/// If excl was not in the free-list chain before alloc, it's not in the chain after.
val alloc_spec_preserves_chain_avoids_other : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
                                              (excl: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  chain_avoids g fp excl (heap_size / U64.v mword) = true /\
                  U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                  U64.v excl % U64.v mword == 0 /\
                  Seq.mem (excl <: obj_addr) (objects zero_addr g))
        (ensures (let r = alloc_spec g fp requested_wz in
                  chain_avoids r.heap_out r.fp_out excl (heap_size / U64.v mword) = true))

/// **Theorem**: alloc_spec preserves well_formed_heap_part4 (no infix objects).
/// Under just well_formed_heap_part1, fl_valid, fl_chain_terminates.
/// All newly created headers (allocated block + remainder) have tag=0 ≠ infix_tag.
/// Existing non-free-list objects have unchanged headers.
val alloc_spec_preserves_wfh_part4 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  well_formed_heap_part4 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  well_formed_heap_part4 r.heap_out))

/// ---------------------------------------------------------------------------
/// Allocation framing: field reads for non-allocated objects
/// ---------------------------------------------------------------------------

/// **Theorem**: alloc_spec preserves reads at non-first-field positions
/// of objects that are NOT the allocated block.
/// (Works for objects ON the free-list chain too — no chain_avoids needed.)
val alloc_spec_read_field_gt0 :
  (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  (src: obj_addr) -> (j: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL /\
                  Seq.mem src (objects zero_addr g) /\
                  src <> (alloc_spec g fp requested_wz).obj_out /\
                  j > 0 /\
                  j < U64.v (wosize_of_object src g) /\
                  U64.v src + j * 8 + 8 <= heap_size)
        (ensures (let r = alloc_spec g fp requested_wz in
                  let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
                  read_word r.heap_out addr == read_word g addr))

/// **Theorem**: In the split case (block_wz - wz >= 2), the remainder fp
/// returned by alloc_from_block is a valid pointer AND is in objects of
/// the output heap. Requires only well_formed_heap_part1.
val alloc_from_block_rem_in_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   bwz >= wz /\ bwz - wz >= 2))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                  is_pointer_field rem_fp /\
                  Seq.mem rem_fp (objects zero_addr g')))

/// **Theorem**: alloc_from_block preserves object membership under just
/// well_formed_heap_part1. (Public wrapper for internal part1 proof.)
val alloc_from_block_preserves_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))

/// **Theorem**: Any object in the post-alloc heap that was NOT in the pre-alloc
/// heap is blue. (The only possible new object is the remainder block,
/// which receives a blue header.)
val alloc_spec_new_objects_blue_part1 :
  (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL)
        (ensures (let r = alloc_spec g fp requested_wz in
                  forall (x: obj_addr).
                    Seq.mem x (objects zero_addr r.heap_out) /\
                    ~(Seq.mem x (objects zero_addr g)) ==>
                    is_blue x r.heap_out = true))

/// **Theorem**: Backward inclusion for alloc_from_block (split case).
/// If h is in objects of the output heap but NOT in objects of the input heap,
/// then h must be the remainder address returned by alloc_from_block.
val alloc_from_block_objects_backward_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (h: obj_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   bwz >= wz /\ wz >= 1 /\ bwz - wz >= 2) /\
                  (let (g', _) = alloc_from_block g obj wz next_fp in
                   Seq.mem h (objects zero_addr g') /\
                   ~(Seq.mem h (objects zero_addr g))))
        (ensures h == snd (alloc_from_block g obj wz next_fp))

/// **Theorem**: alloc_spec preserves no_black_objects under well_formed_heap_part1.
val alloc_spec_preserves_no_black_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires Mark.no_black_objects g /\
                  well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  Mark.no_black_objects r.heap_out))
