module GC.SPOT.ThreeObjects.Full

/// Full 3-object SPOT using real allocators
/// - Object A and B in minor heap (A reachable, B unreachable)
/// - Object C in major heap, pointing to A
/// - Call gen_gc, prove A and C survive, B is collected

#lang-pulse
open Pulse.Lib.Pervasives
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array
module Vec = Pulse.Lib.Vec

open GC.Spec.Base
open GC.Spec.Allocator
open GC.Impl.Heap
open GC.Impl.Allocator
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl
open GC.SPOT.InitHeapLemmas

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"

///  **Step 1**: Create and initialize major heap
fn create_major_heap ()
  returns gh: (gen_heap_t & erased heap)
  ensures exists* s.
    is_gen_heap gh s **
    pure (
      // Major heap is one big blue free block
      let (h_major, _fp) = init_heap_spec (Seq.create heap_size 0uy) in
      fst s == h_major
    )
{
  let heap_sz = SZ.uint64_to_sizet (U64.uint_to_t heap_size);
  let major_bytes = A.alloc 0uy heap_sz;
  
  // Initialize heap to one big free block
  let fp_ref = R.alloc 0UL;
  let major_h : heap_t = { data = major_bytes; fp_ref = fp_ref };
  
  let fp = init_heap major_h;
  
  // At this point:
  // - (major_h.data, fp) == init_heap_spec (Seq.create heap_size 0uy)
  // - But we need well_formed_heap to call allocate
  
  // Create empty minor heap
  let minor_h = alloc_minor_heap ();
  
  // Build gen_heap
  let rs_ref = R.alloc 0UL;
  let gh : gen_heap_t = {
    major = major_h;
    minor = minor_h;
    remembered_set_size = rs_ref
  };
  
  // TODO: Prove this satisfies is_gen_heap
  // For now, return with admit
  admit();
  (gh, hide (fst (init_heap_spec (Seq.create heap_size 0uy))))
}

/// **Step 2**: Allocate object C in major heap
/// BLOCKER: This requires well_formed_heap, which init_heap doesn't provide
fn allocate_major_object
  (gh: gen_heap_t)
  (#s: erased (heap & minor_heap_state))
requires is_gen_heap gh s
returns obj_C: U64.t
ensures exists* s'.
  is_gen_heap gh s' **
  pure (
    // obj_C is a valid allocated object in major heap
    obj_C > 0UL
  )
{
  with _smh. assert (is_minor gh.minor _smh);
  with _fp. assert (R.pts_to gh.major.fp_ref _fp);
  
  unfold (is_heap gh.major);
  with s_major. assert (A.pts_to gh.major.data s_major);
  
  // BLOCKER: allocate requires well_formed_heap
  // We have: (s_major, fp) == init_heap_spec (zeros)
  // We need: well_formed_heap s_major
  // Solution: Call init_heap_well_formed lemma
  
  // TODO: Extract the ghost heap state, call lemma
  admit();
  
  // let obj_addr = allocate gh.major !gh.major.fp_ref 2UL;  // wosize=2 (1 field + padding)
  0UL  // placeholder
}

/// **Step 3**: Allocate A and B in minor heap
fn allocate_minor_objects
  (gh: gen_heap_t)
  (#s: erased (heap & minor_heap_state))
requires is_gen_heap gh s
returns (obj_A: U64.t & obj_B: U64.t)
ensures exists* s'.
  is_gen_heap gh s' **
  pure (
    // Both objects allocated
    obj_A > 0UL /\ obj_B > 0UL /\ obj_A <> obj_B
  )
{
  // Minor allocator doesn't require well_formed_heap - this works!
  let obj_A = minor_alloc gh.minor 1UL 0UL;  // 1 field, tag=0
  let obj_B = minor_alloc gh.minor 1UL 0UL;  // 1 field, tag=0
  
  (obj_A, obj_B)
}

/// **Step 4**: Wire up pointers (C points to A)
fn wire_pointers
  (gh: gen_heap_t)
  (obj_C obj_A: U64.t)
  (#s: erased (heap & minor_heap_state))
requires is_gen_heap gh s **
  pure (obj_C > 0UL /\ obj_A > 0UL)
ensures exists* s'.
  is_gen_heap gh s' **
  pure (
    // C.field[0] = A
    true  // TODO: formalize
  )
{
  // Write field in C (major object) pointing to A (minor object)
  unfold (is_heap gh.major);
  with s_major. assert (A.pts_to gh.major.data s_major);
  
  // Calculate field address: obj_C + 0*mword
  let field_addr = obj_C;  // First field
  
  // Write A's address into C's field
  // TODO: Use write_word wrapper from GC.Impl.Object
  admit();
  ()
}

/// **Step 5**: Build roots and call GC
fn three_object_spot ()
  ensures emp ** pure (true)  // TODO: meaningful postcondition
{
  // Step 1: Create major heap with one big free block
  let (gh, s0) = create_major_heap ();
  
  // Step 2: Allocate C in major heap
  // BLOCKER: Requires well_formed_heap lemma
  let obj_C = allocate_major_object gh;
  
  // Step 3: Allocate A and B in minor heap
  let (obj_A, obj_B) = allocate_minor_objects gh;
  
  // Step 4: Wire pointers (C.field[0] = A)
  wire_pointers gh obj_C obj_A;
  
  // Step 5: Build roots array [obj_A]
  let roots = A.alloc obj_A 1sz;
  
  // Step 6: Build remembered set array [obj_C + field_offset]
  let slots = A.alloc obj_C 1sz;  // Simplified: just object address
  
  // Step 7: Call gen_gc
  // TODO: Unfold is_gen_heap, build witnesses, call gen_gc
  admit();
  
  // Step 8: Verify postcondition
  // - obj_A survived (promoted to major)
  // - obj_B was collected
  // - obj_C survived
  // - C still points to promoted A
  admit();
  
  // Cleanup
  drop_ (pts_to roots _);
  drop_ (pts_to slots _);
  ()
}

#pop-options
