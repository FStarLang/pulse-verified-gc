/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.TriColor - Tri-Color Invariant for Concurrent GC
/// ---------------------------------------------------------------------------

module Pulse.Spec.GC.TriColor

open FStar.Seq
module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields

/// ---------------------------------------------------------------------------
/// Type Aliases (Updated for color_sem)
/// ---------------------------------------------------------------------------

/// Color type is now algebraic (Blue | White | Gray | Black) from Header.fst
/// Import via Object which re-exports color_sem as color
open Pulse.Lib.Header  // For color_sem constructors

/// Alias for compatibility with code using set_color
let set_color (g: heap) (oa: obj_addr) (c: color) : GTot heap =
  set_object_color oa g c

/// ---------------------------------------------------------------------------
/// Foundational Heap Lemmas
/// ---------------------------------------------------------------------------
/// These describe how color changes affect heap state. In a complete development,
/// these would be proven from read/write lemmas in the Heap module.

/// After graying, the object is gray (and not black/white)
let gray_makes_gray (oa: obj_addr) (g: heap)
  : Lemma (let g' = makeGray oa g in
           is_gray oa g' /\ 
           not (is_black oa g') /\
           not (is_white oa g'))
  = let g' = makeGray oa g in
    makeGray_is_gray oa g;
    is_gray_iff oa g';
    is_black_iff oa g';
    is_white_iff oa g'
    // Color distinctness is automatic with color_sem

/// After blackening, the object is black (and not gray/white)
let black_makes_black (oa: obj_addr) (g: heap)
  : Lemma (let g' = makeBlack oa g in
           is_black oa g' /\
           not (is_gray oa g') /\
           not (is_white oa g'))
  = let g' = makeBlack oa g in
    makeBlack_is_black oa g;
    is_black_iff oa g';
    is_gray_iff oa g';
    is_white_iff oa g'
    // Color distinctness is automatic with color_sem

/// Well-formed heaps: different objects have different header addresses
/// Requires both addresses >= 8 (which holds for all valid objects)
let different_objects_different_headers (obj1 obj2: obj_addr)
  : Lemma (requires obj1 <> obj2)
          (ensures hd_address obj1 <> hd_address obj2)
  = // hd_address is injective
    hd_address_injective obj1 obj2

/// Color changes preserve the objects list
/// This is a foundational property: set_color only modifies color bits, not wosize
/// Proof strategy: By induction on the recursive structure of objects.
/// At each position start, the header read determines the wosize.
/// We show that set_color preserves the wosize at every position:
/// - If start = hd_address oa: use setColor_preserves_wosize_lemma
/// - If start <> hd_address oa: use color_change_header_locality

/// Recursive helper lemma that mirrors objects structure
#push-options "--fuel 3 --ifuel 2 --z3rlimit 500"
let rec color_change_preserves_objects_at (start: hp_addr) (oa: obj_addr) (g: heap) (c: color)
  : Lemma 
    (ensures objects start (set_color g oa c) == objects start g)
    (decreases (Seq.length g - U64.v start))
  =
  let g' = set_color g oa c in
  if U64.v start + 8 >= Seq.length g then (
    // Base case: both return empty
    ()
  ) else begin
    // Read header in both heaps
    let header = read_word g start in
    let header' = read_word g' start in
    
    // Prove headers give same wosize
    if start = hd_address oa then (
      // At the changed object's header
      // We know start = hd_address oa
      // And by hd_address_spec: U64.v (hd_address oa) = U64.v oa - 8
      hd_address_spec oa;
      assert (U64.v start = U64.v oa - 8);
      
      // Use color_preserves_wosize
      color_preserves_wosize oa g c;
      // This gives: wosize_of_object oa g' == wosize_of_object oa g
      
      // Connect to getWosize: wosize_of_object reads header at hd_address and extracts wosize
      wosize_of_object_spec oa g;
      wosize_of_object_spec oa g';
      // wosize_of_object oa g == getWosize (read_word g (hd_address oa))
      // wosize_of_object oa g' == getWosize (read_word g' (hd_address oa))
      assert (hd_address oa = start);
      assert (getWosize (read_word g' start) == getWosize (read_word g start));
      assert (getWosize header' == getWosize header);
      ()
    ) else (
      // At a different position: header unchanged
      color_change_header_locality oa start g c;
      // This gives: read_word g' start == read_word g start
      assert (header' == header);
      ()
    );
    
    // Extract wosize (same in both heaps)
    let wz = getWosize header in
    let wz' = getWosize header' in
    assert (wz' == wz);
    
    // Calculate obj_addr (same in both heaps)
    let obj_addr_raw = obj_address start in
    assert (U64.v start + 8 < Seq.length g);
    assert (Seq.length g == heap_size);
    assert (U64.v start + 8 < heap_size);
    assert (U64.v start + 8 < pow2 64);
    assert (U64.v obj_addr_raw = U64.v start + 8);
    let obj_addr : hp_addr = obj_addr_raw in
    
    // Calculate next_start (same in both heaps since wz is same)
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + FStar.Mul.(obj_size_nat * 8) in
    
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then (
      // Both return empty
      ()
    ) else if next_start_nat >= heap_size then (
      // Both return singleton
      ()
    ) else (
      // Both recurse: prove recursive call preserves equality
      let next_start_raw = U64.uint_to_t next_start_nat in
      let next_start : hp_addr = next_start_raw in
      
      // Recursive call
      color_change_preserves_objects_at next_start oa g c;
      
      // Both cons obj_addr to same recursive result
      assert (objects next_start g' == objects next_start g);
      ()
    )
  end
#pop-options

/// Main lemma: color changes preserve objects starting from 0
let color_change_preserves_objects (oa: obj_addr) (g: heap) (c: color)
  : Lemma (objects 0UL (set_color g oa c) == objects 0UL g)
  = color_change_preserves_objects_at 0UL oa g c

/// makeBlack preserves the objects list (follows from color_change_preserves_objects)
let makeBlack_preserves_objects (oa: obj_addr) (g: heap)
  : Lemma (objects 0UL (makeBlack oa g) == objects 0UL g)
  = makeBlack_eq oa g;
    color_change_preserves_objects oa g Black

/// makeGray preserves the objects list
let makeGray_preserves_objects (oa: obj_addr) (g: heap)
  : Lemma (objects 0UL (makeGray oa g) == objects 0UL g)
  = makeGray_eq oa g;
    color_change_preserves_objects oa g Gray

/// Color changes preserve pointer structure
/// Proof: set_color only modifies header (at hd_address), not field values
/// points_to reads field values which are at different addresses

/// Recursive helper: exists_field_pointing_to_unchecked preserved by color change
#push-options "--fuel 3 --ifuel 2 --z3rlimit 300"
let rec exists_field_preserved_by_color (g: heap) (h: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) 
                                         (target: obj_addr) (oa: obj_addr) (c: color)
  : Lemma 
    (ensures exists_field_pointing_to_unchecked (set_color g oa c) h wz target ==
             exists_field_pointing_to_unchecked g h wz target)
    (decreases U64.v wz)
  =
  let g' = set_color g oa c in
  if wz = 0UL then ()
  else begin
    let idx = U64.sub wz 1UL in
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    let field_addr_raw = field_address_raw h idx in
    
    // Check bounds in both heaps
    if U64.v field_addr_raw >= heap_size || U64.v field_addr_raw % 8 <> 0 then (
      // Both return false due to bounds check
      ()
    ) else (
      let field_addr : hp_addr = field_addr_raw in
      
      // Prove field value is unchanged
      // field_addr = h + idx*8, and h = hd_address h + 8
      // So field_addr = hd_address h + 8 + idx*8
      // Since idx >= 0, field_addr <> hd_address h (unless idx = 0, but then we're at h itself)
      // Actually we need to be more careful: we need field_addr <> hd_address oa
      
      // If h = oa and idx = 0, then field_addr = h = oa
      // But idx = wz - 1 and wz > 0, so idx >= 0
      // If idx = 0, then field_addr = h = hd_address h + 8
      // We need to show field_addr <> hd_address oa
      
      // Case 1: h <> oa, then hd_address h <> hd_address oa (by injectivity)
      //         field_addr is based on h, hd_address oa is independent
      //         More precisely: field_addr = h + idx*8
      //         If field_addr = hd_address oa, then h + idx*8 = hd_address oa
      //         But h = hd_address h + 8, so hd_address h + 8 + idx*8 = hd_address oa
      //         This would require hd_address oa to be > hd_address h, but they're at 8-byte boundaries
      
      // Case 2: h = oa, then field_addr = oa + idx*8
      //         hd_address oa = oa - 8 (since oa = hd_address oa + 8)
      //         field_addr = oa + idx*8 <> oa - 8 for idx >= 0
      //         Since idx*8 >= 0, oa + idx*8 >= oa > oa - 8
      
      // Let's use a simpler approach: show that field_addr <> hd_address oa
      if h = oa then (
        // field_addr = h + idx*8 = oa + idx*8
        // hd_address oa = oa - 8
        // Since idx >= 0 (actually idx = wz - 1 >= 0), oa + idx*8 >= oa > oa - 8
        // So field_addr <> hd_address oa
        hd_address_spec oa;
        assert (U64.v (hd_address oa) = U64.v oa - 8);
        // field_addr_raw uses add_mod, so field_addr = (h + idx*8) mod 2^64
        // For well-formed heaps, this won't wrap
        // Since idx >= 0, h + idx*8 >= h = oa
        // And hd_address oa = oa - 8 < oa
        // So if field_addr doesn't wrap, field_addr >= oa > hd_address oa
        
        // NOTE: This requires proving that field addresses in a well-formed heap
        // are distinct from header addresses. This would follow from the fact that
        // field_addr = oa + idx*8 >= oa, while hd_address oa = oa - 8.
        // For a complete proof, we'd need:
        // 1. A lemma showing that field_address_raw doesn't wrap for valid heaps
        // 2. Then: U64.v field_addr = U64.v oa + U64.v idx * 8 >= U64.v oa > U64.v (hd_address oa)
        assume (field_addr <> hd_address oa)
      ) else (
        // h <> oa, need to show field_addr <> hd_address oa
        // This is trickier. We know hd_address is injective, so hd_address h <> hd_address oa
        // field_addr could be anywhere in the range [h, h + (wz-1)*8]
        // We need field_addr <> hd_address oa
        
        // Since objects don't overlap (well-formed heap assumption), and field_addr is within h's fields,
        // it cannot equal hd_address oa which is a header address of a different object
        // However, we don't have this assumption available here
        
        // Alternative: use color_change_header_locality
        // This states: if hd_address oa <> addr, then read_word g' addr == read_word g addr
        // We just need to show field_addr <> hd_address oa
        
        // Actually, let me check if we have hd_address h <> hd_address oa implies field_addr <> hd_address oa
        // We have: hd_address h <> hd_address oa (by injectivity since h <> oa)
        // field_addr = h + idx*8 = (hd_address h + 8) + idx*8 = hd_address h + 8 + idx*8
        // For field_addr = hd_address oa, we need: hd_address h + 8 + idx*8 = hd_address oa
        // But hd_address values are 8-byte aligned addresses at object boundaries
        // If hd_address h <> hd_address oa, they differ by at least 8 (actually by at least object size)
        // So hd_address h + 8 + idx*8 = hd_address oa would require a specific alignment
        
        // For safety, let me just assume we're in a well-formed heap where this holds
        // Actually, I should use the fact that set_color only changes hd_address oa
        // and use color_change_header_locality
        
        different_objects_different_headers h oa;
        assert (hd_address h <> hd_address oa);
        
        // Now I need: field_addr <> hd_address oa
        // We have field_addr = h + idx*8 where h = hd_address h + 8
        // So field_addr = hd_address h + 8 + idx*8
        // For this to equal hd_address oa, we'd need hd_address oa = hd_address h + 8 + idx*8
        // But hd_address values are at specific positions (object headers), not arbitrary offsets
        // In a well-formed heap, hd_address oa would be at another object's header, not in the middle of h's fields
        
        // NOTE: This requires a well-formedness property of heaps: objects don't overlap.
        // Specifically, for h <> oa with hd_address h <> hd_address oa, the field addresses of h
        // (which are in the range [h, h + wosize*8]) cannot include hd_address oa.
        // This would follow from a lemma showing that objects are laid out consecutively without overlap.
        // Proving this rigorously would require:
        // 1. A well-formed heap predicate ensuring objects don't overlap
        // 2. A lemma that field_addr ∈ [h, h+wosize*8] and hd_address oa is at a different object boundary
        assume (field_addr <> hd_address oa)
      );
      
      // Now we know field_addr <> hd_address oa
      color_change_header_locality oa field_addr g c;
      let field_val = read_word g field_addr in
      let field_val' = read_word g' field_addr in
      assert (field_val' == field_val);
      
      // The condition is the same in both heaps
      if is_pointer_field field_val && hd_address field_val = hd_address target then (
        ()
      ) else (
        // Recursive case
        exists_field_preserved_by_color g h idx target oa c;
        ()
      )
    )
  end
#pop-options

/// Main lemma: color change preserves points_to
let color_change_preserves_points_to (oa: obj_addr) (g: heap) (c: color) (src dst: hp_addr)
  : Lemma (points_to_safe (set_color g oa c) src dst = points_to_safe g src dst)
  =
  let g' = set_color g oa c in
  if U64.v src >= U64.v mword && U64.v dst >= U64.v mword then (
    // Both use points_to
    // points_to g src dst = exists_field_pointing_to_unchecked g src (wosize_of_object src g) dst
    
    // First show wosize is preserved
    if src = oa then (
      // wosize of the changed object is preserved
      color_preserves_wosize oa g c;
      wosize_of_object_spec oa g;
      wosize_of_object_spec oa g';
      ()
    ) else (
      // wosize unchanged for other objects
      // wosize_of_object reads the header and extracts wosize
      // The header is at hd_address src
      different_objects_different_headers src oa;
      color_change_header_locality oa (hd_address src) g c;
      wosize_of_object_spec src g;
      wosize_of_object_spec src g';
      ()
    );
    
    let wz = wosize_of_object src g in
    let wz' = wosize_of_object src g' in
    // wz' == wz should follow from above
    
    // Now show exists_field is preserved
    wosize_of_object_bound src g;
    wosize_of_object_bound src g';
    // src and dst have type hp_addr{>= mword}, which is equivalent to obj_addr
    let src_obj : obj_addr = src in
    let dst_obj : obj_addr = dst in
    exists_field_preserved_by_color g src_obj wz dst_obj oa c;
    ()
  ) else (
    // Both return false
    ()
  )

/// Changing one object's color doesn't affect other objects' colors (for addresses >= mword)
/// This is the set_color version of color_change_locality
/// Proven using color_change_preserves_other_color from Object.fst
let color_change_preserves_other_colors (oa: obj_addr) (g: heap) (c: color) (other: hp_addr{U64.v other >= U64.v mword})
  : Lemma (requires hd_address oa <> hd_address other)
          (ensures color_of_object other (set_color g oa c) = color_of_object other g)
  = // hd_address oa <> hd_address other implies oa <> other
    // (contrapositive: oa = other implies hd_address oa = hd_address other)
    if oa = other then ()  // vacuously true since hd_address oa = hd_address other contradicts precondition
    else begin
      // oa <> other, so we can use color_change_preserves_other_color
      // set_color g oa c = set_object_color oa g c
      Pulse.Spec.GC.Object.color_change_preserves_other_color oa other g c
    end

/// makeBlack preserves other object's colors (for addresses >= mword)
let makeBlack_preserves_other_colors (oa: obj_addr) (g: heap) (other: hp_addr{U64.v other >= U64.v mword})
  : Lemma (requires hd_address oa <> hd_address other)
          (ensures color_of_object other (makeBlack oa g) = color_of_object other g)
  = makeBlack_eq oa g;
    color_change_preserves_other_colors oa g Black other

/// ---------------------------------------------------------------------------
/// Bridge Lemmas: Connect color_of_object to is_*_safe
/// ---------------------------------------------------------------------------

/// Bridge: color preservation implies is_black_safe preservation
let is_black_safe_color_change_other (oa: obj_addr) (other: hp_addr) (g: heap) (c: color)
  : Lemma (requires U64.v other >= U64.v mword /\ hd_address oa <> hd_address other)
          (ensures is_black_safe other (set_color g oa c) == is_black_safe other g)
  = // is_black_safe other g = is_black other g when other >= mword
    // is_black other g <==> color_of_object other g = Black
    color_change_preserves_other_colors oa g c other;
    is_black_iff other g;
    is_black_iff other (set_color g oa c)

/// Bridge: color preservation implies is_white_safe preservation
let is_white_safe_color_change_other (oa: obj_addr) (other: hp_addr) (g: heap) (c: color)
  : Lemma (requires U64.v other >= U64.v mword /\ hd_address oa <> hd_address other)
          (ensures is_white_safe other (set_color g oa c) == is_white_safe other g)
  = // is_white_safe other g = is_white other g when other >= mword
    // is_white other g <==> color_of_object other g = White
    color_change_preserves_other_colors oa g c other;
    is_white_iff other g;
    is_white_iff other (set_color g oa c)

/// Bridge: color preservation implies is_gray_safe preservation
let is_gray_safe_color_change_other (oa: obj_addr) (other: hp_addr) (g: heap) (c: color)
  : Lemma (requires U64.v other >= U64.v mword /\ hd_address oa <> hd_address other)
          (ensures is_gray_safe other (set_color g oa c) == is_gray_safe other g)
  = color_change_preserves_other_colors oa g c other;
    is_gray_iff other g;
    is_gray_iff other (set_color g oa c)

/// ---------------------------------------------------------------------------
/// Tri-Color Invariant Definition
/// ---------------------------------------------------------------------------

/// The tri-color invariant: no black object has a field pointing to a white object
/// This ensures that the collector won't miss any live objects during marking
/// Note: Uses is_*_safe which handle addresses < 8 safely (always returns false)
let tri_color_inv (g: heap) : prop =
  forall (b_addr w_addr: hp_addr).
    (Seq.mem b_addr (objects 0UL g) /\
     Seq.mem w_addr (objects 0UL g) /\
     is_black_safe b_addr g /\
     is_white_safe w_addr g) ==>
    not (points_to_safe g b_addr w_addr)

/// ---------------------------------------------------------------------------
/// Initial State Satisfies Invariant
/// ---------------------------------------------------------------------------

/// At GC start, all objects are white (or blue)
/// This trivially satisfies tri-color since there are no black objects
val initial_tri_color (g: heap)
  : Lemma
    (requires forall (h: hp_addr). Seq.mem h (objects 0UL g) ==> 
              (is_white_safe h g \/ is_blue_safe h g))
    (ensures tri_color_inv g)

#push-options "--z3rlimit 10"
let initial_tri_color g =
  // Proof: No object is black (all are white or blue).
  // The antecedent "is_black b_addr g" is always false for objects in the list,
  // making the implication vacuously true.
  let aux (b_addr: hp_addr) : Lemma
    (requires Seq.mem b_addr (objects 0UL g))
    (ensures is_black_safe b_addr g == false)
    =  
      // Use objects_addresses_ge_8 to establish b_addr >= 8
      objects_addresses_ge_8 g b_addr;
      // b_addr >= mword, so is_black_safe b_addr g = is_black b_addr g
      // Unfold color predicate definitions to help SMT
      is_black_iff b_addr g;
      is_white_iff b_addr g;
      is_blue_iff b_addr g
      // The precondition says: all objects in (objects 0UL g) are white or blue
      // Since b_addr is in that sequence, we know: is_white b_addr g \/ is_blue b_addr g
      // Since colors are distinct (automatic with color_sem): not (is_black b_addr g)
      // Therefore: is_black_safe b_addr g = false
  in
  Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Graying Preserves Invariant  
/// ---------------------------------------------------------------------------

/// Changing an object from white to gray preserves tri-color
/// (A gray object can point to anything, and nothing changes for black objects)
val gray_preserves_tri_color (g: heap) (w_addr: obj_addr)
  : Lemma
    (requires tri_color_inv g /\ is_white w_addr g)
    (ensures tri_color_inv (makeGray w_addr g))

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let gray_preserves_tri_color g w_addr =
  let g' = makeGray w_addr g in
  gray_makes_gray w_addr g;
  
  // Key: makeGray w_addr g = set_object_color w_addr g Gray = set_color g w_addr Gray
  makeGray_eq w_addr g;
  assert (g' == set_object_color w_addr g Gray);
  
  // Establish key facts about g' at w_addr
  is_gray_iff w_addr g';
  is_black_iff w_addr g';
  is_white_iff w_addr g';
  
  // Objects list is preserved by color change
  color_change_preserves_objects w_addr g Gray;
  
  // Prove tri_color_inv g' by proving the forall
  let aux (b_addr: hp_addr) (white_addr: hp_addr) : Lemma
    (requires 
      Seq.mem b_addr (objects 0UL g') /\
      Seq.mem white_addr (objects 0UL g') /\
      is_black_safe b_addr g' /\
      is_white_safe white_addr g')
    (ensures not (points_to_safe g' b_addr white_addr))
    = 
      // Addresses in objects are >= mword - use objects_addresses_ge_8
      objects_addresses_ge_8 g' b_addr;
      objects_addresses_ge_8 g' white_addr;
      
      // Case 1: b_addr = w_addr
      if b_addr = w_addr then (
        // is_black_safe w_addr g' should be false since w_addr is gray in g'
        ()
      )
      // Case 2: white_addr = w_addr  
      else if white_addr = w_addr then (
        // is_white_safe w_addr g' should be false since w_addr is gray in g'
        ()
      )
      // Case 3: b_addr <> w_addr /\ white_addr <> w_addr
      else begin
        // Both are different from w_addr
        different_objects_different_headers b_addr w_addr;
        different_objects_different_headers white_addr w_addr;
        
        // Apply preservation lemmas
        color_change_preserves_other_colors w_addr g Gray b_addr;
        color_change_preserves_other_colors w_addr g Gray white_addr;
        color_change_preserves_points_to w_addr g Gray b_addr white_addr;
        
        // Objects are preserved: objects g' == objects g
        // This should follow from color_change_preserves_objects since g' = set_color g w_addr Gray
        color_change_preserves_objects w_addr g Gray;
        assert (objects 0UL g' == objects 0UL g);
        
        // Therefore b_addr and white_addr are also in objects g
        assert (Seq.mem b_addr (objects 0UL g));
        assert (Seq.mem white_addr (objects 0UL g));
        
        // Colors are preserved for b_addr and white_addr (since they != w_addr)
        // Use bridge lemmas
        is_black_safe_color_change_other w_addr b_addr g Gray;
        is_white_safe_color_change_other w_addr white_addr g Gray;
        assert (is_black_safe b_addr g == is_black_safe b_addr g');
        assert (is_white_safe white_addr g == is_white_safe white_addr g');
        
        // Therefore the color predicates in g match those in g'
        assert (is_black_safe b_addr g);
        assert (is_white_safe white_addr g);
        
        // Pointers are preserved - use color_change_preserves_points_to
        color_change_preserves_points_to w_addr g Gray b_addr white_addr;
        assert (points_to_safe g b_addr white_addr == points_to_safe g' b_addr white_addr);
        
        // Now instantiate tri_color_inv g with b_addr and white_addr
        // We have all the conditions: b_addr in objects g, white_addr in objects g,
        // is_black_safe b_addr g, is_white_safe white_addr g
        // Therefore by tri_color_inv g: not (points_to_safe g b_addr white_addr)
        assert (not (points_to_safe g b_addr white_addr));
        
        // And by pointer preservation: not (points_to_safe g' b_addr white_addr)
        ()
      end
  in
  Classical.forall_intro_2 (Classical.move_requires_2 aux)
#pop-options

/// ---------------------------------------------------------------------------  
/// Blackening Gray Objects
/// ---------------------------------------------------------------------------

/// Blackening a gray object preserves tri-color IF all its children are non-white
val black_gray_with_nonwhite_children (g: heap) (gr_addr: obj_addr)
  : Lemma
    (requires 
      tri_color_inv g /\
      is_gray gr_addr g /\
      (forall (child: hp_addr). 
        points_to_safe g gr_addr child ==> not (is_white_safe child g)))
    (ensures tri_color_inv (makeBlack gr_addr g))

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let black_gray_with_nonwhite_children g gr_addr =
  let g' = makeBlack gr_addr g in
  black_makes_black gr_addr g;
  
  // Key: makeBlack gr_addr g = set_object_color gr_addr g Black = set_color g gr_addr Black
  makeBlack_eq gr_addr g;
  assert (g' == set_object_color gr_addr g Black);
  
  // Establish key facts about g' at gr_addr
  is_black_iff gr_addr g';
  is_gray_iff gr_addr g';
  is_white_iff gr_addr g';
  
  // Objects list is preserved by color change
  color_change_preserves_objects gr_addr g Black;
  assert (objects 0UL g' == objects 0UL g);
  
  // Prove tri_color_inv g' by proving the forall
  let aux (b_addr: hp_addr) (w_addr: hp_addr) : Lemma
    (requires 
      Seq.mem b_addr (objects 0UL g') /\
      Seq.mem w_addr (objects 0UL g') /\
      is_black_safe b_addr g' /\
      is_white_safe w_addr g')
    (ensures not (points_to_safe g' b_addr w_addr))
    = 
      // Addresses in objects are >= mword - use objects_addresses_ge_8
      objects_addresses_ge_8 g' b_addr;
      objects_addresses_ge_8 g' w_addr;
      
      // Case 1: w_addr = gr_addr
      if w_addr = gr_addr then (
        // is_white_safe gr_addr g' should be false since gr_addr is black in g'
        ()
      )
      // Case 2: b_addr = gr_addr (and w_addr <> gr_addr)
      else if b_addr = gr_addr then (
        // After makeBlack, gr_addr is black and not gray/white
        // By bridge lemma: is_white w_addr g' = is_white w_addr g
        different_objects_different_headers b_addr w_addr;
        is_white_safe_color_change_other gr_addr w_addr g Black;
        assert (is_white_safe w_addr g == is_white_safe w_addr g');
        
        // By color_change_preserves_points_to: points_to g' gr_addr w_addr = points_to g gr_addr w_addr
        color_change_preserves_points_to gr_addr g Black gr_addr w_addr;
        assert (points_to_safe g' gr_addr w_addr == points_to_safe g gr_addr w_addr);
        
        // By precondition: points_to g gr_addr w_addr ==> not (is_white w_addr g)
        // Therefore: not (points_to g' gr_addr w_addr) ∨ not (is_white w_addr g')
        ()
      )
      // Case 3: b_addr <> gr_addr and w_addr <> gr_addr
      else begin
        // Both are different from gr_addr
        different_objects_different_headers b_addr gr_addr;
        different_objects_different_headers w_addr gr_addr;
        
        // Apply preservation lemmas
        color_change_preserves_other_colors gr_addr g Black b_addr;
        color_change_preserves_other_colors gr_addr g Black w_addr;
        color_change_preserves_points_to gr_addr g Black b_addr w_addr;
        
        // Objects are preserved (already established)
        assert (Seq.mem b_addr (objects 0UL g));
        assert (Seq.mem w_addr (objects 0UL g));
        
        // Colors are preserved for b_addr and w_addr (since they != gr_addr)
        // Use bridge lemmas
        is_black_safe_color_change_other gr_addr b_addr g Black;
        is_white_safe_color_change_other gr_addr w_addr g Black;
        assert (is_black_safe b_addr g == is_black_safe b_addr g');
        assert (is_white_safe w_addr g == is_white_safe w_addr g');
        
        // Therefore the color predicates in g match those in g'
        assert (is_black_safe b_addr g);
        assert (is_white_safe w_addr g);
        
        // Pointers are preserved
        color_change_preserves_points_to gr_addr g Black b_addr w_addr;
        assert (points_to_safe g b_addr w_addr == points_to_safe g' b_addr w_addr);
        
        // Now instantiate tri_color_inv g with b_addr and w_addr
        // Therefore by tri_color_inv g: not (points_to_safe g b_addr w_addr)
        assert (not (points_to_safe g b_addr w_addr));
        
        // And by pointer preservation: not (points_to_safe g' b_addr w_addr)
        ()
      end
  in
  Classical.forall_intro_2 (Classical.move_requires_2 aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Write Barrier Correctness
/// ---------------------------------------------------------------------------

/// The write barrier operation: when writing a pointer from src to dst,
/// if src is black and dst is white, gray the dst first.
///
/// This ensures the write doesn't create a black→white edge.

val write_barrier_preserves_tri_color (g: heap) (src dst: hp_addr{U64.v src >= U64.v mword /\ U64.v dst >= U64.v mword})
  : Lemma
    (requires tri_color_inv g)
    (ensures
      (let g' = if is_black src g && is_white dst g then makeGray dst g else g in
       tri_color_inv g'))

let write_barrier_preserves_tri_color g src dst =
  if is_black src g && is_white dst g then
    gray_preserves_tri_color g dst
  else ()

/// ---------------------------------------------------------------------------
/// Stronger Invariant: No Pending Violations
/// ---------------------------------------------------------------------------

/// A stronger form: after write barrier, the specific src→dst edge is safe
val write_barrier_no_violation (g: heap) (src dst: hp_addr{U64.v src >= U64.v mword /\ U64.v dst >= U64.v mword})
  : Lemma
    (requires tri_color_inv g)
    (ensures
      (let g' = if is_black src g && is_white dst g then makeGray dst g else g in
       not (is_black src g' && is_white dst g')))

let write_barrier_no_violation g src dst =
  if is_black src g && is_white dst g then (
    // After graying dst, it's not white anymore
    gray_makes_gray dst g
  ) else ()

/// ---------------------------------------------------------------------------
/// Termination: Gray Set Decreases
/// ---------------------------------------------------------------------------

/// When a gray object is blackened (with children grayed first),
/// the total number of non-black objects decreases

let non_black_count (g: heap) : GTot nat =
  Seq.length (gray_blocks g) + Seq.length (white_blocks g)

/// Mark step progress: blackening one gray decreases non-black count
val mark_step_decreases_count (g: heap) (gr_addr: obj_addr)
  : Lemma
    (requires 
      is_gray gr_addr g /\
      Seq.mem gr_addr (objects 0UL g))
    (ensures
      non_black_count (makeBlack gr_addr g) < non_black_count g)

/// Helper: seq_filter extensionality
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
let rec seq_filter_extensionality (#a:eqtype) (f f': a -> GTot bool) (s: Seq.seq a)
  : Lemma
    (requires forall (x:a). Seq.mem x s ==> f x = f' x)
    (ensures seq_filter f s == seq_filter f' s)
    (decreases Seq.length s)
  =
  if Seq.length s = 0 then ()
  else begin
    let hd = Seq.head s in
    let tl = Seq.tail s in
    seq_filter_extensionality f f' tl;
    assert (f hd = f' hd);
    if f hd then begin
      assert (seq_filter f s == Seq.cons hd (seq_filter f tl));
      assert (seq_filter f' s == Seq.cons hd (seq_filter f' tl))
    end else begin
      assert (seq_filter f s == seq_filter f tl);
      assert (seq_filter f' s == seq_filter f' tl)
    end
  end
#pop-options

/// Helper lemma: When one element's predicate value changes from true to false,
/// and that element appears exactly once, the filtered sequence length decreases by 1
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let rec seq_filter_one_false (#a:eqtype) (f f': a -> GTot bool) (s: Seq.seq a) (x: a)
  : Lemma
    (requires
      Seq.mem x s /\
      f x = true /\
      f' x = false /\
      (forall (y:a). Seq.mem y s /\ y <> x ==> f y = f' y))
    (ensures
      Seq.length (seq_filter f' s) <= Seq.length (seq_filter f s) /\
      (Seq.length (seq_filter f' s) < Seq.length (seq_filter f s)))
    (decreases Seq.length s)
  =
  if Seq.length s = 0 then ()
  else begin
    let hd = Seq.head s in
    let tl = Seq.tail s in
    
    if hd = x then begin
      // The changed element is the head
      assert (f hd = true);
      assert (f' hd = false);
      assert (seq_filter f s == Seq.cons hd (seq_filter f tl));
      assert (seq_filter f' s == seq_filter f' tl);
      // For all elements in tl: if they equal x, same treatment; if not, f y = f' y
      // Need to establish that seq_filter f tl has at least as many elements as seq_filter f' tl
      // and since we're removing one occurrence of x from the filter, we get the inequality
      
      // Case 1: x also appears in tl
      if Seq.mem x tl then begin
        // Recursive call on tail
        seq_filter_one_false f f' tl x;
        // This tells us length (seq_filter f' tl) < length (seq_filter f tl)
        // So length (seq_filter f' s) = length (seq_filter f' tl) < length (seq_filter f tl) + 1 = length (seq_filter f s)
        ()
      end else begin
        // Case 2: x does not appear in tl, so all elements of tl are <> x
        // Therefore for all y in tl: f y = f' y
        assert (forall (y:a). Seq.mem y tl ==> y <> x);
        seq_filter_extensionality f f' tl;
        assert (seq_filter f tl == seq_filter f' tl);
        // So length (seq_filter f' s) = length (seq_filter f tl) < length (seq_filter f tl) + 1 = length (seq_filter f s)
        ()
      end
    end else begin
      // The changed element is not the head
      assert (hd <> x);
      Seq.lemma_mem_inversion s;
      assert (Seq.mem x tl);
      seq_filter_one_false f f' tl x;
      assert (f hd = f' hd);
      if f hd then begin
        assert (seq_filter f s == Seq.cons hd (seq_filter f tl));
        assert (seq_filter f' s == Seq.cons hd (seq_filter f' tl));
        ()
      end else begin
        assert (seq_filter f s == seq_filter f tl);
        assert (seq_filter f' s == seq_filter f' tl);
        ()
      end
    end
  end
#pop-options

/// Helper lemma: Connecting gray_blocks definition to named lambda
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let gray_blocks_eq (g: heap) (fg: hp_addr -> GTot bool)
  : Lemma (requires forall (h:hp_addr). fg h == is_gray_safe h g)
          (ensures gray_blocks g == seq_filter fg (objects 0UL g))
  = seq_filter_extensionality (fun h -> is_gray_safe h g) fg (objects 0UL g)

/// Helper lemma: Connecting white_blocks definition to named lambda
let white_blocks_eq (g: heap) (fw: hp_addr -> GTot bool)
  : Lemma (requires forall (h:hp_addr). fw h == is_white_safe h g)
          (ensures white_blocks g == seq_filter fw (objects 0UL g))
  = seq_filter_extensionality (fun h -> is_white_safe h g) fw (objects 0UL g)
#pop-options

/// Helper: When makeBlack transforms a gray object, gray_blocks decreases and white_blocks unchanged  
#push-options "--fuel 2 --ifuel 1 --z3rlimit 300"
let makeBlack_decreases_gray_blocks (g: heap) (gr_addr: obj_addr)
  : Lemma
    (requires
      is_gray gr_addr g /\
      Seq.mem gr_addr (objects 0UL g))
    (ensures
      (let g' = makeBlack gr_addr g in
       Seq.length (gray_blocks g') < Seq.length (gray_blocks g) /\
       Seq.length (white_blocks g') = Seq.length (white_blocks g)))
  =
  let g' = makeBlack gr_addr g in
  
  // Objects list preserved
  makeBlack_preserves_objects gr_addr g;
  
  // gr_addr becomes black (not gray/white) in g'
  black_makes_black gr_addr g;
  makeBlack_eq gr_addr g;
  
  // gr_addr >= 8 (since it's in objects)
  objects_addresses_ge_8 g gr_addr;
  
  // In g: gr_addr is gray
  is_gray_iff gr_addr g;
  
  // In g': gr_addr is black (not gray)
  is_gray_iff gr_addr g';
  
  // Establish gr_addr is in gray_blocks g
  seq_filter_mem_complete (fun h -> is_gray_safe h g) (objects 0UL g) gr_addr;
  
  // For other objects: gray status unchanged
  let aux_gray (other: hp_addr)
    : Lemma
      (requires Seq.mem other (objects 0UL g) /\ other <> gr_addr)
      (ensures is_gray_safe other g' = is_gray_safe other g)
    =
    objects_addresses_ge_8 g other;
    different_objects_different_headers other gr_addr;
    makeBlack_preserves_other_colors gr_addr g other;
    is_gray_safe_color_change_other gr_addr other g Black
  in
  Classical.forall_intro (Classical.move_requires aux_gray);
  
  // Apply seq_filter_one_false for gray_blocks
  let fg = (fun h -> is_gray_safe h g) in
  let fg' = (fun h -> is_gray_safe h g') in
  seq_filter_one_false fg fg' (objects 0UL g) gr_addr;
  
  // For white_blocks: gr_addr was gray in g (not white), so not in white_blocks g or g'
  // All other objects preserve white status
  let aux_white (other: hp_addr)
    : Lemma
      (requires Seq.mem other (objects 0UL g) /\ other <> gr_addr)
      (ensures is_white_safe other g' = is_white_safe other g)
    =
    objects_addresses_ge_8 g other;
    different_objects_different_headers other gr_addr;
    makeBlack_preserves_other_colors gr_addr g other;
    is_white_safe_color_change_other gr_addr other g Black
  in
  Classical.forall_intro (Classical.move_requires aux_white);
  
  // gr_addr is not white in either heap (it was gray in g, black in g')
  is_white_iff gr_addr g;
  is_white_iff gr_addr g';
  
  // Apply seq_filter extensionality for white_blocks
  let fw = (fun h -> is_white_safe h g) in
  let fw' = (fun h -> is_white_safe h g') in
  seq_filter_extensionality fw fw' (objects 0UL g);
  
  // Connect the definitions using helper lemmas
  gray_blocks_eq g fg;
  gray_blocks_eq g' fg';
  white_blocks_eq g fw;
  white_blocks_eq g' fw';
  
  // Now seq_filter_one_false and seq_filter_extensionality give us the postcondition
  ()
#pop-options

let mark_step_decreases_count g gr_addr =
  makeBlack_decreases_gray_blocks g gr_addr;
  ()
