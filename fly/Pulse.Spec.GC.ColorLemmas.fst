/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.ColorLemmas - Raw Color Change Preservation for 4-Color GC
/// ---------------------------------------------------------------------------
///
/// Defines `set_object_color_raw` using Header.set_color64 which works with
/// raw U64 color values (0-3), enabling blue (3) transitions that the standard
/// `set_object_color` (which takes `color_sem` = White|Gray|Black) cannot express.
///
/// Proves that `set_object_color_raw` preserves `well_formed_heap`.
///
/// All helper lemmas from common/ (write_word locality, setColor64 preservation)
/// are assembled here to avoid modifying common/.

module Pulse.Spec.GC.ColorLemmas

open FStar.Seq
open FStar.Classical
open FStar.Mul
module U64 = FStar.UInt64
module ML = FStar.Math.Lemmas

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Fields
module Header = Pulse.Lib.Header

/// ===========================================================================
/// Section 1: set_object_color_raw Definition
/// ===========================================================================

/// Set the color bits of an object's header to a raw U64 value (0-3).
/// Unlike set_object_color which takes color_sem (White|Gray|Black),
/// this handles all 4 colors including Blue (3).
let set_object_color_raw (obj: obj_addr) (g: heap) (c: U64.t{U64.v c < 4}) : GTot heap =
  let hd_addr = hd_address obj in
  let old_header = read_word g hd_addr in
  let new_header = Header.set_color64 old_header c in
  write_word g hd_addr new_header

/// ===========================================================================
/// Section 2: Basic Properties
/// ===========================================================================

/// Length preserved
let set_object_color_raw_length (obj: obj_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (Seq.length (set_object_color_raw obj g c) == Seq.length g)
  = ()

/// Wosize at the modified header is preserved
/// Bridge: Header.setColor64_preserves_wosize works at nat level (get_wosize),
/// we need U64 level (getWosize). Prove the bridge explicitly.
private let getWosize_nat_bridge (hdr: U64.t)
  : Lemma (U64.v (getWosize hdr) == Header.get_wosize (U64.v hdr))
  = getWosize_spec hdr;
    // getWosize hdr == U64.shift_right hdr 10ul
    // U64.v (U64.shift_right hdr 10ul) = UInt.shift_right (U64.v hdr) 10 = U64.v hdr / pow2 10
    // Header.get_wosize n = n / pow2 10
    ()

let setColor64_preserves_getWosize (hdr: U64.t) (c: U64.t{U64.v c < 4})
  : Lemma (getWosize (Header.set_color64 hdr c) == getWosize hdr)
  = Header.setColor64_preserves_wosize hdr c;
    // Nat level: get_wosize (U64.v (set_color64 hdr c)) == get_wosize (U64.v hdr)
    getWosize_nat_bridge hdr;
    getWosize_nat_bridge (Header.set_color64 hdr c);
    // Now: U64.v (getWosize hdr) == get_wosize (U64.v hdr)
    //      U64.v (getWosize (set_color64 hdr c)) == get_wosize (U64.v (set_color64 hdr c))
    // Combined: U64.v (getWosize (set_color64 hdr c)) == U64.v (getWosize hdr)
    U64.v_inj (getWosize (Header.set_color64 hdr c)) (getWosize hdr)

let set_object_color_raw_preserves_getWosize_at_hd (obj: obj_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (getWosize (read_word (set_object_color_raw obj g c) (hd_address obj)) ==
           getWosize (read_word g (hd_address obj)))
  = let hd = hd_address obj in
    let old_hdr = read_word g hd in
    let new_hdr = Header.set_color64 old_hdr c in
    read_write_same g hd new_hdr;
    setColor64_preserves_getWosize old_hdr c

/// Two distinct word-aligned addresses don't overlap (local copy of private helper from common/)
private let word_aligned_separate_local (a b: hp_addr)
  : Lemma (requires a <> b)
          (ensures U64.v a + 8 <= U64.v b \/ U64.v b + 8 <= U64.v a)
  = let va = U64.v a in
    let vb = U64.v b in
    let eight : pos = 8 in
    ML.lemma_mod_sub_distr vb va eight;
    ML.lemma_mod_sub_distr va vb eight;
    if vb > va then (
      if vb - va < 8 then ML.small_mod (vb - va) eight
    ) else (
      if va - vb < 8 then ML.small_mod (va - vb) eight
    )

/// Read at a different address is unchanged (only needs <>, derives non-overlap internally)
let set_object_color_raw_read_other (obj: obj_addr) (addr: hp_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (requires hd_address obj <> addr)
          (ensures read_word (set_object_color_raw obj g c) addr == read_word g addr)
  = let hd = hd_address obj in
    let new_hdr = Header.set_color64 (read_word g hd) c in
    word_aligned_separate_local hd addr;
    read_write_different g hd addr new_hdr

/// Combined: read_word at any address either returns preserved wosize or unchanged value
let set_object_color_raw_read_word (obj: obj_addr) (start: hp_addr) (g: heap) (c: U64.t{U64.v c < 4})
  : Lemma (ensures
    Seq.length (set_object_color_raw obj g c) == Seq.length g /\
    (hd_address obj <> start ==>
      read_word (set_object_color_raw obj g c) start == read_word g start) /\
    (hd_address obj = start ==>
      getWosize (read_word (set_object_color_raw obj g c) start) ==
      getWosize (read_word g start)))
  [SMTPat (read_word (set_object_color_raw obj g c) start)]
  = set_object_color_raw_length obj g c;
    if hd_address obj = start then
      set_object_color_raw_preserves_getWosize_at_hd obj g c
    else
      set_object_color_raw_read_other obj start g c

/// ===========================================================================
/// Section 3: Objects Enumeration Preservation
/// ===========================================================================

/// Header at any position: either it's the modified object (wosize preserved)
/// or it's at a different address (value unchanged).
/// This is the key insight for objects preservation.
private let header_at_preserved (obj: obj_addr) (g: heap) (c: U64.t{U64.v c < 4}) (start: hp_addr)
  : Lemma (ensures getWosize (read_word (set_object_color_raw obj g c) start) ==
                   getWosize (read_word g start))
  = if hd_address obj = start then
      set_object_color_raw_preserves_getWosize_at_hd obj g c
    else
      set_object_color_raw_read_other obj start g c

/// Objects enumeration is preserved by raw color change
#push-options "--z3rlimit 400 --fuel 4 --ifuel 2"
val raw_color_change_preserves_objects_aux : (start: hp_addr) -> (g: heap) -> (obj: obj_addr) -> (c: U64.t{U64.v c < 4}) ->
  Lemma (ensures objects start (set_object_color_raw obj g c) == objects start g)
        (decreases (Seq.length g - U64.v start))

let rec raw_color_change_preserves_objects_aux start g obj c =
  set_object_color_raw_length obj g c;
  if U64.v start + 8 >= Seq.length g then ()
  else begin
    header_at_preserved obj g c start;
    let wz = getWosize (read_word g start) in
    let next_start_nat = U64.v start + (U64.v wz + 1) * 8 in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else if next_start_nat >= heap_size then ()
    else
      raw_color_change_preserves_objects_aux (U64.uint_to_t next_start_nat) g obj c
  end
#pop-options

let raw_color_change_preserves_objects (g: heap) (obj: obj_addr) (c: U64.t{U64.v c < 4})
  : Lemma (objects 0UL (set_object_color_raw obj g c) == objects 0UL g)
  = raw_color_change_preserves_objects_aux 0UL g obj c

let raw_color_change_preserves_objects_mem (g: heap) (obj: obj_addr) (c: U64.t{U64.v c < 4}) (x: obj_addr)
  : Lemma (Seq.mem x (objects 0UL (set_object_color_raw obj g c)) <==> Seq.mem x (objects 0UL g))
  = raw_color_change_preserves_objects g obj c

/// ===========================================================================
/// Section 4: Field Address / Header Address Separation
/// ===========================================================================

/// Field address of object h at index idx: h + idx * 8
/// Since h >= 8 (obj_addr) and hd_address h = h - 8, we have:
///   field_addr = h + idx*8 >= h >= h - 8 + 8 = hd_address h + 8
/// So field_addr >= hd_address h + 8, meaning they don't overlap.

/// Inline version of field_offset_bound (private in common/)
private let field_offset_bound_local (field_idx: U64.t{U64.v field_idx < pow2 61}) : Lemma
  (FStar.UInt.size (U64.v field_idx * 8) 64)
  = ML.pow2_plus 61 3;
    assert (pow2 61 * pow2 3 == pow2 64);
    assert (U64.v field_idx * 8 < pow2 64)

/// Inline version of field_addr_raw_value (private in common/)
private let field_addr_raw_value_local (h: obj_addr) (idx: U64.t{U64.v idx < pow2 61})
  : Lemma (U64.v (field_address_raw h idx) = (U64.v h + U64.v idx * 8) % pow2 64)
  = field_offset_bound_local idx

/// Self case: computed field address of h is not at hd_address h.
/// Takes the computed address directly to avoid field_address_raw subtyping issue.
private let field_addr_ne_hd_self (h: obj_addr) (far: hp_addr) (idx_val: nat{idx_val < pow2 54})
  : Lemma (requires U64.v far = (U64.v h + idx_val * 8) % pow2 64)
          (ensures far <> hd_address h)
  = hd_address_spec h;
    // far = (h + idx*8) % 2^64, hd h = h - 8
    // If equal: (h + idx*8) % 2^64 = h - 8
    // No overflow: h + idx*8 = h - 8 => idx*8 = -8, impossible for idx >= 0
    // Overflow: h + idx*8 - 2^64 = h - 8 => idx*8 = 2^64 - 8
    //   But idx < pow2 54, so idx*8 < pow2 54 * 8 = pow2 57
    //   And pow2 57 < pow2 64 - 8 (since pow2 57 < pow2 64 / 128 and 8 < pow2 64 * 127/128)
    if U64.v h + idx_val * 8 < pow2 64 then ()
    else begin
      assert_norm (pow2 54 * 8 = pow2 57);
      assert (idx_val * 8 < pow2 57);
      assert_norm (pow2 57 < pow2 64 - 8)
    end

/// ===========================================================================
/// Section 5: Field Pointing Preservation (Self Case)
/// ===========================================================================

/// Changing the color of object h preserves exists_field_pointing_to_unchecked
/// when checking fields of h itself.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec raw_color_change_preserves_field_pointing_self
  (g: heap) (h: obj_addr) (c: U64.t{U64.v c < 4})
  (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr)
  : Lemma (ensures exists_field_pointing_to_unchecked (set_object_color_raw h g c) h wz target
                   == exists_field_pointing_to_unchecked g h wz target)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      assert_norm (pow2 54 < pow2 61);
      field_offset_bound_local idx;
      ML.modulo_lemma (U64.v idx * U64.v mword) (pow2 64);
      let far = U64.add_mod h (U64.mul_mod idx mword) in
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then
        raw_color_change_preserves_field_pointing_self g h c idx target
      else begin
        let field_addr : hp_addr = far in
        // Prove far = (h + idx*8) % pow2 64 for field_addr_ne_hd_self
        field_addr_ne_hd_self h field_addr (U64.v idx);
        set_object_color_raw_read_other h field_addr g c;
        raw_color_change_preserves_field_pointing_self g h c idx target
      end
    end
#pop-options

/// ===========================================================================
/// Section 6: Field Pointing Preservation (Other Case)
/// ===========================================================================

/// Cross-object case: computed field address of src is not at hd_address of obj.
/// Takes the computed address directly to avoid field_address_raw subtyping issue.
#push-options "--z3rlimit 1000"
private let field_addr_ne_hd_cross (g: heap) (src: obj_addr) (obj: obj_addr)
  (far: hp_addr) (idx_val: nat{idx_val < pow2 54})
  : Lemma (requires src <> obj /\
                    Seq.mem src (objects 0UL g) /\ Seq.mem obj (objects 0UL g) /\
                    well_formed_heap g /\
                    idx_val < U64.v (wosize_of_object_as_wosize src g) /\
                    U64.v far = (U64.v src + idx_val * 8) % pow2 64)
          (ensures far <> hd_address obj)
  = hd_address_spec obj;
    let ws = U64.v (wosize_of_object_as_wosize src g) in
    wf_object_bound g src;
    assert (U64.v src + op_Multiply ws 8 <= heap_size);
    let sum = U64.v src + idx_val * 8 in
    assert_norm (pow2 54 * 8 = pow2 57);
    assert (idx_val * 8 < pow2 57);
    assert (sum <= heap_size);
    ML.small_mod sum (pow2 64);
    if U64.v src > U64.v obj then ()
    else begin
      objects_separated 0UL g src obj;
      ()
    end
#pop-options

/// Changing the color of obj preserves exists_field_pointing_to_unchecked
/// when checking fields of a different object src.
#push-options "--z3rlimit 200 --fuel 2 --ifuel 1"
let rec raw_color_change_preserves_field_pointing_other
  (g: heap) (obj: obj_addr) (c: U64.t{U64.v c < 4})
  (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54}) (target: hp_addr)
  : Lemma (requires src <> obj /\
                    Seq.mem src (objects 0UL g) /\
                    Seq.mem obj (objects 0UL g) /\
                    well_formed_heap g /\
                    U64.v wz <= U64.v (wosize_of_object_as_wosize src g))
          (ensures exists_field_pointing_to_unchecked (set_object_color_raw obj g c) src wz target
                   == exists_field_pointing_to_unchecked g src wz target)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      assert_norm (pow2 54 < pow2 61);
      field_offset_bound_local idx;
      ML.modulo_lemma (U64.v idx * U64.v mword) (pow2 64);
      let far = U64.add_mod src (U64.mul_mod idx mword) in
      if U64.v far >= heap_size || U64.v far % 8 <> 0 then
        raw_color_change_preserves_field_pointing_other g obj c src idx target
      else begin
        let field_addr : hp_addr = far in
        field_addr_ne_hd_cross g src obj field_addr (U64.v idx);
        set_object_color_raw_read_other obj field_addr g c;
        raw_color_change_preserves_field_pointing_other g obj c src idx target
      end
    end
#pop-options

/// ===========================================================================
/// Section 7: Main Theorem — Raw Color Change Preserves well_formed_heap
/// ===========================================================================

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
val set_object_color_raw_preserves_wf :
  (g: heap) -> (obj: obj_addr) -> (c: U64.t{U64.v c < 4}) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
        (ensures well_formed_heap (set_object_color_raw obj g c))

let set_object_color_raw_preserves_wf g obj c =
  let g' = set_object_color_raw obj g c in
  raw_color_change_preserves_objects g obj c;
  set_object_color_raw_length obj g c;
  // Part 1: object bounds preserved (wosize unchanged + length unchanged)
  let aux1 (h: obj_addr) : Lemma
    (requires Seq.mem h (objects 0UL g))
    (ensures (let wz = wosize_of_object h g' in
              U64.v (hd_address h) + 8 + op_Multiply (U64.v wz) 8 <= Seq.length g'))
  = wf_object_size_bound g h;
    set_object_color_raw_length obj g c;
    wosize_of_object_spec h g;
    wosize_of_object_spec h g';
    if h <> obj then
      hd_address_injective h obj
    else ()
  in
  forall_intro (move_requires aux1);
  // Part 2: pointer targets preserved
  let aux2 (src dst: obj_addr) : Lemma
    (requires Seq.mem src (objects 0UL g') /\
             (let wz = wosize_of_object src g' in
              U64.v wz < pow2 54 /\
              exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem dst (objects 0UL g'))
  = wosize_of_object_spec src g;
    wosize_of_object_spec src g';
    if src = obj then begin
      raw_color_change_preserves_field_pointing_self g obj c (wosize_of_object src g) dst
    end else begin
      hd_address_injective src obj;
      raw_color_change_preserves_field_pointing_other g obj c src (wosize_of_object src g) dst
    end
  in
  let aux2_flat (src: obj_addr) (dst: obj_addr) : Lemma
    (requires Seq.mem src (objects 0UL g') /\
              U64.v (wosize_of_object src g') < pow2 54 /\
              exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst)
    (ensures Seq.mem dst (objects 0UL g'))
  = aux2 src dst
  in
  let aux2_imp (src: obj_addr) (dst: obj_addr) : Lemma
    ((Seq.mem src (objects 0UL g') /\
      U64.v (wosize_of_object src g') < pow2 54 /\
      exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst) ==>
     Seq.mem dst (objects 0UL g'))
  = move_requires (aux2_flat src) dst
  in
  forall_intro_2 aux2_imp
#pop-options

/// ===========================================================================
/// Section 8: Standard Color Changes Preserve well_formed_heap
/// ===========================================================================

/// Since set_object_color is abstract, we can't prove equality with set_object_color_raw.
/// Instead, we prove preservation directly for standard colors using the
/// set_object_color_read_word SMTPat from Object.fsti.

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"
val set_object_color_preserves_wf :
  (g: heap) -> (obj: obj_addr) -> (c: color) ->
  Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
        (ensures well_formed_heap (set_object_color obj g c))

let set_object_color_preserves_wf g obj c =
  let g' = set_object_color obj g c in
  color_change_preserves_objects g obj c;
  set_object_color_length obj g c;
  let aux1 (h: obj_addr) : Lemma
    (requires Seq.mem h (objects 0UL g))
    (ensures (let wz = wosize_of_object h g' in
              U64.v (hd_address h) + 8 + op_Multiply (U64.v wz) 8 <= Seq.length g'))
  = wf_object_size_bound g h;
    set_object_color_length obj g c;
    wosize_of_object_spec h g;
    wosize_of_object_spec h g';
    if h <> obj then
      hd_address_injective h obj
    else ()
  in
  forall_intro (move_requires aux1);
  let aux2 (src dst: obj_addr) : Lemma
    (requires Seq.mem src (objects 0UL g') /\
             (let wz = wosize_of_object src g' in
              U64.v wz < pow2 54 /\
              exists_field_pointing_to_unchecked g' src wz dst))
    (ensures Seq.mem dst (objects 0UL g'))
  = wosize_of_object_spec src g;
    wosize_of_object_spec src g';
    if src = obj then begin
      color_change_preserves_field_pointing_self g obj c (wosize_of_object src g) dst
    end else begin
      hd_address_injective src obj;
      color_change_preserves_field_pointing_other g obj c src (wosize_of_object src g) dst
    end
  in
  let aux2_flat (src: obj_addr) (dst: obj_addr) : Lemma
    (requires Seq.mem src (objects 0UL g') /\
              U64.v (wosize_of_object src g') < pow2 54 /\
              exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst)
    (ensures Seq.mem dst (objects 0UL g'))
  = aux2 src dst
  in
  let aux2_imp (src: obj_addr) (dst: obj_addr) : Lemma
    ((Seq.mem src (objects 0UL g') /\
      U64.v (wosize_of_object src g') < pow2 54 /\
      exists_field_pointing_to_unchecked g' src (wosize_of_object src g') dst) ==>
     Seq.mem dst (objects 0UL g'))
  = move_requires (aux2_flat src) dst
  in
  forall_intro_2 aux2_imp
#pop-options

/// Convenience: makeWhite / makeBlack preserve well_formed_heap
let makeWhite_preserves_wf (g: heap) (obj: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
          (ensures well_formed_heap (makeWhite obj g))
  = makeWhite_eq obj g;
    set_object_color_preserves_wf g obj Header.White

let makeBlack_preserves_wf (g: heap) (obj: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
          (ensures well_formed_heap (makeBlack obj g))
  = makeBlack_eq obj g;
    set_object_color_preserves_wf g obj Header.Black

let makeGray_preserves_wf (g: heap) (obj: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem obj (objects 0UL g))
          (ensures well_formed_heap (makeGray obj g))
  = makeGray_eq obj g;
    set_object_color_preserves_wf g obj Header.Gray

/// ===========================================================================
/// Section 9: Objects Preservation and roots_valid / stack_valid
/// ===========================================================================

/// All addresses in a sequence are members of `objects 0UL g`
let seq_addrs_valid (g: heap) (addrs: Seq.seq obj_addr) : prop =
  forall (i: nat). i < Seq.length addrs ==> Seq.mem (Seq.index addrs i) (objects 0UL g)

/// Alias for root sequences
let roots_valid (g: heap) (roots: Seq.seq obj_addr) : prop = seq_addrs_valid g roots

/// Alias for gray stack
let stack_valid (g: heap) (gs: Seq.seq obj_addr) : prop = seq_addrs_valid g gs

/// Predicate: the objects enumeration is identical between two heaps.
/// This is a helper to avoid inlining `objects 0UL g1 == objects 0UL g2` 
/// inside Pulse `pure` propositions (which can cause SMT elaboration issues).
let objects_preserved (g1 g2: heap) : prop =
  objects 0UL g1 == objects 0UL g2

/// Color change preserves objects (wrapped for Pulse)
let objects_preserved_by_color (g: heap) (obj: obj_addr) (c: color)
  : Lemma (requires Seq.mem obj (objects 0UL g))
          (ensures objects_preserved (set_object_color obj g c) g)
  = color_change_preserves_objects g obj c

let objects_preserved_by_raw_color (g: heap) (obj: obj_addr) (c: U64.t{U64.v c < 4})
  : Lemma (requires Seq.mem obj (objects 0UL g))
          (ensures objects_preserved (set_object_color_raw obj g c) g)
  = raw_color_change_preserves_objects g obj c

let objects_preserved_makeGray (g: heap) (obj: obj_addr)
  : Lemma (requires Seq.mem obj (objects 0UL g))
          (ensures objects_preserved (makeGray obj g) g)
  = makeGray_eq obj g;
    color_change_preserves_objects g obj Header.Gray

let objects_preserved_makeBlack (g: heap) (obj: obj_addr)
  : Lemma (requires Seq.mem obj (objects 0UL g))
          (ensures objects_preserved (makeBlack obj g) g)
  = makeBlack_eq obj g;
    color_change_preserves_objects g obj Header.Black

let objects_preserved_makeWhite (g: heap) (obj: obj_addr)
  : Lemma (requires Seq.mem obj (objects 0UL g))
          (ensures objects_preserved (makeWhite obj g) g)
  = makeWhite_eq obj g;
    color_change_preserves_objects g obj Header.White

/// objects_preserved transfers membership
let objects_preserved_mem (g1 g2: heap) (x: obj_addr)
  : Lemma (requires objects_preserved g1 g2)
          (ensures Seq.mem x (objects 0UL g1) == Seq.mem x (objects 0UL g2))
  = ()

/// objects_preserved transfers roots_valid
let objects_preserved_roots_valid (g1 g2: heap) (roots: Seq.seq obj_addr)
  : Lemma (requires objects_preserved g1 g2 /\ roots_valid g2 roots)
          (ensures roots_valid g1 roots)
  = ()

/// Color change preserves seq_addrs_valid (raw version)
#push-options "--z3rlimit 200"
let seq_addrs_valid_preserved_raw (g: heap) (obj: obj_addr) (c: U64.t{U64.v c < 4})
    (addrs: Seq.seq obj_addr)
  : Lemma (requires seq_addrs_valid g addrs /\ Seq.mem obj (objects 0UL g))
          (ensures seq_addrs_valid (set_object_color_raw obj g c) addrs)
  = raw_color_change_preserves_objects g obj c;
    // objects are identical, so membership transfers directly
    assert (objects 0UL (set_object_color_raw obj g c) == objects 0UL g)
#pop-options

/// Color change preserves seq_addrs_valid (standard color version)
#push-options "--z3rlimit 200"
let seq_addrs_valid_preserved (g: heap) (obj: obj_addr) (c: color)
    (addrs: Seq.seq obj_addr)
  : Lemma (requires seq_addrs_valid g addrs /\ Seq.mem obj (objects 0UL g))
          (ensures seq_addrs_valid (set_object_color obj g c) addrs)
  = color_change_preserves_objects g obj c;
    assert (objects 0UL (set_object_color obj g c) == objects 0UL g)
#pop-options

/// Convenience: makeWhite/makeBlack/makeGray preserve roots_valid
let roots_valid_makeWhite (g: heap) (obj: obj_addr) (roots: Seq.seq obj_addr)
  : Lemma (requires roots_valid g roots /\ Seq.mem obj (objects 0UL g))
          (ensures roots_valid (makeWhite obj g) roots)
  = makeWhite_eq obj g;
    seq_addrs_valid_preserved g obj Header.White roots

let roots_valid_makeBlack (g: heap) (obj: obj_addr) (roots: Seq.seq obj_addr)
  : Lemma (requires roots_valid g roots /\ Seq.mem obj (objects 0UL g))
          (ensures roots_valid (makeBlack obj g) roots)
  = makeBlack_eq obj g;
    seq_addrs_valid_preserved g obj Header.Black roots

let roots_valid_makeGray (g: heap) (obj: obj_addr) (roots: Seq.seq obj_addr)
  : Lemma (requires roots_valid g roots /\ Seq.mem obj (objects 0UL g))
          (ensures roots_valid (makeGray obj g) roots)
  = makeGray_eq obj g;
    seq_addrs_valid_preserved g obj Header.Gray roots

let roots_valid_raw (g: heap) (obj: obj_addr) (c: U64.t{U64.v c < 4})
    (roots: Seq.seq obj_addr)
  : Lemma (requires roots_valid g roots /\ Seq.mem obj (objects 0UL g))
          (ensures roots_valid (set_object_color_raw obj g c) roots)
  = seq_addrs_valid_preserved_raw g obj c roots

/// stack_valid is preserved when popping (tail is a subsequence)
let stack_valid_tail (g: heap) (gs: Seq.seq obj_addr)
  : Lemma (requires stack_valid g gs /\ Seq.length gs > 0)
          (ensures stack_valid g (Seq.tail gs))
  = let tl = Seq.tail gs in
    let aux (i: nat{i < Seq.length tl})
      : Lemma (Seq.mem (Seq.index tl i) (objects 0UL g))
      = Seq.lemma_index_slice gs 1 (Seq.length gs) i;
        assert (Seq.index tl i == Seq.index gs (i + 1));
        assert (i + 1 < Seq.length gs)
    in
    Classical.forall_intro aux

/// stack_valid is preserved when pushing a valid element
let stack_valid_cons (g: heap) (x: obj_addr) (gs: Seq.seq obj_addr)
  : Lemma (requires stack_valid g gs /\ Seq.mem x (objects 0UL g))
          (ensures stack_valid g (Seq.cons x gs))
  = let s = Seq.cons x gs in
    let aux (i: nat{i < Seq.length s})
      : Lemma (Seq.mem (Seq.index s i) (objects 0UL g))
      = if i = 0 then (Seq.lemma_index_is_nth s 0; ())
        else begin
          assert (Seq.index s i == Seq.index gs (i - 1));
          assert (i - 1 < Seq.length gs)
        end
    in
    Classical.forall_intro aux

/// stack_valid head element is a member of objects
let stack_valid_head (g: heap) (gs: Seq.seq obj_addr)
  : Lemma (requires stack_valid g gs /\ Seq.length gs > 0)
          (ensures Seq.mem (Seq.index gs 0) (objects 0UL g))
  = ()

/// stack_valid is transferred via objects_preserved
let stack_valid_preserved (g1 g2: heap) (gs: Seq.seq obj_addr)
  : Lemma (requires stack_valid g2 gs /\ objects_preserved g1 g2)
          (ensures stack_valid g1 gs)
  = let aux (i: nat{i < Seq.length gs})
      : Lemma (Seq.mem (Seq.index gs i) (objects 0UL g1))
      = objects_preserved_mem g1 g2 (Seq.index gs i)
    in
    Classical.forall_intro aux

/// stack_valid preserved by makeBlack
let stack_valid_makeBlack (g: heap) (obj: obj_addr) (gs: Seq.seq obj_addr)
  : Lemma (requires stack_valid g gs /\ Seq.mem obj (objects 0UL g))
          (ensures stack_valid (makeBlack obj g) gs)
  = makeBlack_eq obj g;
    seq_addrs_valid_preserved g obj Header.Black gs

/// stack_valid preserved by makeGray
let stack_valid_makeGray (g: heap) (obj: obj_addr) (gs: Seq.seq obj_addr)
  : Lemma (requires stack_valid g gs /\ Seq.mem obj (objects 0UL g))
          (ensures stack_valid (makeGray obj g) gs)
  = makeGray_eq obj g;
    seq_addrs_valid_preserved g obj Header.Gray gs

/// ===========================================================================
/// Section 9b: Color change preserves wosize of ALL objects
/// ===========================================================================

/// set_object_color preserves wosize of any object (same or different from target).
/// For same object: uses color_preserves_wosize.
/// For different object: uses color_change_header_locality + wosize_of_object_spec.
let set_color_preserves_wosize_all (g: heap) (obj parent: obj_addr) (c: color)
  : Lemma (requires Seq.length g == heap_size)
          (ensures wosize_of_object parent (set_object_color obj g c) == wosize_of_object parent g)
  = if obj = parent then
      color_preserves_wosize parent g c
    else begin
      // hd_address is obj - 8, injective for obj_addr (both >= 8)
      hd_address_spec obj;
      hd_address_spec parent;
      assert (hd_address obj <> hd_address parent);
      color_change_header_locality obj (hd_address parent) g c;
      wosize_of_object_spec parent g;
      wosize_of_object_spec parent (set_object_color obj g c);
      ()
    end

/// makeGray preserves wosize of any object
let makeGray_preserves_wosize_all (g: heap) (obj parent: obj_addr)
  : Lemma (requires Seq.mem obj (objects 0UL g) /\ Seq.length g == heap_size)
          (ensures wosize_of_object parent (makeGray obj g) == wosize_of_object parent g)
  = makeGray_eq obj g;
    set_color_preserves_wosize_all g obj parent Header.Gray

/// ===========================================================================
/// Section 9c: Pointer field membership (for check_and_darken)
/// ===========================================================================

/// Key lemma: any pointer-valued field of a known object points to a known object.
/// Wraps field_read_implies_exists_pointing + well_formed_heap part 2.
///
/// Given parent ∈ objects(0, g), field index k < wosize(parent),
/// and read_word g (parent + k*8) is a pointer, then that field value ∈ objects(0, g).
#push-options "--z3rlimit 200"
let pointer_field_in_objects (g: heap) (parent: obj_addr) (k: nat) (field_addr: hp_addr)
  : Lemma (requires well_formed_heap g /\
                    Seq.mem parent (objects 0UL g) /\
                    Seq.length g == heap_size /\
                    k < U64.v (wosize_of_object parent g) /\
                    U64.v field_addr == U64.v parent + k * 8 /\
                    is_pointer_field (read_word g field_addr))
          (ensures Seq.mem (read_word g field_addr) (objects 0UL g))
  = let wz = wosize_of_object parent g in
    let fv = read_word g field_addr in
    // fv is a pointer: U64.v fv >= 8, < heap_size, % 8 == 0
    let target : obj_addr = fv in
    // 1. well_formed_object g parent (from wfh part 1)
    wf_object_size_bound g parent;
    // 2. wosize bound for exists_field_pointing_to_unchecked
    wosize_of_object_bound parent g;
    assert (U64.v wz < pow2 54);
    // 3. Build k as U64 for field_read_implies_exists_pointing
    ML.pow2_lt_compat 61 54;
    let k_u64 : U64.t = FStar.UInt64.uint_to_t k in
    // 4. Show add_mod/mul_mod don't overflow, so far == field_addr
    ML.pow2_plus 54 3;
    ML.pow2_lt_compat 64 57;
    FStar.Math.Lemmas.modulo_lemma (k * 8) (pow2 64);
    assert (U64.v (U64.mul_mod k_u64 mword) == k * 8);
    wf_object_bound g parent;
    assert (U64.v parent + k * 8 < heap_size);
    FStar.Math.Lemmas.modulo_lemma (U64.v parent + k * 8) (pow2 64);
    let far = U64.add_mod parent (U64.mul_mod k_u64 mword) in
    assert (U64.v far == U64.v field_addr);
    // 5. far is a valid hp_addr with the right properties
    ML.lemma_mod_plus_distr_l (U64.v parent) (k * 8) 8;
    assert (U64.v far % 8 == 0);
    assert (U64.v far < heap_size);
    // 6. read_word g far == read_word g field_addr (same index)
    assert (read_word g (far <: hp_addr) == fv);
    // 7. hd_address fv = hd_address target (trivially, target = fv)
    // 8. Call field_read_implies_exists_pointing
    field_read_implies_exists_pointing g parent wz k_u64 target;
    // 9. Instantiate wfh part 2
    assert (exists_field_pointing_to_unchecked g parent wz target);
    ()
#pop-options

/// ===========================================================================
/// Section 10: Sweep helper lemmas (objects enumeration tracking)
/// ===========================================================================

/// When objects(start, g) is non-empty and we know obj_address(start) is in
/// objects(0, g), the object fits in the heap (from well_formed_heap).
/// This guarantees objects returns non-empty (cases A and B ruled out).
#push-options "--z3rlimit 200"
let objects_nonempty_at (start: hp_addr) (g: heap) : Lemma
  (requires U64.v start + 8 < Seq.length g /\
            well_formed_heap g /\
            Seq.mem (obj_address start) (objects 0UL g))
  (ensures Seq.length (objects start g) > 0)
  = let obj = obj_address start in
    wf_object_size_bound g obj;
    hd_address_spec obj;
    wosize_of_object_spec obj g
#pop-options

/// Head of a non-empty objects sequence is a member of that sequence.
let objects_head_is_mem (start: hp_addr) (g: heap) : Lemma
  (requires Seq.length (objects start g) > 0)
  (ensures Seq.mem (obj_address start) (objects start g))
  = objects_nonempty_head start g;
    // head == obj_address start, and head == Seq.index (objects start g) 0
    // Seq.mem checks all indices, so head is a member
    assert (Seq.index (objects start g) 0 == obj_address start)

/// Membership in objects(start, g) implies membership in objects(0, g)
/// when we have an established subset chain.
let objects_tail_subset_step (start: hp_addr) (g: heap) (x: obj_addr) : Lemma
  (requires Seq.length (objects start g) > 0)
  (ensures (let wz = getWosize (read_word g start) in
            let next_nat = U64.v start + FStar.Mul.((U64.v wz + 1) * 8) in
            next_nat < heap_size /\ next_nat < pow2 64 /\ next_nat % 8 == 0 ==>
            (let next : hp_addr = U64.uint_to_t next_nat in
             Seq.mem x (objects next g) ==> Seq.mem x (objects start g))))
  = objects_later_subset start g x

/// Cursor membership predicate for sweep loop invariant.
/// Encapsulates the hp_addr typing so it can be used safely in Pulse pure assertions.
let cursor_mem (c: U64.t) (g: heap) : prop =
  (U64.v c < heap_size /\ U64.v c % 8 == 0 /\ U64.v c + 8 < heap_size) ==>
  Seq.mem (obj_address c) (objects 0UL g)

/// cursor_mem at 0UL from objects_head_is_mem
let cursor_mem_init (g: heap) : Lemma
  (requires Seq.length (objects 0UL g) > 0)
  (ensures cursor_mem 0UL g)
  = objects_head_is_mem 0UL g;
    objects_later_subset 0UL g (obj_address 0UL)

/// cursor_mem preserved by color change (makeWhite)
let cursor_mem_preserved_makeWhite (g: heap) (obj: obj_addr) (c: U64.t) : Lemma
  (requires Seq.mem obj (objects 0UL g) /\ cursor_mem c g)
  (ensures cursor_mem c (makeWhite obj g))
  = if U64.v c < heap_size && U64.v c % 8 = 0 && U64.v c + 8 < heap_size then begin
      makeWhite_eq obj g;
      let g' = makeWhite obj g in
      color_change_preserves_objects_mem g obj Header.White (obj_address c);
      ()
    end

/// ===========================================================================
/// Section 11: Objects suffix membership (for cursor advancement in sweep)
/// ===========================================================================

/// Key structural lemma: if obj_address(c) is in objects(start, g) and
/// x is in objects(c, g), then x is in objects(start, g).
/// Proof by induction: objects(start, g) = cons (obj_address start) (objects next g).
/// Either c == start (trivial), or obj_address c is in objects(next, g) (by IH).
#push-options "--fuel 3 --ifuel 1 --z3rlimit 400"
let rec objects_suffix_mem (start: hp_addr) (c: hp_addr) (g: heap) (x: obj_addr)
  : Lemma (requires U64.v c + 8 < heap_size /\
                    Seq.mem (obj_address c) (objects start g) /\
                    Seq.mem x (objects c g))
          (ensures Seq.mem x (objects start g))
          (decreases Seq.length g - U64.v start)
  = if U64.v start + 8 >= Seq.length g then ()  // objects start g = empty, contradiction
    else begin
      let header = read_word g start in
      let wz = U64.v (getWosize header) in
      let next_nat = U64.v start + (wz + 1) * 8 in
      if next_nat > Seq.length g || next_nat >= pow2 64 then ()  // objects start g = empty
      else begin
        let oa : obj_addr = obj_address start in
        let oc : obj_addr = obj_address c in
        if next_nat >= heap_size then begin
          // objects start g = singleton [oa]
          mem_cons_lemma oc oa Seq.empty;
          assert (oc == oa);
          mem_cons_lemma x oa Seq.empty;
          ()
        end
        else begin
          let next : hp_addr = U64.uint_to_t next_nat in
          let rest = objects next g in
          mem_cons_lemma oc oa rest;
          if oc = oa then begin
            assert (U64.v c = U64.v start);
            ()
          end
          else begin
            // oc ∈ rest = objects next g
            // By IH: x ∈ objects c g ∧ oc ∈ objects next g ⟹ x ∈ objects next g
            objects_suffix_mem next c g x;
            mem_cons_lemma x oa rest;
            ()
          end
        end
      end
    end
#pop-options

/// Cursor advancement bounds: computes next position bounds from well_formed_heap.
/// cursor_mem cannot be proven without a stronger heap well-formedness (see note below).
#push-options "--z3rlimit 300"
let cursor_advance_bounds (g: heap) (c: hp_addr) : Lemma
  (requires well_formed_heap g /\ Seq.length g == heap_size /\
            U64.v c + 8 < heap_size /\ cursor_mem c g)
  (ensures (let wz = getWosize (read_word g c) in
            let next_nat = U64.v c + (U64.v wz + 1) * 8 in
            next_nat <= heap_size /\
            next_nat % 8 == 0 /\
            next_nat + 8 < pow2 64))
  = assert (Seq.mem (obj_address c) (objects 0UL g));
    objects_nonempty_at c g;
    objects_nonempty_next c g;
    let wz = getWosize (read_word g c) in
    let next_nat = U64.v c + (U64.v wz + 1) * 8 in
    assert (next_nat <= heap_size);
    assert (next_nat % 8 == 0);
    ML.pow2_lt_compat 64 58;
    Math.Lemmas.pow2_double_sum 57
#pop-options

/// ===========================================================================
/// Section 12: Contiguous heap and cursor advancement
/// ===========================================================================

/// A heap is "contiguous" if the objects enumeration has no gaps: for every
/// enumerated position c, if the next position has room for a header (nn + 8
/// < heap_size), then that next position is also enumerated.
/// This is true for OCaml heaps (contiguously packed) but not provable from
/// well_formed_heap alone.
let contiguous_heap (g: heap) : prop =
  forall (c: hp_addr).
    U64.v c + 8 < heap_size ==>
    Seq.mem (obj_address c) (objects 0UL g) ==>
    (let wz = getWosize (read_word g c) in
     let nn = U64.v c + (U64.v wz + 1) * 8 in
     nn + 8 < heap_size /\ nn < pow2 64 /\ nn % 8 == 0 ==>
     Seq.mem (obj_address (U64.uint_to_t nn)) (objects 0UL g))

/// contiguous_heap is preserved by makeWhite.
/// Proof: color change preserves objects enumeration at every position and
/// preserves getWosize at every position. So the same positions are enumerated
/// and the same next-position computations hold.
#push-options "--z3rlimit 200"
let contiguous_heap_preserved_makeWhite (g: heap) (obj: obj_addr) : Lemma
  (requires contiguous_heap g /\ Seq.mem obj (objects 0UL g))
  (ensures contiguous_heap (makeWhite obj g))
  = let g' = makeWhite obj g in
    makeWhite_eq obj g;
    color_change_preserves_objects g obj Header.White;
    let aux (c: hp_addr) : Lemma
      (requires U64.v c + 8 < heap_size /\
               Seq.mem (obj_address c) (objects 0UL g'))
      (ensures (let wz = getWosize (read_word g' c) in
                let nn = U64.v c + (U64.v wz + 1) * 8 in
                nn + 8 < heap_size /\ nn < pow2 64 /\ nn % 8 == 0 ==>
                Seq.mem (obj_address (U64.uint_to_t nn)) (objects 0UL g')))
      = ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// contiguous_heap is preserved by makeGray.
#push-options "--z3rlimit 200"
let contiguous_heap_preserved_makeGray (g: heap) (obj: obj_addr) : Lemma
  (requires contiguous_heap g /\ Seq.mem obj (objects 0UL g))
  (ensures contiguous_heap (makeGray obj g))
  = let g' = makeGray obj g in
    makeGray_eq obj g;
    color_change_preserves_objects g obj Header.Gray;
    let aux (c: hp_addr) : Lemma
      (requires U64.v c + 8 < heap_size /\
               Seq.mem (obj_address c) (objects 0UL g'))
      (ensures (let wz = getWosize (read_word g' c) in
                let nn = U64.v c + (U64.v wz + 1) * 8 in
                nn + 8 < heap_size /\ nn < pow2 64 /\ nn % 8 == 0 ==>
                Seq.mem (obj_address (U64.uint_to_t nn)) (objects 0UL g')))
      = ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// contiguous_heap is preserved by makeBlack.
#push-options "--z3rlimit 200"
let contiguous_heap_preserved_makeBlack (g: heap) (obj: obj_addr) : Lemma
  (requires contiguous_heap g /\ Seq.mem obj (objects 0UL g))
  (ensures contiguous_heap (makeBlack obj g))
  = let g' = makeBlack obj g in
    makeBlack_eq obj g;
    color_change_preserves_objects g obj Header.Black;
    let aux (c: hp_addr) : Lemma
      (requires U64.v c + 8 < heap_size /\
               Seq.mem (obj_address c) (objects 0UL g'))
      (ensures (let wz = getWosize (read_word g' c) in
                let nn = U64.v c + (U64.v wz + 1) * 8 in
                nn + 8 < heap_size /\ nn < pow2 64 /\ nn % 8 == 0 ==>
                Seq.mem (obj_address (U64.uint_to_t nn)) (objects 0UL g')))
      = ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// contiguous_heap is preserved by set_object_color_raw (covers blue and all colors).
#push-options "--z3rlimit 200"
let contiguous_heap_preserved_raw_color (g: heap) (obj: obj_addr) (col: U64.t{U64.v col < 4}) : Lemma
  (requires contiguous_heap g /\ Seq.mem obj (objects 0UL g))
  (ensures contiguous_heap (set_object_color_raw obj g col))
  = let g' = set_object_color_raw obj g col in
    raw_color_change_preserves_objects g obj col;
    let aux (c: hp_addr) : Lemma
      (requires U64.v c + 8 < heap_size /\
               Seq.mem (obj_address c) (objects 0UL g'))
      (ensures (let wz = getWosize (read_word g' c) in
                let nn = U64.v c + (U64.v wz + 1) * 8 in
                nn + 8 < heap_size /\ nn < pow2 64 /\ nn % 8 == 0 ==>
                Seq.mem (obj_address (U64.uint_to_t nn)) (objects 0UL g')))
      = header_at_preserved obj g col c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// cursor_mem_advance: the key lemma for sweep cursor advancement.
/// Given contiguous_heap and cursor_mem at c, proves cursor_mem at the next position.
#push-options "--z3rlimit 300"
let cursor_mem_advance (g: heap) (c: hp_addr) : Lemma
  (requires contiguous_heap g /\ well_formed_heap g /\ Seq.length g == heap_size /\
            cursor_mem c g /\ U64.v c + 8 < heap_size)
  (ensures (let wz = getWosize (read_word g c) in
            let nn = U64.v c + (U64.v wz + 1) * 8 in
            nn < pow2 64 /\ nn % 8 == 0 /\ nn <= heap_size /\
            nn + 8 < pow2 64 /\
            cursor_mem (U64.uint_to_t nn) g))
  = assert (Seq.mem (obj_address c) (objects 0UL g));
    objects_nonempty_at c g;
    cursor_advance_bounds g c;
    let wz = getWosize (read_word g c) in
    let nn = U64.v c + (U64.v wz + 1) * 8 in
    // If nn + 8 >= heap_size: cursor_mem (uint_to_t nn) g is vacuously true
    // If nn + 8 < heap_size: contiguous_heap gives obj_address(nn) ∈ objects 0UL g
    ()
#pop-options

/// Transfer cursor_mem across objects_preserved (objects lists are equal).
let cursor_mem_from_objects_preserved (g1 g2: heap) (c: U64.t) : Lemma
  (requires objects_preserved g1 g2 /\ cursor_mem c g2)
  (ensures cursor_mem c g1)
  = ()
