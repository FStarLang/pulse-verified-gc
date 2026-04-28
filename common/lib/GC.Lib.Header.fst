module GC.Lib.Header

/// Pure header operations for OCaml GC with semantic types
///
/// Header layout (64-bit):
///   bits 0-7   : tag (8 bits)
///   bits 8-9   : color (2 bits: white=0, gray=1, black=2)
///   bits 10-63 : wosize (54 bits)

module UInt = FStar.UInt
open FStar.UInt
open FStar.Classical
open FStar.Math.Lemmas

/// ---------------------------------------------------------------------------
/// Semantic Color Type
/// ---------------------------------------------------------------------------

type color_sem =
  | White  // 0 - Not yet visited
  | Gray   // 1 - Visited but not scanned
  | Blue   // 2 - Free-list block
  | Black  // 3 - Fully scanned

let pack_color (c: color_sem) : uint_t 64 =
  match c with
  | White -> 0
  | Gray -> 1
  | Blue -> 2
  | Black -> 3

let unpack_color (w: uint_t 64) : option color_sem =
  if w = 0 then Some White
  else if w = 1 then Some Gray
  else if w = 2 then Some Blue
  else if w = 3 then Some Black
  else None

let valid_color (w: uint_t 64) : bool = w < 4

/// Pack/unpack roundtrip for colors
let pack_unpack_color (c: color_sem) 
  : Lemma (unpack_color (pack_color c) == Some c) 
  = ()

let unpack_pack_color (w: uint_t 64{valid_color w}) 
  : Lemma (pack_color (Some?.v (unpack_color w)) == w) 
  = ()

let valid_color_unpack (w: uint_t 64) 
  : Lemma (valid_color w <==> Some? (unpack_color w))
  = ()

/// ---------------------------------------------------------------------------
/// Semantic Header Type  
/// ---------------------------------------------------------------------------

type header_sem = {
  wosize : w:uint_t 64{w < pow2 54};
  color  : color_sem;
  tag    : t:uint_t 64{t < 256};
}

/// ---------------------------------------------------------------------------
/// Bitvector Operations
/// ---------------------------------------------------------------------------

// Symbolic mask definitions (for nth-level proofs)
private let v256 : uint_t 64 = shift_left #64 1 8   // bit 55 (= 256)
private let v512 : uint_t 64 = shift_left #64 1 9   // bit 54 (= 512)
private let mask_2bit : uint_t 64 = logor #64 1 2  // equals 3

let mask_color : uint_t 64 = logor #64 v256 v512  // 768 = 0x300 = bits 8-9
let mask_tag : uint_t 64 = shift_right #64 (ones 64) 56  // 255 = 0xFF = bits 0-7

let get_tag (v: uint_t 64) : uint_t 64 = 
  logand #64 v mask_tag

let get_color (v: uint_t 64) : uint_t 64 = 
  logand #64 (shift_right #64 v 8) mask_2bit

let get_wosize (v: uint_t 64) : uint_t 64 = 
  shift_right #64 v 10

let set_color (v: uint_t 64) (c: uint_t 64{c < 4}) : uint_t 64 =
  logor #64 (logand #64 v (lognot #64 mask_color)) (shift_left #64 c 8)

/// Bounds lemmas needed for unpacking
#push-options "--z3rlimit 100"
let get_tag_bound (v: uint_t 64) : Lemma (get_tag v < 256) =
  logand_le #64 v 255
#pop-options

let get_wosize_bound (v: uint_t 64) : Lemma (get_wosize v < pow2 54) =
  shift_right_value_lemma #64 v 10;
  lemma_div_lt_nat v 64 10

/// ---------------------------------------------------------------------------
/// Pack/Unpack for Headers
/// ---------------------------------------------------------------------------

let pack_header (h: header_sem) : uint_t 64 =
  logor #64 h.tag 
    (logor #64 (shift_left #64 (pack_color h.color) 8)
               (shift_left #64 h.wosize 10))

let unpack_header (w: uint_t 64) : option header_sem =
  let c = get_color w in
  match unpack_color c with
  | None -> None
  | Some col -> 
    get_tag_bound w;
    get_wosize_bound w;
    Some { 
      wosize = get_wosize w; 
      color = col; 
      tag = get_tag w 
    }

/// get_color always returns < 4 (logand with 3)
let get_color_bound (v: uint_t 64) : Lemma (get_color v < 4) =
  logor_disjoint #64 2 1 1; 
  logor_commutative #64 1 2;
  assert (mask_2bit = 3);
  logand_le #64 (shift_right #64 v 8) mask_2bit

/// Expose get_color definition in terms of 3 (not private mask_2bit)
#push-options "--z3rlimit 20"
let get_color_val (v: uint_t 64) : Lemma (get_color v == logand #64 (shift_right #64 v 8) 3) =
  logor_disjoint #64 2 1 1; logor_commutative #64 1 2
#pop-options

/// Therefore unpack_header succeeds when color bits are valid (not 0)
let unpack_header_total (w: uint_t 64) : Lemma 
  (requires valid_color (get_color w))
  (ensures Some? (unpack_header w)) =
  valid_color_unpack (get_color w)

/// Accessor for unpacked header (uses totality)
let unpack_header_v (w: uint_t 64{valid_color (get_color w)}) : header_sem =
  unpack_header_total w;
  Some?.v (unpack_header w)

/// ---------------------------------------------------------------------------
/// Semantic Color Operations
/// ---------------------------------------------------------------------------

let set_color_sem (h: header_sem) (c: color_sem) : header_sem =
  { h with color = c }

/// Trivial by record semantics
let set_color_sem_color (h: header_sem) (c: color_sem)
  : Lemma ((set_color_sem h c).color == c)
  = ()

let set_color_sem_preserves_wosize (h: header_sem) (c: color_sem)
  : Lemma ((set_color_sem h c).wosize == h.wosize)
  = ()

let set_color_sem_preserves_tag (h: header_sem) (c: color_sem)
  : Lemma ((set_color_sem h c).tag == h.tag)
  = ()

/// ---------------------------------------------------------------------------
/// Helper Lemmas for Bit-level Proofs
/// ---------------------------------------------------------------------------

/// Prove symbolic masks equal numeric constants
private let logor_1_2_eq_3 () : Lemma (logor #64 1 2 = 3) =
  logor_disjoint #64 2 1 1; logor_commutative #64 1 2

private let nth_mask_2bit (i: nat{i < 64}) : Lemma (nth #64 mask_2bit i = (i >= 62)) =
  one_nth_lemma #64 i; pow2_nth_lemma #64 1 i;
  assert_norm (pow2_n #64 1 = 2); logor_definition #64 1 2 i

#push-options "--z3rlimit 20"
private let c_eq_c_and_mask2 (c: uint_t 64{c < 4}) : Lemma (logand #64 c mask_2bit = c) =
  logor_1_2_eq_3 (); logand_mask #64 c 2;
  assert_norm (pow2 2 = 4); assert_norm (pow2 2 - 1 = 3)
#pop-options

private let small_nth_zero (c: uint_t 64{c < 4}) (i: nat{i < 64 /\ i < 62}) : Lemma (nth #64 c i = false) =
  c_eq_c_and_mask2 c; logand_definition #64 c mask_2bit i; nth_mask_2bit i

/// nth properties for v256 and v512
private let nth_256 (i: nat{i < 64}) : Lemma (nth #64 v256 i = (i = 55)) =
  if i >= 56 then shift_left_lemma_1 #64 1 8 i
  else (shift_left_lemma_2 #64 1 8 i; one_nth_lemma #64 (i + 8))

private let nth_512 (i: nat{i < 64}) : Lemma (nth #64 v512 i = (i = 54)) =
  if i >= 55 then shift_left_lemma_1 #64 1 9 i
  else (shift_left_lemma_2 #64 1 9 i; one_nth_lemma #64 (i + 9))

/// nth property of mask_color
private let nth_mask_color (i: nat{i < 64}) : Lemma (nth #64 mask_color i = (i = 54 || i = 55)) =
  nth_256 i; nth_512 i; logor_definition #64 v256 v512 i

private let nth_not_mask_color (i: nat{i < 64}) 
  : Lemma (nth #64 (lognot #64 mask_color) i = (i <> 54 && i <> 55)) =
  nth_mask_color i; lognot_definition #64 mask_color i

/// nth properties of c shifted left by 8 (for c < 4)
private let nth_c_shifted_8 (c: uint_t 64{c < 4}) (i: nat{i < 64}) 
  : Lemma (nth #64 (shift_left #64 c 8) i = (if i >= 56 then false
                                              else if i = 55 then nth #64 c 63
                                              else if i = 54 then nth #64 c 62
                                              else false)) =
  if i >= 56 then shift_left_lemma_1 #64 c 8 i
  else begin
    shift_left_lemma_2 #64 c 8 i;
    if i + 8 < 62 then small_nth_zero c (i + 8) else ()
  end

/// Key lemma: setColor preserves bits outside positions 54-55
private let setColor_preserves_bit (v: uint_t 64) (c: uint_t 64{c < 4}) (i: nat{i < 64}) 
  : Lemma (requires i <> 54 /\ i <> 55)
          (ensures nth #64 (set_color v c) i = nth #64 v i) =
  logor_definition #64 (logand #64 v (lognot #64 mask_color)) (shift_left #64 c 8) i;
  logand_definition #64 v (lognot #64 mask_color) i;
  nth_not_mask_color i;
  nth_c_shifted_8 c i

/// setColor sets bits 54-55 according to c
private let setColor_bit_54_55 (v: uint_t 64) (c: uint_t 64{c < 4}) (i: nat{i < 64 /\ (i = 54 || i = 55)}) 
  : Lemma (nth #64 (set_color v c) i = nth #64 (shift_left #64 c 8) i) =
  logor_definition #64 (logand #64 v (lognot #64 mask_color)) (shift_left #64 c 8) i;
  logand_definition #64 v (lognot #64 mask_color) i;
  nth_not_mask_color i

/// ---------------------------------------------------------------------------
/// Key Lemmas (bitvector level)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

#restart-solver

/// getColor after setColor returns the color
private let getColor_setColor_aux (v: uint_t 64) (c: uint_t 64{c < 4}) (i: nat{i < 64}) 
  : Lemma (nth #64 (get_color (set_color v c)) i = nth #64 c i) =
  let scv = set_color v c in
  let shifted = shift_right #64 scv 8 in
  logand_definition #64 shifted mask_2bit i;
  nth_mask_2bit i;
  if i < 62 then begin
    small_nth_zero c i
  end else begin
    shift_right_lemma_2 #64 scv 8 i;
    let j = i - 8 in
    assert (j = 54 || j = 55);
    setColor_bit_54_55 v c j;
    shift_left_lemma_2 #64 c 8 j;
    assert (j + 8 = i)
  end

let getColor_setColor (v: uint_t 64) (c: uint_t 64{c < 4}) 
  : Lemma (get_color (set_color v c) == c) =
  let aux (i: nat{i < 64}) : Lemma (nth #64 (get_color (set_color v c)) i = nth #64 c i) =
    getColor_setColor_aux v c i
  in
  forall_intro aux;
  nth_lemma #64 (get_color (set_color v c)) c

#restart-solver

/// setColor preserves wosize
let setColor_preserves_wosize (v: uint_t 64) (c: uint_t 64{c < 4}) 
  : Lemma (get_wosize (set_color v c) == get_wosize v) =
  let scv = set_color v c in
  let aux (i: nat{i < 64}) : Lemma (nth #64 (get_wosize scv) i = nth #64 (get_wosize v) i) =
    if i < 10 then begin
      shift_right_lemma_1 #64 scv 10 i;
      shift_right_lemma_1 #64 v 10 i
    end else begin
      shift_right_lemma_2 #64 scv 10 i;
      shift_right_lemma_2 #64 v 10 i;
      let j = i - 10 in
      if j < 54 then setColor_preserves_bit v c j else ()
    end
  in
  forall_intro aux;
  nth_lemma #64 (get_wosize scv) (get_wosize v)

/// setColor preserves tag  
let setColor_preserves_tag (v: uint_t 64) (c: uint_t 64{c < 4})
  : Lemma (get_tag (set_color v c) == get_tag v) =
  let scv = set_color v c in
  let aux (i: nat{i < 64}) : Lemma (nth #64 (get_tag scv) i = nth #64 (get_tag v) i) =
    logand_definition #64 scv 255 i;
    logand_definition #64 v 255 i;
    // 255 keeps only bits 56-63 (the least significant byte)
    // For i < 56: both sides are false (ANDing with false)
    // For i >= 56: both sides equal the original bit (ANDing with true)
    // Need to show that 255 has bit i set iff i >= 56
    assert_norm (255 = pow2 8 - 1);
    pow2_nth_lemma #64 8 i;
    if i >= 56 then setColor_preserves_bit v c i else ()
  in
  forall_intro aux;
  nth_lemma #64 (get_tag scv) (get_tag v)

#pop-options

/// ---------------------------------------------------------------------------
/// Bridge: Semantic ↔ Bitvector
/// ---------------------------------------------------------------------------

/// Helper: small numbers have high bits zero
private let small_value_nth (t: uint_t 64{t < 256}) (i: nat{i < 64 /\ i < 56})
  : Lemma (nth t i = false)
  = logand_mask #64 t 8;
    logand_definition t (pow2 8 - 1) i;
    pow2_nth_lemma #64 8 i

/// Helper: c < 4 means only bits 62-63 can be non-zero
private let small_2bit_nth (c: uint_t 64{c < 4}) (i: nat{i < 64 /\ i < 62})
  : Lemma (nth c i = false)
  = logand_mask #64 c 2;
    assert (logand c 3 == c);
    logand_definition c 3 i;
    logor_definition #64 1 2 i;
    one_nth_lemma #64 i;
    pow2_nth_lemma #64 1 i

/// Helper: color<<8 only affects bits 54-55
#push-options "--z3rlimit 100"
private let nth_c_shifted_only_color (c: uint_t 64{c < 4}) (i: nat{i < 64})
  : Lemma (i <> 54 /\ i <> 55 ==> nth (shift_left c 8) i = false)
  = if i >= 56 then shift_left_lemma_1 #64 c 8 i
    else if i < 54 then begin
      shift_left_lemma_2 #64 c 8 i;
      small_2bit_nth c (i + 8)
    end
#pop-options

/// Helper: wosize<<10 has no bits at positions 54-55
private let nth_wosize_shifted_not_color (w: uint_t 64) (i: nat{i < 64})
  : Lemma (i = 54 \/ i = 55 ==> nth (shift_left w 10) i = false)
  = if i = 54 then shift_left_lemma_1 #64 w 10 i
    else if i = 55 then shift_left_lemma_1 #64 w 10 i

/// Setting color semantically then packing = setting color on packed
#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"
let pack_set_color (h: header_sem) (c: color_sem)
  : Lemma (pack_header (set_color_sem h c) == set_color (pack_header h) (pack_color c))
  = let lhs = pack_header (set_color_sem h c) in
    let rhs = set_color (pack_header h) (pack_color c) in
    
    let aux (i: nat{i < 64}) : Lemma (nth lhs i == nth rhs i) =
      // LHS = h.tag | (pack_color c << 8) | (h.wosize << 10)
      logor_definition h.tag (logor (shift_left (pack_color c) 8) (shift_left h.wosize 10)) i;
      logor_definition (shift_left (pack_color c) 8) (shift_left h.wosize 10) i;
      
      // RHS = (pack_header h & ~mask) | (pack_color c << 8)
      logor_definition (logand (pack_header h) (lognot mask_color)) (shift_left (pack_color c) 8) i;
      
      // Expand pack_header h
      logand_definition (pack_header h) (lognot mask_color) i;
      logor_definition h.tag (logor (shift_left (pack_color h.color) 8) (shift_left h.wosize 10)) i;
      logor_definition (shift_left (pack_color h.color) 8) (shift_left h.wosize 10) i;
      
      // Each component's AND with ~mask
      logand_definition h.tag (lognot mask_color) i;
      logand_definition (shift_left (pack_color h.color) 8) (lognot mask_color) i;
      logand_definition (shift_left h.wosize 10) (lognot mask_color) i;
      
      // Key lemmas
      nth_not_mask_color i;
      nth_c_shifted_only_color (pack_color h.color) i;
      nth_c_shifted_only_color (pack_color c) i;
      nth_wosize_shifted_not_color h.wosize i;
      if i < 56 then small_value_nth h.tag i
    in
    FStar.Classical.forall_intro aux;
    nth_lemma lhs rhs
#pop-options

/// Unpacking then getting color = getting color then unpacking  
let unpack_get_color (w: uint_t 64)
  : Lemma (requires Some? (unpack_header w))
          (ensures (Some?.v (unpack_header w)).color == Some?.v (unpack_color (get_color w)))
  = ()  // By definition of unpack_header

/// ---------------------------------------------------------------------------
/// Mask Value Lemmas
/// ---------------------------------------------------------------------------

/// mask_tag = 255
#push-options "--z3rlimit 50"
let mask_tag_value () : Lemma (mask_tag == 255) =
  shift_right_value_lemma #64 (ones 64) 56;
  assert_norm (pow2 64 - 1 == 18446744073709551615);
  assert_norm (pow2 56 == 72057594037927936);
  assert_norm ((pow2 64 - 1) / pow2 56 == 255)
#pop-options

/// A header is valid for tri-color GC if its color is valid
let valid_header (w: uint_t 64) : bool = valid_color (get_color w)

/// ---------------------------------------------------------------------------
/// Roundtrip Proofs
/// ---------------------------------------------------------------------------

private let nth_mask_tag (i: nat{i < 64}) : Lemma (nth mask_tag i = (i >= 56)) =
  if i < 56 then shift_right_lemma_1 #64 (ones 64) 56 i
  else begin
    shift_right_lemma_2 #64 (ones 64) 56 i;
    ones_nth_lemma #64 (i - 56)
  end

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let get_tag_pack_header (h: header_sem)
  : Lemma (get_tag (pack_header h) == h.tag)
  = let ph = pack_header h in
    let c = pack_color h.color in
    let aux (i: nat{i < 64}) : Lemma (nth (get_tag ph) i == nth h.tag i) =
      logand_definition ph mask_tag i;
      nth_mask_tag i;
      logor_definition h.tag (logor (shift_left c 8) (shift_left h.wosize 10)) i;
      logor_definition (shift_left c 8) (shift_left h.wosize 10) i;
      if i < 56 then begin
        logand_mask #64 h.tag 8; logand_definition h.tag (pow2 8 - 1) i; pow2_nth_lemma #64 8 i
      end else begin
        shift_left_lemma_1 #64 c 8 i;
        shift_left_lemma_1 #64 h.wosize 10 i
      end
    in forall_intro aux; nth_lemma (get_tag ph) h.tag
#pop-options

#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"  
let get_color_pack_header (h: header_sem)
  : Lemma (get_color (pack_header h) == pack_color h.color)
  = let ph = pack_header h in
    let c = pack_color h.color in
    let w = h.wosize in
    let aux (i: nat{i < 64}) : Lemma (nth (get_color ph) i == nth c i) =
      logand_definition (shift_right ph 8) mask_2bit i;
      nth_mask_2bit i;
      shift_right_logor_lemma #64 h.tag (logor (shift_left c 8) (shift_left w 10)) 8;
      shift_right_logor_lemma #64 (shift_left c 8) (shift_left w 10) 8;
      logor_definition (shift_right h.tag 8) 
                       (logor (shift_right (shift_left c 8) 8) (shift_right (shift_left w 10) 8)) i;
      logor_definition (shift_right (shift_left c 8) 8) (shift_right (shift_left w 10) 8) i;
      if i < 62 then small_2bit_nth c i
      else begin
        shift_right_lemma_2 #64 h.tag 8 i;
        logand_mask #64 h.tag 8; logand_definition h.tag (pow2 8 - 1) (i - 8); pow2_nth_lemma #64 8 (i - 8);
        shift_right_lemma_2 #64 (shift_left c 8) 8 i; shift_left_lemma_2 #64 c 8 (i - 8);
        shift_right_lemma_2 #64 (shift_left w 10) 8 i;
        shift_left_lemma_1 #64 w 10 (i - 8)
      end
    in forall_intro aux; nth_lemma (get_color ph) c
#pop-options

#push-options "--z3rlimit 800 --fuel 0 --ifuel 0"
let get_wosize_pack_header (h: header_sem)
  : Lemma (get_wosize (pack_header h) == h.wosize)
  = let ph = pack_header h in
    let c = pack_color h.color in
    let w = h.wosize in
    
    let aux (i: nat{i < 64}) : Lemma (nth (get_wosize ph) i == nth w i) =
      shift_right_logor_lemma #64 h.tag (logor (shift_left c 8) (shift_left w 10)) 10;
      shift_right_logor_lemma #64 (shift_left c 8) (shift_left w 10) 10;
      logor_definition (shift_right h.tag 10) 
                       (logor (shift_right (shift_left c 8) 10) (shift_right (shift_left w 10) 10)) i;
      logor_definition (shift_right (shift_left c 8) 10) (shift_right (shift_left w 10) 10) i;
      
      if i < 10 then begin
        shift_right_lemma_1 #64 h.tag 10 i;
        shift_right_lemma_1 #64 (shift_left c 8) 10 i;
        shift_right_lemma_1 #64 (shift_left w 10) 10 i;
        logand_mask #64 w 54; 
        assert_norm (pow2 54 > 0);
        logand_definition w (pow2 54 - 1) i; 
        pow2_nth_lemma #64 54 i
      end else begin
        shift_right_lemma_2 #64 h.tag 10 i;
        logand_mask #64 h.tag 8;
        assert_norm (pow2 8 > 0);
        logand_definition h.tag (pow2 8 - 1) (i - 10);
        pow2_nth_lemma #64 8 (i - 10);
        
        shift_right_lemma_2 #64 (shift_left c 8) 10 i;
        shift_left_lemma_2 #64 c 8 (i - 10);
        logand_mask #64 c 2;
        assert_norm (pow2 2 - 1 = 3);
        logand_definition c 3 (i - 2);
        logor_definition #64 1 2 (i - 2);
        one_nth_lemma #64 (i - 2);
        pow2_nth_lemma #64 1 (i - 2);
        
        shift_right_lemma_2 #64 (shift_left w 10) 10 i;
        shift_left_lemma_2 #64 w 10 (i - 10)
      end
    in
    forall_intro aux;
    nth_lemma (get_wosize ph) w
#pop-options

/// pack (unpack h) == Some h
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let pack_unpack_header (h: header_sem) 
  : Lemma (unpack_header (pack_header h) == Some h)
  = get_tag_pack_header h;
    get_color_pack_header h;
    get_wosize_pack_header h
#pop-options

/// unpack (pack v) == v when valid
#push-options "--z3rlimit 500 --fuel 0 --ifuel 0"
let unpack_pack_header (v: uint_t 64)
  : Lemma (requires valid_header v)
          (ensures pack_header (Some?.v (unpack_header v)) == v)
  = let h = Some?.v (unpack_header v) in
    unpack_pack_color (get_color v);
    
    let aux (i: nat{i < 64}) : Lemma (nth (pack_header h) i == nth v i) =
      logor_definition h.tag (logor (shift_left (pack_color h.color) 8) (shift_left h.wosize 10)) i;
      logor_definition (shift_left (pack_color h.color) 8) (shift_left h.wosize 10) i;
      logand_definition v mask_tag i;
      nth_mask_tag i;
      logand_definition (shift_right v 8) mask_2bit i;
      one_nth_lemma #64 i; pow2_nth_lemma #64 1 i; logor_definition #64 1 2 i;
      
      if i < 54 then begin
        logand_mask #64 h.tag 8;
        logand_definition h.tag (pow2 8 - 1) i;
        pow2_nth_lemma #64 8 i;
        if i < 56 then shift_left_lemma_2 #64 (pack_color h.color) 8 i
        else shift_left_lemma_1 #64 (pack_color h.color) 8 i;
        logand_mask #64 (pack_color h.color) 2;
        logand_definition (pack_color h.color) 3 (i + 8);
        logor_definition #64 1 2 (i + 8);
        one_nth_lemma #64 (i + 8);
        pow2_nth_lemma #64 1 (i + 8);
        shift_left_lemma_2 #64 h.wosize 10 i;
        shift_right_lemma_2 #64 v 10 (i + 10)
      end
      else if i < 56 then begin
        logand_mask #64 h.tag 8;
        logand_definition h.tag (pow2 8 - 1) i;
        pow2_nth_lemma #64 8 i;
        shift_left_lemma_2 #64 (pack_color h.color) 8 i;
        logand_definition (shift_right v 8) mask_2bit (i + 8);
        logor_definition #64 1 2 (i + 8);
        one_nth_lemma #64 (i + 8);
        pow2_nth_lemma #64 1 (i + 8);
        shift_right_lemma_2 #64 v 8 (i + 8);
        shift_left_lemma_1 #64 h.wosize 10 i
      end
      else begin
        shift_left_lemma_1 #64 (pack_color h.color) 8 i;
        shift_left_lemma_1 #64 h.wosize 10 i
      end
    in
    forall_intro aux;
    nth_lemma (pack_header h) v
#pop-options

/// ---------------------------------------------------------------------------
/// U64.t Wrappers for External Use
/// ---------------------------------------------------------------------------

module U64 = FStar.UInt64

/// Get color from header (U64.t version)
let get_color64 (v: U64.t) : c:U64.t{U64.v c < 4} = 
  get_color_bound (U64.v v);
  U64.uint_to_t (get_color (U64.v v))

/// Set color in header (U64.t version)
let set_color64 (v: U64.t) (c: U64.t{U64.v c < 4}) : U64.t =
  U64.uint_to_t (set_color (U64.v v) (U64.v c))

/// Pack semantic header to U64.t
let pack_header64 (h: header_sem) : U64.t =
  U64.uint_to_t (pack_header h)

/// Unpack U64.t to semantic header
let unpack_header64 (v: U64.t) : option header_sem =
  unpack_header (U64.v v)

/// Check if header has valid color (U64.t version)
let valid_header64 (v: U64.t) : bool = valid_header (U64.v v)

/// Get unpacked header (requires valid, U64.t version)
let unpack_header64_v (v: U64.t{valid_header64 v}) : header_sem =
  unpack_header_v (U64.v v)

/// ---------------------------------------------------------------------------
/// U64.t Wrapper Lemmas
/// ---------------------------------------------------------------------------

let getColor64_setColor64 (v: U64.t) (c: U64.t{U64.v c < 4}) 
  : Lemma (get_color64 (set_color64 v c) == c) =
  getColor_setColor (U64.v v) (U64.v c);
  U64.uv_inv c

let setColor64_preserves_wosize (v: U64.t) (c: U64.t{U64.v c < 4}) 
  : Lemma (get_wosize (U64.v (set_color64 v c)) == get_wosize (U64.v v)) =
  setColor_preserves_wosize (U64.v v) (U64.v c)

let setColor64_preserves_tag (v: U64.t) (c: U64.t{U64.v c < 4})
  : Lemma (get_tag (U64.v (set_color64 v c)) == get_tag (U64.v v)) =
  setColor_preserves_tag (U64.v v) (U64.v c)

let pack_unpack_header64 (h: header_sem) 
  : Lemma (unpack_header64 (pack_header64 h) == Some h) =
  pack_unpack_header h

let unpack_pack_header64 (v: U64.t{valid_header64 v})
  : Lemma (pack_header64 (unpack_header64_v v) == v) =
  unpack_pack_header (U64.v v)

/// makeHeader from extracted fields with new color == set_color
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let repack_set_color64 (v: U64.t{valid_header64 v}) (c: color_sem)
  : Lemma (requires get_wosize (U64.v v) < pow2 54 /\ get_tag (U64.v v) < 256)
          (ensures pack_header64 { wosize = get_wosize (U64.v v); color = c; tag = get_tag (U64.v v) } ==
                   set_color64 v (U64.uint_to_t (pack_color c)))
  = unpack_pack_header (U64.v v);
    let h = Some?.v (unpack_header (U64.v v)) in
    pack_set_color h c
#pop-options
