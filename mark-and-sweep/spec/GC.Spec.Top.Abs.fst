/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Abs - the byte-level major heap, read as the model
/// ---------------------------------------------------------------------------
///
/// `abs g` reads the byte-level heap `g` (GC.Spec.Base) as a heap of the
/// top-level specification (GC.Spec.Top.Heap):
///   - model word `m` is the byte word at `zero_addr + 8 m`; the model heap has
///     `(heap_size - zero_addr) / 8` words;
///   - a block starts at `m` exactly when the heap walk from `zero_addr`
///     (`GC.Spec.Walk.reaches`) lands on its header and can step: the blocks of
///     the model are the objects of `objects zero_addr g` (`abs_is_block`);
///   - its header is the decoded header (`GC.Spec.Top.Word.abs_hdr`: wosize,
///     tag, colour; blue stays blue);
///   - every word is read by `GC.Spec.Top.Word.absv`: a major pointer, a young
///     pointer, or a word of bytes (infix headers included, whole).
/// The representation relation of the byte heap is `brepr m g`: `m` is,
/// word by word, the canonical reading `cabs g` (`abs g` with the words
/// outside fields read as 0); the bytes below `zero_addr` are not read.
///
/// Proved:
///   - blocks, headers, colours and fields correspond to GC.Spec.Object's
///     (`abs_is_block`, `abs_header`, `abs_blue`, `abs_field`); the reads
///     `read_hd`, `read_field` are those of every represented model heap
///     (`brepr_reads`);
///   - pointers correspond: a word is a major pointer of the model exactly
///     when it is `is_pointer`, to the object whose header is there
///     (`absv_major`); a pointer the model resolves through an infix header
///     resolves to the same closure by `GC.Spec.Object.resolve_object`
///     (`resolve_infix_bytes`), and a pointer to a block to itself
///     (`resolve_block_bytes`); a word is a young pointer exactly when it is an
///     aligned nursery offset (`absv_young`);
///   - when the walk reaches the end of the heap the model is tiled
///     (`abs_tiled`, `abs_well_formed`);
///   - nothing missing: every representable model heap is represented, by
///     the heap whose words are the model's (`conc`, `conc_repr`).

module GC.Spec.Top.Abs

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Walk
open GC.Lib.Header
open GC.Spec.Top.Word
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module GB = GC.Gen.Base

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// The byte position of model word `m`.
let pos (m: nat) : nat = base + 8 * m

let pos_aligned (m: nat) : Lemma (pos m % 8 == 0) = base_facts ()

let hp (m: nat{pos m < heap_size}) : hp_addr = pos_aligned m; mk_hp_addr (pos m)

/// The model address of a byte header position.
let mpos (p: nat) : nat = if p >= base then (p - base) / 8 else 0

/// The walk lands on the header at model word `m` and can step.
let on_walk (g: heap) (m: nat) : bool =
  if pos m < heap_size then reaches g zero_addr (pos m) && can_step g (hp m) else false

let word (g: heap) (m: nat) : U64.t =
  if pos m < heap_size then read_word g (hp m) else 0UL

let abs_hd (g: heap) (m: nat) : option M.header =
  if on_walk g m then Some (abs_hdr (word g m)) else None

let abs_body (g: heap) (m: nat) : M.value = absv (word g m)

let abs (g: heap) : M.mheap = { M.size = msize; M.hd = abs_hd g; M.body = abs_body g }

/// ---------------------------------------------------------------------------
/// Blocks, headers, fields
/// ---------------------------------------------------------------------------

let msize_pos (m: nat) : Lemma (m < msize <==> pos m < heap_size)
  = base_facts ()

/// The object (first-field address) of the block at model word `m`.
let obj_of (m: nat{pos m + 8 < heap_size}) : obj_addr =
  pos_aligned m; base_facts (); mk_hp_addr (pos m + 8)

let abs_is_block (g: heap) (m: nat)
  : Lemma (M.is_block (abs g) m <==>
           (pos m + 8 < heap_size /\ Seq.mem (obj_of m) (objects zero_addr g)))
  = msize_pos m;
    if pos m + 8 < heap_size then begin
      objects_mem_iff g zero_addr (obj_of m);
      hd_address_pos (obj_of m)
    end

let abs_header (g: heap) (m: nat)
  : Lemma (requires M.is_block (abs g) m)
          (ensures pos m + 8 < heap_size /\
                   M.wz_of (abs g) m == U64.v (wosize_of_object (obj_of m) g) /\
                   M.tag_of (abs g) m == U64.v (tag_of_object (obj_of m) g) /\
                   M.col_of (abs g) m == abs_col (color_of_object (obj_of m) g))
  = abs_is_block g m;
    hd_address_pos (obj_of m);
    wosize_of_object_spec (obj_of m) g;
    tag_of_object_spec (obj_of m) g;
    color_of_object_spec (obj_of m) g

let abs_blue (g: heap) (m: nat)
  : Lemma (requires M.is_block (abs g) m)
          (ensures pos m + 8 < heap_size /\ (M.col_of (abs g) m == M.Blue <==> is_blue (obj_of m) g))
  = abs_header g m;
    is_blue_iff (obj_of m) g

/// Field `i` of a block is the word `i` past its first-field address.
let abs_field (g: heap) (m i: nat)
  : Lemma (requires pos (m + 1 + i) < heap_size)
          (ensures M.field (abs g) m i == absv (read_word g (hp (m + 1 + i))) /\
                   U64.v (hp (m + 1 + i)) == pos m + 8 + 8 * i)
  = ()

/// The instance's reads: the decoded header at a walk position, and the
/// word at a field's address.
let read_hd (g: heap) (o: nat) : GTot (option M.header) = abs_hd g o

let read_field (g: heap) (o i: nat) : GTot M.value =
  if pos (o + 1 + i) < heap_size then absv (read_word g (hp (o + 1 + i))) else M.VInt 0

/// ---------------------------------------------------------------------------
/// Pointers
/// ---------------------------------------------------------------------------

/// A word is a major pointer exactly when it is `is_pointer`, to the model
/// address of the header below it.
let absv_major (v: U64.t) (a: nat)
  : Lemma (absv v == M.VPtr (M.Major a) <==> (is_pointer v /\ U64.v v == pos a + 8))
  = base_facts ()

/// A word is a young pointer exactly when it is an aligned nursery offset
/// past a header (`GC.Gen.Base.is_minor_addr`, kept by `to_minor_offset`).
let absv_young (v: U64.t) (a: nat)
  : Lemma (absv v == M.VPtr (M.Young a) <==> (is_young_w v /\ U64.v v == 8 * a + 8))
  = base_facts ()

let young_is_minor (v: U64.t)
  : Lemma (requires is_young_w v) (ensures GB.is_minor_addr v /\ GB.to_minor_offset v == v)
  = GB.is_minor_addr_from_bounds v; GB.to_minor_offset_in_minor_range v

/// The header word of the block at `m` is the header of its object.
let hd_of_obj (m: nat{pos m + 8 < heap_size})
  : Lemma (hd_address (obj_of m) == hp m)
  = hd_address_pos (obj_of m)

/// A pointer to a block resolves to it, in both readings.
let resolve_block_bytes (g: heap) (a: nat)
  : Lemma (requires M.is_block (abs g) a /\ no_infix_block g)
          (ensures pos a + 8 < heap_size /\ M.resolve (abs g) a == Some a /\
                   resolve_object (obj_of a) g == obj_of a)
  = abs_is_block g a;
    resolve_non_infix (obj_of a) g

let tag_low_byte (v: U64.t) : Lemma (U64.v (getTag v) == U64.v v % 256)
  = getTag_spec v;
    FStar.UInt.logand_mask #64 (U64.v v) 8;
    assert_norm (pow2 8 - 1 == 255)

let wosize_high (v: U64.t) : Lemma (U64.v (getWosize v) == U64.v v / 1024)
  = getWosize_spec v;
    assert_norm (pow2 10 == 1024)

/// A pointer the model resolves through an infix header resolves, by
/// `resolve_object`, to the same closure: the infix header is the word
/// below the pointer, its tag the infix tag and its wosize the offset.
let resolve_infix_bytes (g: heap) (a o: nat)
  : Lemma (requires a + 1 < msize /\ ~(M.is_block (abs g) a) /\ M.resolve (abs g) a == Some o)
          (ensures pos a + 8 < heap_size /\ pos o + 8 < heap_size /\
                   is_infix (obj_of a) g /\ resolve_object (obj_of a) g == obj_of o)
  = base_facts ();
    let w = word g a in
    let k = a - o in
    assert (M.infix_hdr (absv w) == Some k);
    assert (M.is_block (abs g) o /\ o < a);
    msize_pos o;
    msize_pos (a + 1);
    hd_of_obj a;
    tag_low_byte w;
    wosize_high w;
    tag_of_object_spec (obj_of a) g;
    is_infix_spec (obj_of a) g;
    infix_tag_val ();
    wosize_of_object_spec (obj_of a) g;
    parent_closure_addr_nat_spec (obj_of a) g;
    assert (parent_closure_addr_nat (obj_of a) g == pos o + 8);
    resolve_infix_spec (obj_of a) g

/// ---------------------------------------------------------------------------
/// The walk tiles the model
/// ---------------------------------------------------------------------------

/// The walk positions are model words.
let walk_pos (g: heap) (p: hp_addr)
  : Lemma (requires reaches g zero_addr (U64.v p))
          (ensures U64.v p >= base /\ pos (mpos (U64.v p)) == U64.v p)
  = reaches_bounds g zero_addr (U64.v p); base_facts ()

let block_of_walk (g: heap) (p: hp_addr)
  : Lemma (requires reaches g zero_addr (U64.v p) /\ can_step g p)
          (ensures (let m = mpos (U64.v p) in
                    M.is_block (abs g) m /\ pos m == U64.v p /\
                    pos m + 8 * (M.wz_of (abs g) m + 1) == bnext g p))
  = walk_pos g p;
    let m = mpos (U64.v p) in
    msize_pos m;
    assert (hp m == p)

/// A block of the model is a block of the walk.
let abs_block_walk (g: heap) (o: nat)
  : Lemma (requires M.is_block (abs g) o)
          (ensures pos o < heap_size /\ reaches g zero_addr (pos o) /\ can_step g (hp o) /\
                   U64.v (hp o) == pos o /\ bnext g (hp o) == pos o + 8 * (M.wz_of (abs g) o + 1))
  = msize_pos o

let abs_uniq (g: heap) (o1 o2 w: nat)
  : Lemma (M.covers (abs g) o1 w /\ M.covers (abs g) o2 w ==> o1 == o2)
  = let h = abs g in
    if M.covers h o1 w && M.covers h o2 w && o1 <> o2 then begin
      abs_block_walk g o1;
      abs_block_walk g o2;
      if o1 < o2 then reaches_block_before g zero_addr (hp o1) (pos o2)
      else reaches_block_before g zero_addr (hp o2) (pos o1)
    end

let abs_cover (g: heap) (w: nat)
  : Lemma (requires reaches g zero_addr heap_size /\ w < msize)
          (ensures exists (o: nat). M.covers (abs g) o w)
  = msize_pos w;
    let p = block_at g zero_addr heap_size (pos w) in
    block_of_walk g p;
    let o = mpos (U64.v p) in
    let k = M.wz_of (abs g) o in
    assert (pos o <= pos w /\ pos w < pos o + 8 * (k + 1));
    assert (o <= w /\ w <= o + k);
    assert (M.covers (abs g) o w)

let abs_tiled (g: heap)
  : Lemma (requires reaches g zero_addr heap_size)
          (ensures M.tiled (abs g))
  = let h = abs g in
    base_facts ();
    let bnd (o: nat) : Lemma (M.is_block h o ==> o + M.wz_of h o < h.M.size)
      = if M.is_block h o then begin
          msize_pos o;
          assert (can_step g (hp o));
          msize_pos (o + M.wz_of h o)
        end in
    FStar.Classical.forall_intro bnd;
    let cov (w: nat) : Lemma (w < h.M.size ==> (exists (o: nat). M.covers h o w))
      = if w < h.M.size then abs_cover g w in
    FStar.Classical.forall_intro cov;
    FStar.Classical.forall_intro_3 (abs_uniq g)

let abs_well_formed (g: heap)
  : Lemma (requires reaches g zero_addr heap_size /\ no_infix_block g)
          (ensures M.well_formed (abs g))
  = abs_tiled g;
    let nt (o: nat) : Lemma (M.is_block (abs g) o ==> M.tag_of (abs g) o <> M.infix_tag)
      = if M.is_block (abs g) o then begin
          abs_is_block g o;
          abs_header g o;
          is_infix_spec (obj_of o) g;
          infix_tag_val ()
        end in
    FStar.Classical.forall_intro nt

/// ---------------------------------------------------------------------------
/// The representation, and its reads
/// ---------------------------------------------------------------------------

/// The canonical reading: `abs g` with the words outside fields read as 0
/// (header words, and the bytes of no block).  It agrees with `abs g`.
let rec fw_below (g: heap) (w n: nat) : bool =
  if n = 0 then false
  else (let o = n - 1 in o < w && on_walk g o && w <= o + U64.v (getWosize (word g o))) || fw_below g w (n - 1)

let is_fw (g: heap) (w: nat) : bool = fw_below g w w

let cabs_body (g: heap) (w: nat) : M.value = if is_fw g w then abs_body g w else M.VInt 0

let cabs (g: heap) : M.mheap = { M.size = msize; M.hd = abs_hd g; M.body = cabs_body g }

let fw_one (g: heap) (w o: nat)
  : Lemma ((o < w && on_walk g o && w <= o + U64.v (getWosize (word g o))) <==> (o < w /\ M.covers (abs g) o w))
  = msize_pos o

let rec fw_below_intro (g: heap) (w n o: nat)
  : Lemma (requires o < n /\ o < w /\ M.covers (abs g) o w) (ensures fw_below g w n) (decreases n)
  = fw_one g w o;
    if o = n - 1 then () else fw_below_intro g w (n - 1) o

let rec fw_below_elim (g: heap) (w n: nat)
  : Lemma (requires fw_below g w n) (ensures exists (o: nat). o < n /\ o < w /\ M.covers (abs g) o w)
          (decreases n)
  = let o = n - 1 in
    fw_one g w o;
    if o < w && on_walk g o && w <= o + U64.v (getWosize (word g o)) then ()
    else fw_below_elim g w (n - 1)

let fw_below_iff (g: heap) (w n: nat)
  : Lemma (fw_below g w n <==> (exists (o: nat). o < n /\ o < w /\ M.covers (abs g) o w))
  = FStar.Classical.move_requires (fw_below_elim g w) n;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (fw_below_intro g w n))

let is_fw_iff (g: heap) (w: nat) : Lemma (is_fw g w <==> R.field_word (abs g) w)
  = fw_below_iff g w w

let cabs_agree (g: heap) : Lemma (R.agree (cabs g) (abs g) /\ R.agree (abs g) (cabs g))
  = FStar.Classical.forall_intro (is_fw_iff g);
    R.agree_sym (cabs g) (abs g)

let cabs_canonical (g: heap) : Lemma (R.canonical (cabs g))
  = FStar.Classical.forall_intro (is_fw_iff g);
    let hd (o: nat) : Lemma (o >= msize ==> abs_hd g o == None) = msize_pos o in
    FStar.Classical.forall_intro hd;
    let bd (w: nat) : Lemma (~(R.field_word (cabs g) w) ==> cabs_body g w == M.VInt 0)
      = R.agree_field_word (cabs g) (abs g) w in
    FStar.Classical.forall_intro bd

/// The representation: `m` is the canonical reading of `g`, word by word.
/// Many byte heaps have one reading (the bytes below `zero_addr`, and the
/// bytes after the walk's end, are not read).
let brepr (m: M.mheap) (g: heap) : prop = R.heq m (cabs g)

let brepr_cabs (g: heap) : Lemma (brepr (cabs g) g) = ()

let brepr_agree (m: M.mheap) (g: heap)
  : Lemma (requires brepr m g) (ensures R.agree m (abs g) /\ R.canonical m)
  = cabs_agree g;
    cabs_canonical g;
    R.heq_agree m (cabs g);
    R.agree_trans m (cabs g) (abs g);
    R.heq_sym m (cabs g);
    R.canonical_heq (cabs g) m

let brepr_field (m: M.mheap) (g: heap) (o i: nat)
  : Lemma (requires R.agree m (abs g) /\ M.is_block m o /\ i < M.wz_of m o)
          (ensures read_field g o i == M.field m o i)
  = let w = o + 1 + i in
    assert (m.M.hd o == (abs g).M.hd o);
    assert (M.is_block (abs g) o /\ M.wz_of (abs g) o == M.wz_of m o);
    assert (M.covers (abs g) o w);
    assert (R.field_word (abs g) w);
    assert (m.M.body w == abs_body g w);
    msize_pos w

let brepr_reads (m: M.mheap) (g: heap)
  : Lemma (requires brepr m g)
          (ensures R.reads_model msize (read_hd g) (read_field g) m)
  = brepr_agree m g;
    let f (o i: nat) : Lemma (M.is_block m o /\ i < M.wz_of m o ==> read_field g o i == M.field m o i)
      = if M.is_block m o && i < M.wz_of m o then brepr_field m g o i in
    FStar.Classical.forall_intro_2 f;
    let h (o: nat) : Lemma (o < m.M.size ==> read_hd g o == m.M.hd o) = () in
    FStar.Classical.forall_intro h

/// ---------------------------------------------------------------------------
/// Nothing missing: the heap whose words are the model's
/// ---------------------------------------------------------------------------

/// The model heaps the byte heap represents: well formed, of its size, every
/// block with a field, every field a word.
[@@"opaque_to_smt"]
let brep_ok (m: M.mheap) : prop =
  M.well_formed m /\ m.M.size == msize /\
  (forall (o: nat). M.is_block m o ==> M.wz_of m o >= 1) /\
  (forall (w: nat). R.field_word m w ==> storable_w (m.M.body w))

let brep_ok_intro (m: M.mheap)
  : Lemma (requires M.well_formed m /\ m.M.size == msize /\
                    (forall (o: nat). M.is_block m o ==> M.wz_of m o >= 1) /\
                    (forall (w: nat). R.field_word m w ==> storable_w (m.M.body w)))
          (ensures brep_ok m)
  = reveal_opaque (`%brep_ok) (brep_ok m)

let brep_size (m: M.mheap) : Lemma (requires brep_ok m) (ensures m.M.size == msize)
  = reveal_opaque (`%brep_ok) (brep_ok m)

let brep_cover (m: M.mheap) (w: nat)
  : Lemma (requires brep_ok m /\ w < msize) (ensures exists (o: nat). M.covers m o w)
  = reveal_opaque (`%brep_ok) (brep_ok m)

let brep_uniq (m: M.mheap) (o1 o2 w: nat)
  : Lemma (requires brep_ok m /\ M.covers m o1 w /\ M.covers m o2 w) (ensures o1 == o2)
  = reveal_opaque (`%brep_ok) (brep_ok m)

let brep_block (m: M.mheap) (o: nat)
  : Lemma (requires brep_ok m /\ M.is_block m o)
          (ensures o + M.wz_of m o < msize /\ M.wz_of m o >= 1)
  = reveal_opaque (`%brep_ok) (brep_ok m)

let brep_store (m: M.mheap) (w: nat)
  : Lemma (requires brep_ok m /\ R.field_word m w) (ensures storable_w (m.M.body w))
  = reveal_opaque (`%brep_ok) (brep_ok m)

/// The block at `o`, of `wz` fields, steps to `o + wz + 1`.
let step_arith (o wz: nat)
  : Lemma (requires o + wz < msize /\ wz >= 1)
          (ensures pos o + 8 < heap_size /\ pos o + 8 * (wz + 1) <= heap_size /\
                   pos o + 8 * (wz + 1) == pos (o + wz + 1) /\ wz < pow2 54)
  = base_facts ()

/// The word at model address `j`: the header of a block, or the field's word.
let cword (m: M.mheap) (j: nat) : U64.t =
  if M.is_block m j then enc_hdr (M.hdr_of m j) else concv (m.M.body j)

let byte_of (v: U64.t) (k: nat{k < 8}) : U8.t =
  match k with
  | 0 -> uint64_to_uint8 v
  | 1 -> uint64_to_uint8 (U64.shift_right v 8ul)
  | 2 -> uint64_to_uint8 (U64.shift_right v 16ul)
  | 3 -> uint64_to_uint8 (U64.shift_right v 24ul)
  | 4 -> uint64_to_uint8 (U64.shift_right v 32ul)
  | 5 -> uint64_to_uint8 (U64.shift_right v 40ul)
  | 6 -> uint64_to_uint8 (U64.shift_right v 48ul)
  | 7 -> uint64_to_uint8 (U64.shift_right v 56ul)

let byte_of_k (v: U64.t)
  : Lemma (byte_of v 0 == uint64_to_uint8 v /\
           byte_of v 1 == uint64_to_uint8 (U64.shift_right v 8ul) /\
           byte_of v 2 == uint64_to_uint8 (U64.shift_right v 16ul) /\
           byte_of v 3 == uint64_to_uint8 (U64.shift_right v 24ul) /\
           byte_of v 4 == uint64_to_uint8 (U64.shift_right v 32ul) /\
           byte_of v 5 == uint64_to_uint8 (U64.shift_right v 40ul) /\
           byte_of v 6 == uint64_to_uint8 (U64.shift_right v 48ul) /\
           byte_of v 7 == uint64_to_uint8 (U64.shift_right v 56ul))
  = ()

let conc_byte (m: M.mheap) (i: nat{i < heap_size}) : U8.t =
  if i < base then 0uy else byte_of (cword m ((i - base) / 8)) ((i - base) % 8)

let conc (m: M.mheap) : heap = Seq.init heap_size (conc_byte m)

let byte_pos (j k: nat)
  : Lemma (requires k < 8) (ensures (pos j + k - base) / 8 == j /\ (pos j + k - base) % 8 == k)
  = FStar.Math.Lemmas.lemma_div_plus k j 8;
    FStar.Math.Lemmas.small_div k 8;
    FStar.Math.Lemmas.lemma_mod_plus k j 8;
    FStar.Math.Lemmas.small_mod k 8

let hp_v (j: nat{pos j < heap_size}) : Lemma (U64.v (hp j) == pos j) = ()

let conc_index (m: M.mheap) (j: nat) (k: nat)
  : Lemma (requires pos j + k < heap_size /\ k < 8)
          (ensures Seq.index (conc m) (pos j + k) == byte_of (cword m j) k)
  = byte_pos j k

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let conc_word (m: M.mheap) (j: nat{j < msize})
  : Lemma (word (conc m) j == cword m j)
  = msize_pos j;
    pos_aligned j;
    let g = conc m in
    hp_v j;
    read_word_spec g (hp j);
    conc_index m j 0; conc_index m j 1; conc_index m j 2; conc_index m j 3;
    conc_index m j 4; conc_index m j 5; conc_index m j 6; conc_index m j 7;
    byte_of_k (cword m j);
    combine_decompose_identity (cword m j)
#pop-options

/// The header word of a block decodes to its header.
let conc_hdr (m: M.mheap) (o: nat)
  : Lemma (requires brep_ok m /\ M.is_block m o)
          (ensures abs_hdr (word (conc m) o) == M.hdr_of m o)
  = brep_block m o;
    step_arith o (M.wz_of m o);
    conc_word m o;
    abs_hdr_enc (M.hdr_of m o)

let tiled_uniq (m: M.mheap) (o1 o2 w: nat)
  : Lemma (requires M.tiled m /\ M.covers m o1 w /\ M.covers m o2 w) (ensures o1 == o2) = ()

let tiled_cover (m: M.mheap) (w: nat)
  : Lemma (requires M.tiled m /\ w < m.M.size) (ensures exists (o: nat). M.covers m o w) = ()

let prev_arith (p wz o: nat)
  : Lemma (requires o > 0 /\ p <= o - 1 /\ o - 1 <= p + wz /\ ~(p + wz >= o)) (ensures p + wz + 1 == o /\ p < o)
  = ()

/// The block before `o` ends just before it.
let prev_block (m: M.mheap) (o: nat)
  : Lemma (requires brep_ok m /\ M.is_block m o /\ o > 0)
          (ensures exists (p: nat). M.is_block m p /\ p < o /\ p + M.wz_of m p + 1 == o)
  = brep_size m;
    brep_cover m (o - 1);
    let p = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun p -> M.covers m p (o - 1)) in
    let wz = M.wz_of m p in
    if p + wz >= o then brep_uniq m p o o
    else prev_arith p wz o

let bnext_eq (g: heap) (o: nat{pos o < heap_size}) (wz: nat)
  : Lemma (requires U64.v (getWosize (read_word g (hp o))) == wz)
          (ensures bnext g (hp o) == pos o + 8 * (wz + 1) /\ U64.v (hp o) == pos o)
  = ()

let walk_step_facts (g: heap) (o: nat{pos o < heap_size}) (wz: nat)
  : Lemma (requires U64.v (getWosize (read_word g (hp o))) == wz /\ o + wz < msize /\ wz >= 1)
          (ensures can_step g (hp o) /\ bnext g (hp o) == pos (o + wz + 1) /\ U64.v (hp o) == pos o)
  = bnext_eq g o wz; step_arith o wz

let rec rep_walk (m: M.mheap) (o: nat)
  : Lemma (requires brep_ok m /\ M.is_block m o)
          (ensures pos o < heap_size /\
                   reaches (conc m) zero_addr (pos o) /\ can_step (conc m) (hp o) /\
                   bnext (conc m) (hp o) == pos (o + M.wz_of m o + 1))
          (decreases o)
  = brep_block m o;
    let wz = M.wz_of m o in
    step_arith o wz;
    let g = conc m in
    conc_hdr m o;
    assert (pos o < heap_size);
    walk_step_facts g o wz;
    if o = 0 then reaches_refl g zero_addr
    else begin
      prev_block m o;
      let p = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun p -> M.is_block m p /\ p < o /\ p + M.wz_of m p + 1 == o) in
      rep_walk m p;
      hp_v p;
      reaches_snoc g zero_addr (hp p)
    end

let rep_on_walk (m: M.mheap) (q: nat)
  : Lemma (requires brep_ok m /\ q < msize)
          (ensures on_walk (conc m) q == M.is_block m q)
  = msize_pos q;
    let g = conc m in
    if M.is_block m q then rep_walk m q
    else if on_walk g q then begin
      brep_cover m q;
      let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers m o q) in
      assert (o <> q);
      assert (o < q /\ q <= o + M.wz_of m o);
      rep_walk m o;
      hp_v o;
      assert (reaches g zero_addr (pos q));
      assert (pos o < pos q);
      reaches_block_before g zero_addr (hp o) (pos q);
      assert (pos (o + M.wz_of m o + 1) <= pos q)
    end

let conc_agree (m: M.mheap)
  : Lemma (requires brep_ok m) (ensures R.agree m (abs (conc m)))
  = let g = conc m in
    brep_size m;
    let hd (o: nat) : Lemma (o < msize ==> m.M.hd o == abs_hd g o)
      = if o < msize then begin
          rep_on_walk m o;
          if M.is_block m o then conc_hdr m o
        end in
    FStar.Classical.forall_intro hd;
    let bd (w: nat) : Lemma (R.field_word (abs g) w ==> m.M.body w == abs_body g w)
      = if FStar.IndefiniteDescription.strong_excluded_middle (R.field_word (abs g) w) then begin
          let o = FStar.IndefiniteDescription.indefinite_description_ghost nat
                    (fun o -> M.covers (abs g) o w /\ o < w) in
          assert (M.covers m o w);
          if M.is_block m w then brep_uniq m o w w;
          brep_block m o;
          conc_word m w;
          brep_store m w;
          absv_concv (m.M.body w)
        end in
    FStar.Classical.forall_intro bd

let conc_repr (m: M.mheap)
  : Lemma (requires brep_ok m /\ R.canonical m) (ensures brepr m (conc m))
  = let g = conc m in
    conc_agree m;
    cabs_agree g;
    cabs_canonical g;
    R.agree_sym (cabs g) (abs g);
    R.agree_trans m (abs g) (cabs g);
    R.agree_canonical m (cabs g)
