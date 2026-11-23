/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWAlloc - first-fit from the bottom block, as a model update
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  The witness runs keep one large free block at the bottom
/// of the heap (model address 0, its object address the free list's head).
/// First-fit allocates from it right-justified (akhil's `alloc_from_block`):
/// the block keeps its address and its link, shrinks by the request and a
/// header, and the new block sits just above it (`split`).  The free list's
/// head is unchanged.

module GC.Spec.Top.FFWAlloc

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFWWords
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module SA = GC.Spec.Allocator
module AP = GC.Spec.Allocator.Phase
module AC = GC.Spec.Allocator.Cursor
module ALC = GC.Spec.Allocator.Lemmas
module ALH = GC.Spec.Allocator.Lemmas.Header
module Header = GC.Lib.Header

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Headers
/// ---------------------------------------------------------------------------

/// A header word is the encoding of the header it reads as.
let enc_of (v: U64.t) (h: M.header) : Lemma (requires abs_hdr v == h) (ensures enc_hdr h == v)
  = enc_abs_hdr v

/// A header encodes to a word of its size.
let enc_wz (h: M.header) : Lemma (requires h.M.wz < pow2 54) (ensures U64.v (getWosize (enc_hdr h)) == h.M.wz)
  = abs_hdr_enc h

/// akhil's header of a size, colour and tag.
#push-options "--z3rlimit 30"
let make_header_abs (w: nat{w < pow2 54 /\ w < pow2 64}) (c: color) (t: U64.t{U64.v t < 256})
  : Lemma (ensures abs_hdr (SA.make_header (U64.uint_to_t w) c t) == ({ M.wz = w; M.tag = U64.v t; M.col = abs_col c }))
  = FStar.Math.Lemmas.pow2_lt_compat 64 54;
    let ww = U64.uint_to_t w in
    ALC.make_header_getColor ww c t;
    Header.pack_unpack_color c;
    getColor_raw (SA.make_header ww c t);
    ALH.make_header_getWosize ww c t;
    ALH.make_header_getTag ww c t
#pop-options

/// ---------------------------------------------------------------------------
/// The model of a split
/// ---------------------------------------------------------------------------

/// The free block at 0, of `f` fields.
let head_ok (m: M.mheap) (f: nat) : prop =
  brep_ok m /\ R.canonical m /\ m.M.hd 0 == Some ({ M.wz = f; M.tag = 0; M.col = M.Blue })

let free_hdr (w: nat) : M.header = { M.wz = w; M.tag = 0; M.col = M.Blue }

/// The block at 0 shrinks to `f - sz - 1` fields; the new block of `sz`
/// fields sits at `f - sz`, its header word no longer a field.
[@@"opaque_to_smt"]
let split (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) : M.mheap =
  { m with
    M.hd = (fun (x: nat) ->
      if x = 0 then Some (free_hdr (f - sz - 1))
      else if x = f - sz then Some ({ M.wz = sz; M.tag = tag; M.col = col })
      else m.M.hd x);
    M.body = (fun (w: nat) -> if w = f - sz then M.VInt 0 else m.M.body w) }

let split_def (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour)
  : Lemma ((split m f sz tag col).M.size == m.M.size /\
           (forall (x: nat). (split m f sz tag col).M.hd x ==
              (if x = 0 then Some (free_hdr (f - sz - 1))
               else if x = f - sz then Some ({ M.wz = sz; M.tag = tag; M.col = col })
               else m.M.hd x)) /\
           (forall (w: nat). (split m f sz tag col).M.body w == (if w = f - sz then M.VInt 0 else m.M.body w)))
  = reveal_opaque (`%split) (split m f sz tag col)

/// Every other block of `m` lies past the block at 0.
let past_head (m: M.mheap) (f: nat) (x: nat)
  : Lemma (requires head_ok m f /\ M.is_block m x /\ x <> 0) (ensures x > f)
  = brep_size m;
    brep_block m 0;
    if x <= f then brep_uniq m 0 x x

/// A word covered in `m` by a block other than 0 lies past `f`.
let past_head_w (m: M.mheap) (f: nat) (x w: nat)
  : Lemma (requires head_ok m f /\ M.covers m x w /\ x <> 0) (ensures w > f)
  = past_head m f x

#push-options "--z3rlimit 40"
let split_covers (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (x w: nat)
  : Lemma (requires head_ok m f /\ sz >= 1)
          (ensures (let m' = split m f sz tag col in
                    M.covers m' x w <==>
                      (if x = 0 then w <= f - sz - 1
                       else if x = f - sz then f - sz <= w /\ w <= f
                       else M.covers m x w)))
  = split_def m f sz tag col;
    brep_size m;
    brep_block m 0;
    if x <> 0 && x <> f - sz && M.is_block m x then past_head m f x
#pop-options

let split_fit (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (o: nat)
  : Lemma (requires head_ok m f /\ sz >= 1 /\ tag <> M.infix_tag)
          (ensures (let m' = split m f sz tag col in
                    M.is_block m' o ==> o + M.wz_of m' o < m'.M.size /\ M.wz_of m' o >= 1 /\
                                         M.tag_of m' o <> M.infix_tag))
  = split_def m f sz tag col;
    brep_size m; brep_block m 0;
    let m' = split m f sz tag col in
    if M.is_block m' o && o <> 0 && o <> f - sz then begin
      brep_block m o;
      reveal_opaque (`%brep_ok) (brep_ok m)
    end

let split_cov (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (w: nat)
  : Lemma (requires head_ok m f /\ sz >= 1)
          (ensures (let m' = split m f sz tag col in w < m'.M.size ==> (exists (o: nat). M.covers m' o w)))
  = split_def m f sz tag col;
    brep_size m; brep_block m 0;
    if w < msize then begin
      if w <= f - sz - 1 then begin split_covers m f sz tag col 0 w; assert (M.covers (split m f sz tag col) 0 w) end
      else if w <= f then begin
        split_covers m f sz tag col (f - sz) w; assert (M.covers (split m f sz tag col) (f - sz) w)
      end
      else begin
        brep_cover m w;
        let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers m o w) in
        assert (o <> 0);
        past_head m f o;
        split_covers m f sz tag col o w;
        assert (M.covers (split m f sz tag col) o w)
      end
    end

let split_uq (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (o1 o2 w: nat)
  : Lemma (requires head_ok m f /\ sz >= 1)
          (ensures (let m' = split m f sz tag col in M.covers m' o1 w /\ M.covers m' o2 w ==> o1 == o2))
  = split_def m f sz tag col;
    split_covers m f sz tag col o1 w;
    split_covers m f sz tag col o2 w;
    let m' = split m f sz tag col in
    if M.covers m' o1 w && M.covers m' o2 w && o1 <> o2 then begin
      if o1 <> 0 && o1 <> f - sz then past_head_w m f o1 w;
      if o2 <> 0 && o2 <> f - sz then past_head_w m f o2 w;
      if o1 <> 0 && o1 <> f - sz && o2 <> 0 && o2 <> f - sz then brep_uniq m o1 o2 w
    end

let split_fw (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (w: nat)
  : Lemma (requires head_ok m f /\ sz >= 1 /\ R.field_word (split m f sz tag col) w)
          (ensures R.field_word m w /\ w <> f - sz)
  = split_def m f sz tag col;
    let m' = split m f sz tag col in
    let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers m' o w /\ o < w) in
    split_covers m f sz tag col o w;
    brep_size m; brep_block m 0;
    if o = 0 || o = f - sz then begin
      assert (M.covers m 0 w);
      assert (R.field_word m w)
    end
    else begin
      assert (M.covers m o w);
      past_head m f o;
      assert (R.field_word m w)
    end

let split_st (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (w: nat)
  : Lemma (requires head_ok m f /\ sz >= 1)
          (ensures R.field_word (split m f sz tag col) w ==> storable_w ((split m f sz tag col).M.body w))
  = split_def m f sz tag col;
    if FStar.IndefiniteDescription.strong_excluded_middle (R.field_word (split m f sz tag col) w) then begin
      split_fw m f sz tag col w;
      brep_store m w
    end

let split_nf (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (w: nat)
  : Lemma (requires head_ok m f /\ sz >= 1)
          (ensures ~(R.field_word (split m f sz tag col) w) ==> (split m f sz tag col).M.body w == M.VInt 0)
  = split_def m f sz tag col;
    let m' = split m f sz tag col in
    brep_size m; brep_block m 0;
    if w <> f - sz && not (FStar.IndefiniteDescription.strong_excluded_middle (R.field_word m' w)) then begin
      if w = 0 then ()
      else if w <= f then begin
        (if w <= f - sz - 1 then split_covers m f sz tag col 0 w else split_covers m f sz tag col (f - sz) w);
        if w <= f - sz - 1 then assert (M.covers m' 0 w) else assert (M.covers m' (f - sz) w)
      end
      else begin
        let nfm () : Lemma (requires R.field_word m w) (ensures R.field_word m' w)
          = let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers m o w /\ o < w) in
            if o = 0 then assert False
            else begin past_head m f o; split_covers m f sz tag col o w end in
        FStar.Classical.move_requires nfm ()
      end
    end

let split_size (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour)
  : Lemma (requires head_ok m f) (ensures (split m f sz tag col).M.size == msize)
  = split_def m f sz tag col; brep_size m

let split_past (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour) (o: nat)
  : Lemma (requires head_ok m f)
          (ensures o >= (split m f sz tag col).M.size ==> (split m f sz tag col).M.hd o == None)
  = split_def m f sz tag col; brep_size m; brep_block m 0

let wf_of (h: M.mheap)
  : Lemma (requires (forall (o: nat). M.is_block h o ==> o + M.wz_of h o < h.M.size /\ M.wz_of h o >= 1 /\
                                         M.tag_of h o <> M.infix_tag) /\
                    (forall (w: nat). w < h.M.size ==> (exists (o: nat). M.covers h o w)) /\
                    (forall (o1 o2 w: nat). M.covers h o1 w /\ M.covers h o2 w ==> o1 == o2))
          (ensures M.well_formed h /\ (forall (o: nat). M.is_block h o ==> M.wz_of h o >= 1))
  = ()

let split_ok (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour)
  : Lemma (requires head_ok m f /\ sz >= 1 /\ tag <> M.infix_tag)
          (ensures brep_ok (split m f sz tag col) /\ R.canonical (split m f sz tag col))
  = let m' = split m f sz tag col in
    FStar.Classical.forall_intro (split_fit m f sz tag col);
    FStar.Classical.forall_intro (split_cov m f sz tag col);
    FStar.Classical.forall_intro_3 (split_uq m f sz tag col);
    FStar.Classical.forall_intro (split_st m f sz tag col);
    FStar.Classical.forall_intro (split_nf m f sz tag col);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (split_past m f sz tag col));
    split_size m f sz tag col;
    wf_of m';
    brep_ok_intro m'

/// ---------------------------------------------------------------------------
/// The bytes
/// ---------------------------------------------------------------------------

/// The new block's colour, as the model's colour rule gives it.
let colour_rule (ph: T.phase U64.t) (o: nat)
  : Lemma (requires pos o < pow2 64)
          (ensures abs_col (GC.Spec.Phase.allocation_color (gph ph) (U64.uint_to_t (pos o))) == T.colour_at ffk ph o)
  = ()

/// The head block's header word.
let head_word (g: heap) (m: M.mheap) (f: nat)
  : Lemma (requires brepr m g /\ head_ok m f)
          (ensures pos 0 + 8 < heap_size /\ f < msize /\ f < pow2 54 /\
                   read_word g (hp 0) == enc_hdr (free_hdr f) /\
                   U64.v (getWosize (read_word g (hp 0))) == f)
  = base_facts ();
    brep_size m; brep_block m 0; msize_pos 0;
    words_of_heq g m 0;
    enc_wz (free_hdr f)

/// The words after the split.
#push-options "--z3rlimit 40"
let split_word (g g2: heap) (m: M.mheap) (f: nat) (sz: nat{sz + 2 <= f}) (tag: M.tag_t) (col: M.colour)
               (rh ah: U64.t) (j: nat)
  : Lemma (requires head_ok m f /\ sz >= 1 /\ f < msize /\ j < msize /\
                    word g j == cword m j /\
                    word g2 j == (if j = 0 then rh else if j = f - sz then ah else word g j) /\
                    abs_hdr rh == free_hdr (f - sz - 1) /\
                    abs_hdr ah == ({ M.wz = sz; M.tag = tag; M.col = col }))
          (ensures word g2 j == cword (split m f sz tag col) j)
  = split_def m f sz tag col;
    brep_size m;
    if j = 0 then enc_of rh (free_hdr (f - sz - 1))
    else if j = f - sz then enc_of ah ({ M.wz = sz; M.tag = tag; M.col = col })
    else begin
      assert (M.is_block (split m f sz tag col) j == M.is_block m j);
      assert (M.hdr_of (split m f sz tag col) j == M.hdr_of m j);
      assert ((split m f sz tag col).M.body j == m.M.body j)
    end
#pop-options

/// The heap first-fit writes: the two headers.
let rh_of (f sz: nat) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  if f >= sz + 1 && f - sz - 1 < pow2 54 then SA.make_header (U64.uint_to_t (f - sz - 1)) Header.Blue 0UL else 0UL

let ah_of (sz: nat) (col: color) (tag: M.tag_t) : U64.t =
  assert_norm (256 < pow2 64);
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  if sz < pow2 54 then SA.make_header (U64.uint_to_t sz) col (U64.uint_to_t tag) else 0UL

let written (g: heap) (f sz: nat) (col: color) (tag: M.tag_t) : GTot heap =
  if f >= sz && pos (f - sz) < heap_size then
    write_word (write_word g (hp 0) (rh_of f sz)) (hp (f - sz)) (ah_of sz col tag)
  else g

/// akhil's search takes the head.
#push-options "--z3rlimit 40"
let search_head (ph: T.phase U64.t) (g: heap) (fp: U64.t) (m: M.mheap) (f: nat) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires pos 0 < heap_size /\ U64.v (getWosize (read_word g (hp 0))) == f /\ f < msize /\
                    sz + 2 <= f /\ U64.v fp == base + 8)
          (ensures (let obj : obj_addr = fp in
                    let r = AP.alloc_at (gph ph) g fp sz (tg tag) in
                    let col = SA.alloc_color (gph ph) g obj sz in
                    let next = SA.spec_next_fp g obj in
                    r.SA.heap_out == fst (SA.alloc_from_block g obj sz col (tg tag) next) /\
                    r.SA.fp_out == fp /\ U64.v r.SA.obj_out == base + 8 + 8 * (f - sz)))
  = base_facts ();
    let obj : obj_addr = fp in
    hd_address_spec obj;
    U64.v_inj (hd_address obj) (hp 0);
    msize_pos (f - sz);
    SA.alloc_search_found_head g fp 0UL fp sz heap_words (gph ph) (tg tag)
#pop-options

/// It splits the head.
#push-options "--z3rlimit 40"
let block_split (g: heap) (fp: U64.t) (m: M.mheap) (f: nat) (sz: M.size_t) (col: color) (tag: M.tag_t) (next: U64.t)
  : Lemma (requires pos 0 < heap_size /\ U64.v (getWosize (read_word g (hp 0))) == f /\ f < msize /\
                    sz + 2 <= f /\ U64.v fp == base + 8)
          (ensures (let obj : obj_addr = fp in
                    pos (f - sz) < heap_size /\
                    fst (SA.alloc_from_block g obj sz col (tg tag) next) == written g f sz col tag))
  = base_facts ();
    let obj : obj_addr = fp in
    hd_address_spec obj;
    U64.v_inj (hd_address obj) (hp 0);
    msize_pos (f - sz);
    SA.alloc_from_block_split_normal g obj sz next col (tg tag);
    U64.v_inj (U64.uint_to_t (U64.v (hd_address obj) + (f - sz) * 8)) (hp (f - sz));
    assert_norm (256 < pow2 64);
    U64.v_inj (tg tag) (U64.uint_to_t tag)
#pop-options

/// The colour akhil gives.
let alloc_col (ph: T.phase U64.t) (g: heap) (fp: U64.t) (m: M.mheap) (f: nat) (sz: M.size_t)
  : Lemma (requires pos 0 < heap_size /\ U64.v (getWosize (read_word g (hp 0))) == f /\ f < msize /\
                    sz + 2 <= f /\ U64.v fp == base + 8)
          (ensures pos (f - sz) < pow2 64 /\
                   SA.alloc_color (gph ph) g (fp <: obj_addr) sz ==
                   GC.Spec.Phase.allocation_color (gph ph) (U64.uint_to_t (pos (f - sz))))
  = base_facts ();
    let obj : obj_addr = fp in
    hd_address_spec obj;
    U64.v_inj (hd_address obj) (hp 0);
    msize_pos (f - sz)

/// A write at one model address keeps the word at another.
let rw_other (g: heap) (i j: nat) (v: U64.t)
  : Lemma (requires pos i < heap_size /\ pos j < heap_size /\ i <> j)
          (ensures read_word (write_word g (hp i) v) (hp j) == read_word g (hp j))
  = hp_v i; hp_v j;
    read_write_different g (hp i) (hp j) v

let written_word (g: heap) (f sz: nat) (col: color) (tag: M.tag_t) (j: nat)
  : Lemma (requires f >= sz /\ pos (f - sz) < heap_size /\ j < msize)
          (ensures word (written g f sz col tag) j ==
                   (if j = 0 then (if f - sz = 0 then ah_of sz col tag else rh_of f sz)
                    else if j = f - sz then ah_of sz col tag else word g j))
  = msize_pos j; base_facts ();
    let g1 = write_word g (hp 0) (rh_of f sz) in
    read_write_same g1 (hp (f - sz)) (ah_of sz col tag);
    read_write_same g (hp 0) (rh_of f sz);
    if j <> f - sz then rw_other g1 (f - sz) j (ah_of sz col tag);
    if j <> 0 then rw_other g 0 j (rh_of f sz);
    if f - sz <> 0 && j = 0 then rw_other g1 (f - sz) 0 (ah_of sz col tag)

/// The words after the split.
#push-options "--z3rlimit 40"
let alloc_word (g: heap) (m: M.mheap) (f: nat) (sz: M.size_t) (col: color) (tag: M.tag_t) (j: nat)
  : Lemma (requires brepr m g /\ head_ok m f /\ sz + 2 <= f /\ j < msize /\ tag <> M.infix_tag)
          (ensures word (written g f sz col tag) j == cword (split m f sz tag (abs_col col)) j)
  = base_facts ();
    head_word g m f;
    words_of_heq g m j;
    msize_pos (f - sz);
    written_word g f sz col tag j;
    assert_norm (256 < pow2 64);
    make_header_abs (f - sz - 1) Header.Blue 0UL;
    make_header_abs sz col (U64.uint_to_t tag);
    split_word g (written g f sz col tag) m f sz tag (abs_col col) (rh_of f sz) (ah_of sz col tag) j
#pop-options

let fp_obj (fp: U64.t)
  : Lemma (requires U64.v fp == base + 8) (ensures U64.v fp >= 8 /\ U64.v fp < heap_size /\ U64.v fp % 8 == 0)
  = base_facts ()

let maddr_of (x: U64.t) (k: nat)
  : Lemma (requires U64.v x == base + 8 + 8 * k) (ensures maddr x == k /\ x <> 0UL)
  = base_facts ()

/// The words of the result.
let alloc_repr (g: heap) (m: M.mheap) (f: nat) (sz: M.size_t) (col: color) (tag: M.tag_t)
  : Lemma (requires brepr m g /\ head_ok m f /\ sz + 2 <= f /\ tag <> M.infix_tag)
          (ensures brepr (split m f sz tag (abs_col col)) (written g f sz col tag))
  = split_ok m f sz tag (abs_col col);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (alloc_word g m f sz col tag));
    heq_of_words (written g f sz col tag) (split m f sz tag (abs_col col))

/// **First-fit from the bottom block.**
#push-options "--z3rlimit 40"
let ffalloc_head (ph: T.phase U64.t) (h: heap) (s: ffst) (m: M.mheap) (f: nat) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires brepr m h /\ head_ok m f /\ sz + 2 <= f /\ U64.v s.fp == base + 8 /\ tag <> M.infix_tag)
          (ensures (let (h', s', r) = ffalloc ph h s sz tag in
                    r == T.Ok (f - sz) /\ s'.fp == s.fp /\
                    brepr (split m f sz tag (T.colour_at ffk ph (f - sz))) h'))
  = let g = gl h s in
    cabs_set_low h s.lo;
    fp_obj s.fp;
    let obj : obj_addr = s.fp in
    let col = SA.alloc_color (gph ph) g obj sz in
    head_word g m f;
    search_head ph g s.fp m f sz tag;
    block_split g s.fp m f sz col tag (SA.spec_next_fp g obj);
    alloc_col ph g s.fp m f sz;
    colour_rule ph (f - sz);
    alloc_repr g m f sz col tag;
    let r = ffres ph h s sz tag in
    maddr_of r.SA.obj_out (f - sz)
#pop-options
