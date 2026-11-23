/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWModel - model updates that keep the shape, and one write
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  The witness runs' model heaps change, between steps, by
/// updates that keep every block where it is with its size: a header's
/// colour or tag (the mark, the sweep), a field (the program, the free
/// list's links).  They keep the heap one the byte heap can represent
/// (`same_shape_ok`).  One word written to the byte heap is the model update
/// that changes that word (`write1_repr`).

module GC.Spec.Top.FFWModel

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.FFWWords
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// `m'` has the blocks of `m`, with their sizes; its other words are `m`'s.
let same_shape (m m': M.mheap) : prop =
  m'.M.size == m.M.size /\
  (forall (x: nat). Some? (m'.M.hd x) == Some? (m.M.hd x)) /\
  (forall (x: nat). M.is_block m' x == M.is_block m x /\ M.wz_of m' x == M.wz_of m x /\
                    (M.is_block m x ==> M.tag_of m' x <> M.infix_tag)) /\
  (forall (w: nat). R.field_word m w ==> storable_w (m'.M.body w)) /\
  (forall (w: nat). ~(R.field_word m w) ==> m'.M.body w == m.M.body w)

let shape_covers (m m': M.mheap) (x w: nat)
  : Lemma (requires same_shape m m') (ensures M.covers m' x w == M.covers m x w)
  = ()

let shape_fw (m m': M.mheap) (w: nat)
  : Lemma (requires same_shape m m') (ensures R.field_word m' w <==> R.field_word m w)
  = FStar.Classical.forall_intro (fun (x: nat) -> shape_covers m m' x w)

let shape_fit (m m': M.mheap) (o: nat)
  : Lemma (requires same_shape m m' /\ brep_ok m)
          (ensures M.is_block m' o ==> o + M.wz_of m' o < m'.M.size /\ M.wz_of m' o >= 1 /\
                                      M.tag_of m' o <> M.infix_tag)
  = brep_size m;
    if M.is_block m' o then brep_block m o

let shape_cov (m m': M.mheap) (w: nat)
  : Lemma (requires same_shape m m' /\ brep_ok m)
          (ensures w < m'.M.size ==> (exists (o: nat). M.covers m' o w))
  = brep_size m;
    if w < msize then begin
      brep_cover m w;
      let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers m o w) in
      shape_covers m m' o w
    end

let shape_uq (m m': M.mheap) (o1 o2 w: nat)
  : Lemma (requires same_shape m m' /\ brep_ok m)
          (ensures M.covers m' o1 w /\ M.covers m' o2 w ==> o1 == o2)
  = shape_covers m m' o1 w; shape_covers m m' o2 w;
    if M.covers m o1 w && M.covers m o2 w then brep_uniq m o1 o2 w

let shape_st (m m': M.mheap) (w: nat)
  : Lemma (requires same_shape m m')
          (ensures R.field_word m' w ==> storable_w (m'.M.body w))
  = shape_fw m m' w

let shape_nf (m m': M.mheap) (w: nat)
  : Lemma (requires same_shape m m' /\ R.canonical m)
          (ensures ~(R.field_word m' w) ==> m'.M.body w == M.VInt 0)
  = shape_fw m m' w

let shape_past (m m': M.mheap) (o: nat)
  : Lemma (requires same_shape m m' /\ R.canonical m) (ensures o >= m'.M.size ==> m'.M.hd o == None)
  = ()

let wf_of (h: M.mheap)
  : Lemma (requires (forall (o: nat). M.is_block h o ==> o + M.wz_of h o < h.M.size /\ M.wz_of h o >= 1 /\
                                         M.tag_of h o <> M.infix_tag) /\
                    (forall (w: nat). w < h.M.size ==> (exists (o: nat). M.covers h o w)) /\
                    (forall (o1 o2 w: nat). M.covers h o1 w /\ M.covers h o2 w ==> o1 == o2))
          (ensures M.well_formed h /\ (forall (o: nat). M.is_block h o ==> M.wz_of h o >= 1))
  = ()

/// **A same-shape update keeps the heap representable.**
let same_shape_ok (m m': M.mheap)
  : Lemma (requires same_shape m m' /\ brep_ok m /\ R.canonical m)
          (ensures brep_ok m' /\ R.canonical m')
  = brep_size m;
    FStar.Classical.forall_intro (shape_fit m m');
    FStar.Classical.forall_intro (shape_cov m m');
    FStar.Classical.forall_intro_3 (shape_uq m m');
    FStar.Classical.forall_intro (shape_st m m');
    FStar.Classical.forall_intro (shape_nf m m');
    FStar.Classical.forall_intro (shape_past m m');
    wf_of m';
    brep_ok_intro m'

/// Representable, sealed (its canonical clause quantifies over the heap's
/// words; the runs carry it as an atom).
[@@"opaque_to_smt"]
let okm (m: M.mheap) : prop = brep_ok m /\ R.canonical m

let okm_def (m: M.mheap) : Lemma (okm m <==> brep_ok m /\ R.canonical m) = reveal_opaque (`%okm) (okm m)

/// ---------------------------------------------------------------------------
/// The updates
/// ---------------------------------------------------------------------------

/// A header replaced by one of the same size.
let rehd (m: M.mheap) (o: nat) (h: M.header) : M.mheap =
  { m with M.hd = (fun (x: nat) -> if x = o then Some h else m.M.hd x) }

let rehd_covers (m: M.mheap) (o: nat) (h: M.header) (x w: nat)
  : Lemma (requires M.is_block m o /\ h.M.wz == M.wz_of m o)
          (ensures M.covers (rehd m o h) x w == M.covers m x w)
  = ()

let rehd_st (m: M.mheap) (o: nat) (h: M.header) (w: nat)
  : Lemma (requires brep_ok m /\ M.is_block m o /\ h.M.wz == M.wz_of m o)
          (ensures R.field_word m w ==> storable_w ((rehd m o h).M.body w))
  = if FStar.IndefiniteDescription.strong_excluded_middle (R.field_word m w) then brep_store m w

let brep_tag (m: M.mheap) (x: nat)
  : Lemma (requires brep_ok m) (ensures M.is_block m x ==> M.tag_of m x <> M.infix_tag)
  = reveal_opaque (`%brep_ok) (brep_ok m)

let rehd_hd (m: M.mheap) (o: nat) (h: M.header) (x: nat)
  : Lemma (requires brep_ok m /\ M.is_block m o /\ h.M.wz == M.wz_of m o /\ h.M.tag <> M.infix_tag)
          (ensures Some? ((rehd m o h).M.hd x) == Some? (m.M.hd x) /\
                   M.is_block (rehd m o h) x == M.is_block m x /\ M.wz_of (rehd m o h) x == M.wz_of m x /\
                   (M.is_block m x ==> M.tag_of (rehd m o h) x <> M.infix_tag))
  = brep_tag m x

let rehd_shape (m: M.mheap) (o: nat) (h: M.header)
  : Lemma (requires brep_ok m /\ M.is_block m o /\ h.M.wz == M.wz_of m o /\ h.M.tag <> M.infix_tag)
          (ensures same_shape m (rehd m o h))
  = FStar.Classical.forall_intro (rehd_hd m o h);
    FStar.Classical.forall_intro (rehd_st m o h)

/// A field word set to a value.
let setb (m: M.mheap) (w: nat) (v: M.value) : M.mheap =
  { m with M.body = (fun (k: nat) -> if k = w then v else m.M.body k) }

let setb_st (m: M.mheap) (w: nat) (v: M.value) (k: nat)
  : Lemma (requires brep_ok m /\ storable_w v)
          (ensures R.field_word m k ==> storable_w ((setb m w v).M.body k))
  = if k <> w && FStar.IndefiniteDescription.strong_excluded_middle (R.field_word m k) then brep_store m k

let setb_shape (m: M.mheap) (w: nat) (v: M.value)
  : Lemma (requires brep_ok m /\ R.field_word m w /\ storable_w v)
          (ensures same_shape m (setb m w v))
  = FStar.Classical.forall_intro (brep_tag m);
    FStar.Classical.forall_intro (setb_st m w v)

/// Recolouring keeps the shape.
let recol_st (m: M.mheap) (o: nat) (c: M.colour) (k: nat)
  : Lemma (requires brep_ok m) (ensures R.field_word m k ==> storable_w ((M.set_col m o c).M.body k))
  = if FStar.IndefiniteDescription.strong_excluded_middle (R.field_word m k) then brep_store m k

let recol_shape (m: M.mheap) (o: nat) (c: M.colour)
  : Lemma (requires brep_ok m) (ensures same_shape m (M.set_col m o c))
  = FStar.Classical.forall_intro (brep_tag m);
    FStar.Classical.forall_intro (recol_st m o c)

/// ---------------------------------------------------------------------------
/// One word written
/// ---------------------------------------------------------------------------

let rw_other (g: heap) (i j: nat) (v: U64.t)
  : Lemma (requires pos i < heap_size /\ pos j < heap_size /\ i <> j)
          (ensures read_word (write_word g (hp i) v) (hp j) == read_word g (hp j))
  = hp_v i; hp_v j;
    read_write_different g (hp i) (hp j) v

let write1_word (g: heap) (m m': M.mheap) (k: nat) (v: U64.t) (j: nat)
  : Lemma (requires brepr m g /\ brep_ok m /\ k < msize /\ pos k < heap_size /\ j < msize /\
                    cword m' k == v /\ (j <> k ==> cword m' j == cword m j))
          (ensures word (write_word g (hp k) v) j == cword m' j)
  = msize_pos k; msize_pos j;
    words_of_heq g m j;
    if j = k then read_write_same g (hp k) v
    else rw_other g k j v

/// **One word written is the model update that changes that word.**
let write1_repr (g: heap) (m m': M.mheap) (k: nat) (v: U64.t)
  : Lemma (requires brepr m g /\ brep_ok m /\ brep_ok m' /\ R.canonical m' /\ k < msize /\ pos k < heap_size /\
                    cword m' k == v /\ (forall (j: nat). j < msize /\ j <> k ==> cword m' j == cword m j))
          (ensures brepr m' (write_word g (hp k) v))
  = msize_pos k;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (write1_word g m m' k v));
    heq_of_words (write_word g (hp k) v) m'
