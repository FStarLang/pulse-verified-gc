/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWState - the first-fit witness heaps, in closed form
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  The first-fit witness runs (GC.Spec.Top.FFWSeq,
/// FFWInc) work on a heap of `msize` words, an abstract size
/// (`GC.Spec.ZeroAddr`), under one explicit hypothesis on it:
///   - `ff_room`: `msize >= 32`, room for the objects the runs allocate.
/// The real runtime configuration meets it by a wide margin.
///
/// First-fit places each new block at the top of the free block at 0
/// (`FFWAlloc.split`), so the runs' blocks sit at fixed distances below the
/// top: A (2 fields), B (1), C (1), K (a closure of 3 fields, an infix header
/// in its second), D (1), the two copies the minor collection while marking
/// promotes (P1 of Y2, P2 of Y1), E (1), and the two the one while sweeping
/// promotes (P3, P4).  Every model heap of the runs is `mk st`
/// for a small record `st`: the free block's size, each block's colour
/// (`None` before it is allocated), the fields the program writes, and the
/// free list's link in the free block's first field.

module GC.Spec.Top.FFWState

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFWWords
open GC.Spec.Top.FFWModel
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module FS = GC.Spec.FusedSweep
module FSI = GC.Spec.FusedSweep.Inv
module FWA = GC.Spec.Top.FFWAlloc
module FIn = GC.Spec.Top.FFInit

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The size hypothesis
/// ---------------------------------------------------------------------------

/// **The witness runs' hypothesis on the configuration**: room for their
/// objects (and more) in the major heap, and for two one-field objects in
/// the nursery.
let ff_room : prop = 32 <= msize /\ 4 <= ywords

let sub (a b: nat) : nat = if a >= b then a - b else 0

/// The blocks' model addresses.
let xA : nat = sub msize 3
let xB : nat = sub msize 5
let xC : nat = sub msize 7
let xK : nat = sub msize 11
let xD : nat = sub msize 13
let xE : nat = sub msize 19
let xP1 : nat = sub msize 15   (* the copy of Y2, promoted while marking *)
let xP2 : nat = sub msize 17   (* the copy of Y1, promoted while marking *)
let xP3 : nat = sub msize 21   (* the copy of Y2, promoted while sweeping *)
let xP4 : nat = sub msize 23   (* the copy of Y1, promoted while sweeping *)

let xs (_: unit)
  : Lemma (requires ff_room)
          (ensures xA == msize - 3 /\ xB == msize - 5 /\ xC == msize - 7 /\ xK == msize - 11 /\
                   xD == msize - 13 /\ xE == msize - 19 /\ xP1 == msize - 15 /\ xP2 == msize - 17 /\
                   xP3 == msize - 21 /\ xP4 == msize - 23)
  = ()

/// ---------------------------------------------------------------------------
/// The heaps
/// ---------------------------------------------------------------------------

noeq type wst = {
  f  : nat;                 (* the free block's fields *)
  ca : option M.colour;
  cb : option M.colour;
  cc : option M.colour;
  ck : option M.colour;
  cd : option M.colour;
  ce : option M.colour;
  cp1 : option M.colour;  cp2 : option M.colour;  (* the copies of Y2 and Y1, while marking *)
  cp3 : option M.colour;  cp4 : option M.colour;  (* the copies of Y2 and Y1, while sweeping *)
  a0 : M.value;  a1 : M.value;  (* A's fields *)
  c0 : M.value;                 (* C's field *)
  d0 : M.value;                 (* D's field *)
  lk : M.value;                 (* the free block's link *)
}

let ohd (wz: nat) (tag: M.tag_t) (c: option M.colour) : option M.header =
  match c with Some c -> Some ({ M.wz = wz; M.tag = tag; M.col = c }) | None -> None

let mhd (st: wst) (x: nat) : option M.header =
  if x = 0 then Some (FWA.free_hdr st.f)
  else if x = xA then ohd 2 0 st.ca
  else if x = xB then ohd 1 0 st.cb
  else if x = xC then ohd 1 0 st.cc
  else if x = xK then ohd 3 M.closure_tag st.ck
  else if x = xD then ohd 1 0 st.cd
  else if x = xE then ohd 1 0 st.ce
  else if x = xP1 then ohd 1 0 st.cp1
  else if x = xP2 then ohd 1 0 st.cp2
  else if x = xP3 then ohd 1 0 st.cp3
  else if x = xP4 then ohd 1 0 st.cp4
  else None

let mbody (st: wst) (w: nat) : M.value =
  if w = 1 then st.lk
  else if Some? st.ca && w = xA + 1 then st.a0
  else if Some? st.ca && w = xA + 2 then st.a1
  else if Some? st.cb && w = xB + 1 then M.VInt 1
  else if Some? st.cc && w = xC + 1 then st.c0
  else if Some? st.ck && w = xK + 1 then M.VInt 1
  else if Some? st.ck && w = xK + 2 then M.infix_word 2
  else if Some? st.ck && w = xK + 3 then M.VInt 1
  else if Some? st.cd && w = xD + 1 then st.d0
  else if Some? st.ce && w = xE + 1 then M.VPtr (M.Major xA)
  else if Some? st.cp1 && w = xP1 + 1 then M.infix_word 2
  else if Some? st.cp2 && w = xP2 + 1 then M.VPtr (M.Major (xK + 2))
  else if Some? st.cp3 && w = xP3 + 1 then M.infix_word 2
  else if Some? st.cp4 && w = xP4 + 1 then M.VPtr (M.Major (xK + 2))
  else M.VInt 0

let mk (st: wst) : M.mheap = { M.size = msize; M.hd = mhd st; M.body = mbody st }

/// The start: one free block.
let st0 : wst = {
  f = sub msize 1; ca = None; cb = None; cc = None; ck = None; cd = None; ce = None;
  cp1 = None; cp2 = None; cp3 = None; cp4 = None;
  a0 = M.VInt 0; a1 = M.VInt 0; c0 = M.VInt 0; d0 = M.VInt 0; lk = M.VInt 0 }

/// Representability is about the reading alone.
let brep_heq_parts (m m': M.mheap)
  : Lemma (requires brep_ok m /\ R.heq m m')
          (ensures M.well_formed m' /\ m'.M.size == msize /\
                   (forall (o: nat). M.is_block m' o ==> M.wz_of m' o >= 1) /\
                   (forall (w: nat). R.field_word m' w ==> storable_w (m'.M.body w)))
  = reveal_opaque (`%brep_ok) (brep_ok m);
    assert (forall (o w: nat). M.covers m o w == M.covers m' o w);
    assert (forall (w: nat). R.field_word m w <==> R.field_word m' w)

let brep_heq (m m': M.mheap)
  : Lemma (requires brep_ok m /\ R.heq m m') (ensures brep_ok m')
  = brep_heq_parts m m';
    brep_ok_intro m'

/// ---------------------------------------------------------------------------
/// The initial heap
/// ---------------------------------------------------------------------------

let zero8 (_: unit) : Lemma (uint64_to_uint8 0UL == 0uy)
  = assert_norm (pow2 8 == 256);
    U8.v_inj (uint64_to_uint8 0UL) 0uy

let shr0 (k: U32.t{U32.v k < 64}) : Lemma (U64.shift_right 0UL k == 0UL)
  = FStar.UInt.shift_right_value_lemma #64 0 (U32.v k);
    U64.v_inj (U64.shift_right 0UL k) 0UL

let rz (a: hp_addr) : Lemma (read_word zero_heap a == 0UL)
  = zero8 ();
    shr0 8ul; shr0 16ul; shr0 24ul; shr0 32ul; shr0 40ul; shr0 48ul; shr0 56ul;
    let g = zero_heap in
    let v = U64.v a in
    assert (v + 8 <= heap_size);
    assert (Seq.index g v == 0uy /\ Seq.index g (v + 1) == 0uy /\ Seq.index g (v + 2) == 0uy /\
            Seq.index g (v + 3) == 0uy /\ Seq.index g (v + 4) == 0uy /\ Seq.index g (v + 5) == 0uy /\
            Seq.index g (v + 6) == 0uy /\ Seq.index g (v + 7) == 0uy);
    read_word_spec g a;
    combine_decompose_identity 0UL

/// The initial heap's words.
#push-options "--z3rlimit 40"
let init_word (j: nat)
  : Lemma (requires j < msize)
          (ensures word init_heap j == (if j = 0 then FIn.init_hdr else 0UL))
  = base_facts ();
    init_facts ();
    msize_pos j; msize_pos 1;
    FIn.words ();
    U64.v_inj (hp 0) zero_addr;
    U64.v_inj (hp 1) FIn.a1;
    let g1 = write_word zero_heap zero_addr FIn.init_hdr in
    assert (init_heap == write_word g1 FIn.a1 0UL);
    if j >= 2 then begin
      rw_other g1 1 j 0UL;
      rw_other zero_heap 0 j FIn.init_hdr;
      rz (hp j)
    end
#pop-options

let init_shape_cov (w: nat)
  : Lemma (requires ff_room) (ensures w < msize ==> M.covers (mk st0) 0 w)
  = ()

let init_shape_uq (o1 o2 w: nat)
  : Lemma (requires ff_room) (ensures M.covers (mk st0) o1 w /\ M.covers (mk st0) o2 w ==> o1 == o2)
  = ()

let init_st (w: nat)
  : Lemma (ensures R.field_word (mk st0) w ==> storable_w ((mk st0).M.body w))
  = ()

let init_nf (w: nat)
  : Lemma (ensures ~(R.field_word (mk st0) w) ==> (mk st0).M.body w == M.VInt 0)
  = if w = 1 && msize >= 2 then assert (M.covers (mk st0) 0 1)

let init_past (o: nat) : Lemma (o >= msize ==> (mk st0).M.hd o == None) = base_facts ()

let init_ok (_: unit)
  : Lemma (requires ff_room) (ensures brep_ok (mk st0) /\ R.canonical (mk st0))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires init_shape_cov);
    FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 init_shape_uq);
    FStar.Classical.forall_intro init_st;
    FStar.Classical.forall_intro init_nf;
    FStar.Classical.forall_intro init_past;
    wf_of (mk st0);
    brep_ok_intro (mk st0)

let init_cword (j: nat)
  : Lemma (requires ff_room /\ j < msize) (ensures word init_heap j == cword (mk st0) j)
  = init_word j;
    init_facts ();
    if j = 0 then begin
      FSI.free_header_facts init_wz;
      FWA.enc_of FIn.init_hdr (FWA.free_hdr (sub msize 1))
    end

/// **The initial heap is `mk st0`.**
let init_repr (_: unit) : Lemma (requires ff_room) (ensures brepr (mk st0) init_heap)
  = init_ok ();
    FStar.Classical.forall_intro (FStar.Classical.move_requires init_cword);
    heq_of_words init_heap (mk st0)
