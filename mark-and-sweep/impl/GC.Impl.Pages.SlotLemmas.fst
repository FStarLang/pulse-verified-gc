/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.SlotLemmas - the page sweep's one pass, with a deferred link
/// ---------------------------------------------------------------------------
///
/// The swept page links each free slot to the next free slot after it
/// (`SweepPage.sw_heap`, `nd_from`), which a pass in address order does not
/// know yet when it frees the slot.  As in the prototype's sweep, the pass
/// writes a free slot's link when it finds the next free slot, and the last
/// one's (0) when it ends.
///
/// `pend g i c k last` is the heap the pass has made after slot `k - 1`: the
/// swept slots `0 .. k-1`, except that the link of the last free slot so far
/// (at `last`, 0 if none) still holds what the marked heap had there.
/// `last_ok` says where `last` is.  `pend_live`, `pend_dead` and `pend_end`
/// are the pass's steps.

module GC.Impl.Pages.SlotLemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module PI = GC.Spec.Pages.PoolInit
module SP = GC.Spec.Pages.SweepPage
module HE = GC.Gen.HeapExtensional

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The last free slot before `k` is at `last`, and no free slot lies between
/// it and `k`; or there is none before `k` and `last` is 0.
let last_ok (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat) (last: U64.t) : prop =
  (last == 0UL /\ SP.nd_from g i c 0 == SP.nd_from g i c k) \/
  (exists (jl: nat). jl < k /\ jl < n_slots c /\ not (SP.live g i c jl) /\
     last == (PI.slot_link i c jl <: U64.t) /\
     SP.nd_from g i c (jl + 1) == SP.nd_from g i c k)

let pend (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat) (last: U64.t)
  : GTot heap =
  if k > n_slots c then g
  else if last <> 0UL && U64.v last < heap_size && U64.v last % 8 = 0
  then write_word (SP.sw_heap g i c k) last (read_word g last)
  else SP.sw_heap g i c k

#push-options "--fuel 1"
let nd_step (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (SP.nd_from g i c k ==
           (if SP.live g i c k then SP.nd_from g i c (k + 1) else (PI.slot_link i c k <: U64.t)))
  = ()

let nd_end (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (SP.nd_from g i c (n_slots c) == 0UL)
  = ()

let sw_step (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (SP.sw_heap g i c (k + 1) ==
           (if SP.live g i c k
            then write_word (SP.sw_heap g i c k) (PI.slot_hd i c k)
                            (colorHeader (read_word g (PI.slot_hd i c k)) White)
            else write_word (write_word (SP.sw_heap g i c k) (PI.slot_hd i c k) (PI.slot_hdr c))
                            (PI.slot_link i c k) (SP.nd_from g i c (k + 1))))
  = ()

let sw_zero (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : Lemma (SP.sw_heap g i c 0 == g) = ()
#pop-options

/// A word after a write.
let rw (g: heap) (a: hp_addr) (x: hp_addr) (v: U64.t)
  : Lemma (read_word (write_word g a v) x == (if x = a then v else read_word g x))
  = if x = a then read_write_same g a v else read_write_different g a x v

/// Where the last free slot's link lies: in the heap, below slot `k`.
let last_where (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c}) (last: U64.t)
  : Lemma (requires last_ok g i c k last /\ last <> 0UL)
          (ensures U64.v last < heap_size /\ U64.v last % 8 == 0 /\
                   (k < n_slots c ==> U64.v last + 8 <= slot_base i c k) /\
                   (exists (jl: nat). jl < k /\ jl < n_slots c /\ not (SP.live g i c jl) /\
                      last == (PI.slot_link i c jl <: U64.t) /\
                      SP.nd_from g i c (jl + 1) == SP.nd_from g i c k))
  = eliminate exists (jl: nat). jl < k /\ not (SP.live g i c jl) /\
                   last == (PI.slot_link i c jl <: U64.t) /\
                   SP.nd_from g i c (jl + 1) == SP.nd_from g i c k
    with (if k < n_slots c then SP.slot_words i c jl k)

/// The header of slot `k` is still the marked heap's.
let pend_hd (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c}) (last: U64.t)
  : Lemma (requires last_ok g i c k last)
          (ensures read_word (pend g i c k last) (PI.slot_hd i c k) == read_word g (PI.slot_hd i c k))
  = let a = PI.slot_hd i c k in
    SP.sw_out g i c k a;
    if last <> 0UL then begin
      last_where g i c k last;
      rw (SP.sw_heap g i c k) last a (read_word g last)
    end

/// A survivor: its header made white.
let pend_live (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c}) (last: U64.t)
  : Lemma (requires last_ok g i c k last /\ SP.live g i c k)
          (ensures (let a = PI.slot_hd i c k in
                    write_word (pend g i c k last) a (colorHeader (read_word g a) White) ==
                    pend g i c (k + 1) last /\
                    last_ok g i c (k + 1) last))
  = let a = PI.slot_hd i c k in
    let v = colorHeader (read_word g a) White in
    sw_step g i c k;
    nd_step g i c k;
    let lhs = write_word (pend g i c k last) a v in
    let rhs = pend g i c (k + 1) last in
    if last <> 0UL then begin
      last_where g i c k last;
      let aux (x: hp_addr) : Lemma (read_word lhs x == read_word rhs x)
        = rw (pend g i c k last) a x v;
          rw (SP.sw_heap g i c k) last x (read_word g last);
          rw (SP.sw_heap g i c (k + 1)) last x (read_word g last);
          rw (SP.sw_heap g i c k) a x v;
          rw (SP.sw_heap g i c k) a last v
      in
      FStar.Classical.forall_intro aux;
      HE.heap_read_word_ext lhs rhs
    end

/// A slot freed: its header written, the last free slot's link set to it,
/// and it becomes the last free slot.
let pend_dead (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c}) (last: U64.t)
  : Lemma (requires last_ok g i c k last /\ not (SP.live g i c k))
          (ensures (let a = PI.slot_hd i c k in
                    let l = PI.slot_link i c k in
                    let s1 = write_word (pend g i c k last) a (PI.slot_hdr c) in
                    (if last = 0UL then s1 else write_word s1 last (l <: U64.t)) ==
                    pend g i c (k + 1) (l <: U64.t) /\
                    last_ok g i c (k + 1) (l <: U64.t) /\
                    (last = 0UL ==> SP.nd_from g i c 0 == (l <: U64.t))))
  = let a = PI.slot_hd i c k in
    let l = PI.slot_link i c k in
    let h = PI.slot_hdr c in
    sw_step g i c k;
    nd_step g i c k;
    PI.slot_fits i c k;
    assert (U64.v l == U64.v a + 8);
    SP.sw_out g i c k l;
    let s0 = pend g i c k last in
    let s1 = write_word s0 a h in
    let lhs = if last = 0UL then s1 else write_word s1 last (l <: U64.t) in
    let sk1 = SP.sw_heap g i c (k + 1) in
    let rhs = pend g i c (k + 1) (l <: U64.t) in
    let sw1 = write_word (SP.sw_heap g i c k) a h in
    if last <> 0UL then begin
      last_where g i c k last;
      eliminate exists (jl: nat). jl < k /\ not (SP.live g i c jl) /\
                   last == (PI.slot_link i c jl <: U64.t) /\
                   SP.nd_from g i c (jl + 1) == SP.nd_from g i c k
      with SP.sw_link g i c k jl
    end;
    let aux (x: hp_addr) : Lemma (read_word lhs x == read_word rhs x)
      = rw sk1 l x (read_word g l);
        rw sw1 l x (SP.nd_from g i c (k + 1));
        rw (SP.sw_heap g i c k) a x h;
        rw (SP.sw_heap g i c k) a l h;
        rw s0 a x h;
        if last <> 0UL then begin
          rw s1 last x (l <: U64.t);
          rw (SP.sw_heap g i c k) last x (read_word g last);
          rw (SP.sw_heap g i c k) a last h;
          rw sw1 l last (SP.nd_from g i c (k + 1));
          rw s0 a last h
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext lhs rhs

/// The end: the last free slot's link is 0, and the heap is the swept one.
let pend_end (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (last: U64.t)
  : Lemma (requires last_ok g i c (n_slots c) last)
          (ensures (let s = pend g i c (n_slots c) last in
                    (if last = 0UL then s else write_word s last 0UL) == SP.sw_heap g i c (n_slots c) /\
                    (last = 0UL ==> SP.nd_from g i c 0 == 0UL)))
  = nd_end g i c;
    let sw = SP.sw_heap g i c (n_slots c) in
    if last <> 0UL then begin
      last_where g i c (n_slots c) last;
      eliminate exists (jl: nat). jl < n_slots c /\ not (SP.live g i c jl) /\
                   last == (PI.slot_link i c jl <: U64.t) /\
                   SP.nd_from g i c (jl + 1) == SP.nd_from g i c (n_slots c)
      with SP.sw_link g i c (n_slots c) jl;
      let s = pend g i c (n_slots c) last in
      let lhs = write_word s last 0UL in
      let aux (x: hp_addr) : Lemma (read_word lhs x == read_word sw x)
        = rw s last x 0UL;
          rw sw last x (read_word g last)
      in
      FStar.Classical.forall_intro aux;
      HE.heap_read_word_ext lhs sw
    end

/// The start.
let pend_start (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (pend g i c 0 0UL == g /\ last_ok g i c 0 0UL)
  = sw_zero g i c
