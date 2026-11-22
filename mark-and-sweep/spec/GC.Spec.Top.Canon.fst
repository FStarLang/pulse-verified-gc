/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Canon - a tiled reading determines the words
/// ---------------------------------------------------------------------------
///
/// When the canonical reading of a byte heap is tiled, every word from
/// `zero_addr` on is a header or a field, and the reading of either is
/// injective (`Low.abs_hdr_inj`, `Low.absv_inj`).  So two byte heaps with the
/// same tiled reading have the same words there (`same_words`), and with the
/// same bytes below `zero_addr` they are the same heap (`same_gl`).  An
/// allocator that runs on `set_low h lo` then does the same on every byte
/// heap that represents a given model heap.

module GC.Spec.Top.Canon

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64
module HE = GC.Gen.HeapExtensional

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

#push-options "--z3rlimit 40"
let same_words_at (g1 g2: heap) (k o: nat)
  : Lemma (requires R.heq (cabs g1) (cabs g2) /\ M.covers (cabs g1) o k)
          (ensures word g1 k == word g2 k)
  = assert (M.covers (cabs g2) o k);
    if o = k then begin
      assert ((cabs g1).M.hd k == Some (abs_hdr (word g1 k)));
      assert ((cabs g2).M.hd k == Some (abs_hdr (word g2 k)));
      abs_hdr_inj (word g1 k) (word g2 k)
    end
    else begin
      assert (o < k);
      is_fw_iff g1 k;
      is_fw_iff g2 k;
      assert (M.covers (abs g1) o k /\ M.covers (abs g2) o k);
      FStar.Classical.exists_intro (fun (x: nat) -> M.covers (abs g1) x k /\ x < k) o;
      FStar.Classical.exists_intro (fun (x: nat) -> M.covers (abs g2) x k /\ x < k) o;
      assert (is_fw g1 k /\ is_fw g2 k);
      absv_inj (word g1 k) (word g2 k)
    end
#pop-options

let same_words (g1 g2: heap) (k: nat)
  : Lemma (requires R.heq (cabs g1) (cabs g2) /\ M.tiled (cabs g1) /\ k < msize)
          (ensures word g1 k == word g2 k)
  = let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers (cabs g1) o k) in
    same_words_at g1 g2 k o

let low_word (g1 g2: heap) (lo: low_t) (a: hp_addr)
  : Lemma (requires U64.v a < base)
          (ensures read_word (set_low g1 lo) a == read_word (set_low g2 lo) a)
  = base_facts ();
    read_word_spec (set_low g1 lo) a;
    read_word_spec (set_low g2 lo) a;
    let b (k: nat{k < 8}) : Lemma (Seq.index (set_low g1 lo) (U64.v a + k) == Seq.index (set_low g2 lo) (U64.v a + k))
      = set_low_index g1 lo (U64.v a + k); set_low_index g2 lo (U64.v a + k) in
    b 0; b 1; b 2; b 3; b 4; b 5; b 6; b 7

/// **Two byte heaps with the same tiled reading, and the same bytes below
/// `zero_addr`, are the same heap.**
let same_gl (g1 g2: heap) (lo: low_t)
  : Lemma (requires R.heq (cabs g1) (cabs g2) /\ M.tiled (cabs g1))
          (ensures set_low g1 lo == set_low g2 lo)
  = let rw (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word (set_low g1 lo) (U64.uint_to_t a) == read_word (set_low g2 lo) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          let p : hp_addr = U64.uint_to_t a in
          if a >= base then begin
            read_set_low g1 lo p;
            read_set_low g2 lo p;
            word_at g1 p;
            word_at g2 p;
            same_words g1 g2 (mpos a)
          end
          else low_word g1 g2 lo p
        end in
    FStar.Classical.forall_intro rw;
    HE.heap_read_word_ext (set_low g1 lo) (set_low g2 lo)
