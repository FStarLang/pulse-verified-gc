/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWWords - a byte heap, word by word, against a model heap
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  The witness runs track, at every step, an explicit model
/// heap that the byte heap represents.  A model heap that is well formed and
/// canonical (`Abs.brep_ok`, `Rep.canonical`) fixes every word from
/// `zero_addr` on (`Abs.cword`: a block's header, or a field's word):
///   - `heq_of_words`: a byte heap with those words represents it;
///   - `words_of_heq`: a byte heap that represents it has those words.
/// So a step that writes a few words of the byte heap is the model update
/// that changes the same words.

module GC.Spec.Top.FFWWords

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// An aligned address from `zero_addr` on is a model address.
let hp_of (a: hp_addr)
  : Lemma (requires U64.v a >= base)
          (ensures (let j = mpos (U64.v a) in pos j == U64.v a /\ j < msize /\ hp j == a))
  = base_facts ();
    let j = mpos (U64.v a) in
    FStar.Math.Lemmas.lemma_mod_sub_distr (U64.v a) base 8;
    FStar.Math.Lemmas.lemma_div_exact (U64.v a - base) 8;
    msize_pos j;
    U64.v_inj (hp j) a

/// **Words to representation.**
let heq_of_words (g: heap) (m: M.mheap)
  : Lemma (requires brep_ok m /\ R.canonical m /\ (forall (j: nat). j < msize ==> word g j == cword m j))
          (ensures brepr m g)
  = conc_repr m;
    let c = conc m in
    let rd (a: hp_addr) : Lemma (U64.v a >= base ==> read_word g a == read_word c a)
      = if U64.v a >= base then begin
          hp_of a;
          conc_word m (mpos (U64.v a))
        end in
    FStar.Classical.forall_intro rd;
    cabs_same_above c g

/// A header word is the encoding of its reading.
let enc_abs_hdr (v: U64.t) : Lemma (enc_hdr (abs_hdr v) == v)
  = wosize_high v;
    FStar.Math.Lemmas.lemma_div_lt_nat (U64.v v) 64 10;
    assert_norm (pow2 64 / pow2 10 == pow2 54);
    abs_hdr_enc (abs_hdr v);
    abs_hdr_inj (enc_hdr (abs_hdr v)) v

/// A word is the encoding of its reading.
let concv_absv (v: U64.t) : Lemma (concv (absv v) == v)
  = absv_storable v;
    absv_concv (absv v);
    absv_inj (concv (absv v)) v

/// **Representation to words.**
#push-options "--z3rlimit 40"
let words_of_heq (g: heap) (m: M.mheap) (j: nat)
  : Lemma (requires brepr m g /\ brep_ok m /\ j < msize) (ensures word g j == cword m j)
  = brep_size m;
    brep_cover m j;
    let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> M.covers m o j) in
    if M.is_block m j then enc_abs_hdr (word g j)
    else begin
      assert (o < j);
      assert (M.covers (abs g) o j);
      is_fw_iff g j;
      concv_absv (word g j)
    end
#pop-options

let words_of_heq_all (g: heap) (m: M.mheap)
  : Lemma (requires brepr m g /\ brep_ok m) (ensures forall (j: nat). j < msize ==> word g j == cword m j)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (words_of_heq g m))
