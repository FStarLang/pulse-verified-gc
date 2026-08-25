module GC.Spec.FreeList.Descending

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module AllocLemmas = GC.Spec.Allocator.Lemmas
module AllocCommon = GC.Spec.Allocator.Lemmas.Common

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

/// Two 8-aligned addresses that are strictly ordered are at least a word apart,
/// so their word indices are strictly ordered too.  Lifted out of the induction
/// because the division is exactly the kind of goal Z3 4.15.3 will not discharge
/// inside a large context.
private let word_index_lt (x y: nat)
  : Lemma (requires x < y /\ x % U64.v mword == 0 /\ y % U64.v mword == 0)
          (ensures x / U64.v mword < y / U64.v mword)
  = FStar.Math.Lemmas.lemma_div_mod x (U64.v mword);
    FStar.Math.Lemmas.lemma_div_mod y (U64.v mword)

/// An address below the heap has a word index below `heap_words`.
private let word_index_bound (x: nat)
  : Lemma (requires x < heap_size /\ x % U64.v mword == 0)
          (ensures x / U64.v mword <= heap_words)
  = FStar.Math.Lemmas.lemma_div_le x heap_size (U64.v mword)

/// The chain walk, generalised over the fuel so the induction has something to
/// consume.  The measure is the *address*, which the descending condition makes
/// strictly decreasing; the fuel is carried along and shown to be sufficient.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
private let rec walk (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma
    (requires fl_descending g /\
              (fp == 0UL \/ fl_cell g fp) /\
              U64.v fp / U64.v mword <= fuel)
    (ensures AllocLemmas.fl_valid g fp fuel /\
             AllocLemmas.fl_chain_terminates g fp fuel)
    (decreases (U64.v fp))
  = if fp = 0UL then begin
      AllocLemmas.fl_chain_terminates_terminal g fp fuel;
      if fuel = 0 then AllocLemmas.fl_valid_zero g fp
      else AllocLemmas.fl_valid_terminal g fp fuel
    end
    else begin
      assert (fl_cell g fp);
      let o : obj_addr = fp in
      let n = fl_link g fp in
      assert (n == read_word g o);
      // fuel >= fp/8 >= 1
      word_index_lt 0 (U64.v fp);
      assert (fuel >= 1);
      // The link is null or a strictly lower cell; either way the tail walk
      // succeeds with one less unit of fuel.
      if n = 0UL then begin
        walk g n (fuel - 1);
        assert (read_word g o <> fp)
      end
      else begin
        assert (fl_cell g n /\ U64.v n < U64.v fp);
        word_index_lt (U64.v n) (U64.v fp);
        walk g n (fuel - 1)
      end;
      AllocLemmas.fl_valid_step g fp fuel;
      AllocLemmas.fl_chain_terminates_step g fp fuel
    end
#pop-options

let fl_descending_gives_valid g fp =
  if fp = 0UL then walk g fp heap_words
  else begin
    assert (fl_cell g fp);
    word_index_bound (U64.v fp);
    walk g fp heap_words
  end

/// ---------------------------------------------------------------------------
/// The chain-local variant
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec fl_desc_chain_weaken g fp bound bound'
  : Lemma (requires fl_desc_chain g fp bound /\ bound <= bound')
          (ensures fl_desc_chain g fp bound')
          (decreases bound)
  = if fp = 0UL then ()
    else if not (U64.v fp >= U64.v mword && U64.v fp < heap_size &&
                 U64.v fp % U64.v mword = 0)
    then ()
    else begin
      let hdv = U64.v fp - U64.v mword in
      if hdv + 2 * U64.v mword > bound then ()
      else ()
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let rec fl_desc_chain_frame g g' fp bound
  : Lemma
    (requires fl_desc_chain g fp bound /\
              Seq.length g' == Seq.length g /\
              (forall (a: hp_addr). U64.v a + U64.v mword <= bound ==>
                 read_word g' a == read_word g a))
    (ensures fl_desc_chain g' fp bound)
    (decreases bound)
  = if fp = 0UL then ()
    else if not (U64.v fp >= U64.v mword && U64.v fp < heap_size &&
                 U64.v fp % U64.v mword = 0)
    then ()
    else begin
      let o : obj_addr = fp in
      let hdv = U64.v fp - U64.v mword in
      if hdv + 2 * U64.v mword > bound then ()
      else begin
        hd_address_spec o;
        let hd : hp_addr = hd_address o in
        assert (U64.v hd == hdv);
        assert (U64.v hd + U64.v mword <= bound);
        assert (read_word g' hd == read_word g hd);
        color_of_object_spec o g;
        color_of_object_spec o g';
        is_blue_iff o g;
        is_blue_iff o g';
        wosize_of_object_spec o g;
        wosize_of_object_spec o g';
        assert (U64.v (o <: hp_addr) + U64.v mword <= bound);
        assert (read_word g' (o <: hp_addr) == read_word g (o <: hp_addr));
        fl_desc_chain_frame g g' (read_word g o) hdv
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let fl_desc_chain_cons g fb bound = ()
#pop-options

/// A chain confined below `bound` starts below `bound`, so its head's word
/// index leaves at least two units of fuel for the tail.
private let chain_fuel_step (hdv bound: nat)
  : Lemma (requires hdv + 2 * U64.v mword <= bound /\ hdv % U64.v mword == 0)
          (ensures hdv / U64.v mword + 2 <= bound / U64.v mword)
  = FStar.Math.Lemmas.lemma_div_le (hdv + 2 * U64.v mword) bound (U64.v mword);
    FStar.Math.Lemmas.lemma_div_plus hdv 2 (U64.v mword)

/// One-step decomposition: a chain confined below `bound` has its head below
/// `bound` too.  Isolated so the unfolding happens in an empty context.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let fl_desc_chain_below (g: heap) (n: U64.t) (bound: nat)
  : Lemma (requires fl_desc_chain g n bound)
          (ensures n == 0UL \/
                   (U64.v n >= U64.v mword /\ U64.v n < heap_size /\
                    U64.v n % U64.v mword == 0 /\
                    U64.v n + U64.v mword <= bound))
  = ()
#pop-options

/// Chain walk with the membership side condition supplied by the caller.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let rec chain_walk
  (g: heap) (fp: U64.t) (bound: nat) (fuel: nat)
  (mem_step: (a: U64.t -> Lemma
     (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\
               U64.v a % U64.v mword == 0 /\
               Seq.mem (a <: obj_addr) (objects zero_addr g) /\
               is_blue (a <: obj_addr) g /\
               U64.v (wosize_of_object (a <: obj_addr) g) >= 1)
     (ensures (let n = read_word g (a <: obj_addr) in
               n == 0UL \/
               (U64.v n >= U64.v mword /\ U64.v n < heap_size /\
                U64.v n % U64.v mword == 0 /\
                Seq.mem (n <: obj_addr) (objects zero_addr g))))))
  : Lemma
    (requires fl_desc_chain g fp bound /\
              bound <= heap_size /\
              (fp == 0UL \/ Seq.mem (fp <: obj_addr) (objects zero_addr g)) /\
              bound / U64.v mword <= fuel)
    (ensures AllocLemmas.fl_valid g fp fuel /\
             AllocLemmas.fl_chain_terminates g fp fuel)
    (decreases bound)
  = if fp = 0UL then begin
      AllocLemmas.fl_chain_terminates_terminal g fp fuel;
      if fuel = 0 then AllocLemmas.fl_valid_zero g fp
      else AllocLemmas.fl_valid_terminal g fp fuel
    end
    else begin
      let o : obj_addr = fp in
      let hdv = U64.v fp - U64.v mword in
      assert (hdv + 2 * U64.v mword <= bound);
      chain_fuel_step hdv bound;
      assert (fuel >= 2);
      mem_step fp;
      let n = read_word g o in
      hd_address_spec o;
      // The tail is null or a cell strictly below this one, so the link is not
      // a self-loop and the recursive walk has both fuel and measure to spare.
      fl_desc_chain_below g n hdv;
      chain_walk g n hdv (fuel - 1) mem_step;
      AllocLemmas.fl_valid_step g fp fuel;
      AllocLemmas.fl_chain_terminates_step g fp fuel
    end
#pop-options

let fl_desc_chain_gives_valid g fp mem_step =
  chain_walk g fp heap_size heap_words mem_step
