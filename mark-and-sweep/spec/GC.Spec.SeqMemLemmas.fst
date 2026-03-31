/// ---------------------------------------------------------------------------
/// GC.Spec.SeqMemLemmas - Helper lemmas for Seq.mem and Seq.cons
/// ---------------------------------------------------------------------------
///
/// This module provides lemmas about membership in sequences when prepending
/// elements using Seq.cons. These are useful for proving invariants about
/// stacks and lists in the GC mark phase.
///
/// These lemmas eliminate the need for assume statements when reasoning about
/// stack membership after pushing elements.

module GC.Spec.SeqMemLemmas

open FStar.Seq
open FStar.Seq.Properties

/// Lemma: If x is a member of sequence s, then x is also a member of (cons v s)
///
/// This lemma proves that prepending an element v to a sequence s preserves
/// membership of all existing elements.
///
/// Example: If addr ∈ st, then addr ∈ (cons new_value st)
///
/// Proof strategy: Uses lemma_append_count from FStar.Seq.Properties which
/// establishes that count x (s1 @| s2) = count x s1 + count x s2.
/// Since Seq.cons v s is defined as (create 1 v) @| s, and count x s > 0
/// (because mem x s), we have count x (cons v s) > 0, hence mem x (cons v s).
let seq_mem_cons_tail (#a:eqtype) (v:a) (x:a) (s:seq a)
  : Lemma 
    (requires Seq.mem x s)
    (ensures Seq.mem x (Seq.cons v s))
  = 
  lemma_append_count (Seq.create 1 v) s

/// Lemma: The head element v is always a member of (cons v s)
///
/// This lemma proves that prepending an element v to any sequence s
/// makes v a member of the resulting sequence.
///
/// Example: v ∈ (cons v st) for any st
///
/// Proof strategy: Uses lemma_append_count to show that since v is in
/// (create 1 v), it must also be in (create 1 v) @| s = cons v s.
let seq_mem_cons_head (#a:eqtype) (v:a) (s:seq a)
  : Lemma (Seq.mem v (Seq.cons v s))
  = 
  lemma_append_count (Seq.create 1 v) s

/// Lemma: If x is in (cons v s) but not in s, then x = v
///
/// This lemma is used to derive equality when we know an element was
/// added by cons but wasn't in the original sequence.
///
/// Example: If addr ∈ (cons new_val st) and addr ∉ st, then addr = new_val
///
/// Proof strategy: By case analysis. Since cons v s = (create 1 v) @| s,
/// elements of cons v s come from either create 1 v (which contains only v)
/// or from s. If x ∉ s, then x must come from create 1 v, so x = v.
let seq_mem_cons_not_mem_implies_eq (#a:eqtype) (v:a) (x:a) (s:seq a)
  : Lemma 
    (requires Seq.mem x (Seq.cons v s) /\ not (Seq.mem x s))
    (ensures x == v)
  =
  // cons v s = create 1 v @| s
  // Since x ∈ (create 1 v @| s) and x ∉ s,
  // x must be in (create 1 v), which contains only v
  // Therefore x = v
  lemma_append_count (Seq.create 1 v) s;
  // count x (cons v s) = count x (create 1 v) + count x s
  // Since not (mem x s), we have count x s = 0
  // Since mem x (cons v s), we have count x (cons v s) > 0
  // Therefore count x (create 1 v) > 0, so x ∈ create 1 v
  // create 1 v has length 1 and index 0 is v, so x = v
  ()

