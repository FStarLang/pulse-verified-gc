(*
   Pulse GC - Remembered Set (Stage 2)

   Fixed-capacity append-only buffer of `(holder, field_idx)` pairs.
   Backed by two parallel `Vec U64.t` arrays sharing a single top
   pointer that counts the number of recorded entries.

   Grows upward (top index = next free slot). The minor collector
   drains the buffer during a collect cycle and then clears the
   top pointer back to 0.

   Model: this mirrors `common/impl/GC.Impl.Stack.fst` but uses an
   upward-growing layout because the remembered set has no LIFO
   semantics — its order is irrelevant; only the set of recorded
   entries matters. Parallel `U64.t` arrays were chosen over a single
   `Vec ref_loc` to avoid relying on Pulse Vec support for custom
   record types.
*)

module GC.Impl.RememberedSet

#lang-pulse

open Pulse.Lib.Pervasives
module Seq = FStar.Seq
module V = Pulse.Lib.Vec
module B = Pulse.Lib.Box
module SZ = FStar.SizeT
module U64 = FStar.UInt64

open GC.Spec.RememberedSet

/// ---------------------------------------------------------------------------
/// Remembered Set Type
/// ---------------------------------------------------------------------------

noeq
type rem_set_rec = {
  holders    : V.vec U64.t;
  field_idxs : V.vec U64.t;
  top        : B.box SZ.t;     // count of recorded entries, in [0, cap]
  cap        : SZ.t;           // capacity (matches V.length of both)
}

let rem_set = rem_set_rec

let rem_set_capacity (rs: rem_set) : GTot nat = SZ.v rs.cap

/// ---------------------------------------------------------------------------
/// Predicate
/// ---------------------------------------------------------------------------
///
/// Entries occupy positions [0..top); the logical view `rt[i] = (holders[i], field_idxs[i])`
/// for i in [0..top). This is the upward-growing dual of the gray stack's
/// downward layout — both work; upward is simpler when LIFO is not needed.

let is_rem_set (rs: rem_set) (rt: ref_table) : slprop =
  exists* (t: SZ.t) (hs: Seq.seq U64.t) (fs: Seq.seq U64.t).
    B.pts_to rs.top t **
    V.pts_to rs.holders hs **
    V.pts_to rs.field_idxs fs **
    pure (
      SZ.v rs.cap > 0 /\
      V.length rs.holders == SZ.v rs.cap /\
      V.length rs.field_idxs == SZ.v rs.cap /\
      V.is_full_vec rs.holders /\
      V.is_full_vec rs.field_idxs /\
      Seq.length hs == SZ.v rs.cap /\
      Seq.length fs == SZ.v rs.cap /\
      SZ.v t <= SZ.v rs.cap /\
      Seq.length rt == SZ.v t /\
      (forall (i:nat). i < Seq.length rt ==>
        (get_ref rt i).holder    == Seq.index hs i /\
        (get_ref rt i).field_idx == Seq.index fs i)
    )

/// ---------------------------------------------------------------------------
/// Pure helper lemmas
/// ---------------------------------------------------------------------------

/// After writing the new pair at position `top` and bumping top to top+1,
/// the logical view appends `e` at the tail.
let add_ref_impl_lemma
  (hs: Seq.seq U64.t) (fs: Seq.seq U64.t) (top cap: nat)
  (e: ref_loc) (rt: ref_table)
  : Lemma
    (requires
      top < cap /\
      Seq.length hs == cap /\ Seq.length fs == cap /\
      Seq.length rt == top /\
      (forall (i:nat). i < top ==>
        (get_ref rt i).holder    == Seq.index hs i /\
        (get_ref rt i).field_idx == Seq.index fs i))
    (ensures (
      let hs' = Seq.upd hs top e.holder in
      let fs' = Seq.upd fs top e.field_idx in
      let rt' = add_ref rt e in
      Seq.length rt' == top + 1 /\
      Seq.length hs' == cap /\ Seq.length fs' == cap /\
      (forall (i:nat). i < top + 1 ==>
        (get_ref rt' i).holder    == Seq.index hs' i /\
        (get_ref rt' i).field_idx == Seq.index fs' i)))
  = let hs' = Seq.upd hs top e.holder in
    let fs' = Seq.upd fs top e.field_idx in
    let rt' = add_ref rt e in
    add_ref_length rt e;
    let aux (i:nat{i < top + 1})
      : Lemma ((get_ref rt' i).holder    == Seq.index hs' i /\
               (get_ref rt' i).field_idx == Seq.index fs' i)
      = if i < top then begin
          add_ref_old rt e i
          // Seq.upd preserves index at i ≠ top
        end else begin
          // i == top
          add_ref_new rt e
        end
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// Operations
/// ---------------------------------------------------------------------------

/// Create an empty remembered set from caller-provided storage.
fn create_rem_set
  (holders: V.vec U64.t)
  (field_idxs: V.vec U64.t)
  (cap: SZ.t)
  requires V.pts_to holders 'init_h **
           V.pts_to field_idxs 'init_f **
           pure (V.length holders == SZ.v cap /\
                 V.length field_idxs == SZ.v cap /\
                 SZ.v cap > 0 /\
                 V.is_full_vec holders /\
                 V.is_full_vec field_idxs)
  returns rs: rem_set
  ensures is_rem_set rs empty_ref_table **
          pure (rem_set_capacity rs == SZ.v cap)
{
  V.pts_to_len holders;
  V.pts_to_len field_idxs;
  let top_box = B.alloc 0sz;
  let rs : rem_set_rec = { holders; field_idxs; top = top_box; cap };
  rewrite (B.pts_to top_box 0sz) as (B.pts_to rs.top 0sz);
  rewrite (V.pts_to holders 'init_h) as (V.pts_to rs.holders 'init_h);
  rewrite (V.pts_to field_idxs 'init_f) as (V.pts_to rs.field_idxs 'init_f);
  fold (is_rem_set rs empty_ref_table);
  rs
}

/// Destroy and return the backing storage.
fn destroy_rem_set (rs: rem_set)
  requires is_rem_set rs 'rt
  returns hs: (V.vec U64.t & V.vec U64.t)
  ensures exists* h_contents f_contents.
            V.pts_to (fst hs) h_contents **
            V.pts_to (snd hs) f_contents **
            pure (V.length (fst hs) == rem_set_capacity rs /\
                  V.length (snd hs) == rem_set_capacity rs /\
                  V.is_full_vec (fst hs) /\
                  V.is_full_vec (snd hs))
{
  unfold is_rem_set;
  with _t _hs _fs. _;
  B.free rs.top;
  (rs.holders, rs.field_idxs)
}

/// Current number of recorded entries.
fn rem_set_len (rs: rem_set)
  requires is_rem_set rs 'rt
  returns n: SZ.t
  ensures is_rem_set rs 'rt ** pure (SZ.v n == Seq.length 'rt)
{
  unfold is_rem_set;
  with _t _hs _fs. _;
  let n = B.op_Bang rs.top;
  fold (is_rem_set rs 'rt);
  n
}

/// True when no more entries can be added without an overflow check.
fn is_full (rs: rem_set)
  requires is_rem_set rs 'rt
  returns b: bool
  ensures is_rem_set rs 'rt ** pure (b <==> (Seq.length 'rt == rem_set_capacity rs))
{
  unfold is_rem_set;
  with _t _hs _fs. _;
  let t = B.op_Bang rs.top;
  let b = (t = rs.cap);
  fold (is_rem_set rs 'rt);
  b
}

/// True when empty (no entries recorded).
fn is_empty (rs: rem_set)
  requires is_rem_set rs 'rt
  returns b: bool
  ensures is_rem_set rs 'rt ** pure (b <==> (Seq.length 'rt == 0))
{
  unfold is_rem_set;
  with _t _hs _fs. _;
  let t = B.op_Bang rs.top;
  let b = (t = 0sz);
  fold (is_rem_set rs 'rt);
  b
}

/// Append an entry. Precondition: remaining capacity.
fn add_ref_impl (rs: rem_set) (holder: U64.t) (field_idx: U64.t)
  requires is_rem_set rs 'rt **
           pure (Seq.length 'rt < rem_set_capacity rs)
  ensures is_rem_set rs (add_ref 'rt ({ holder; field_idx }))
{
  unfold is_rem_set;
  with t hs fs. _;
  let top_val = B.op_Bang rs.top;
  V.op_Array_Assignment rs.holders top_val holder;
  V.op_Array_Assignment rs.field_idxs top_val field_idx;
  let new_top = SZ.add top_val 1sz;
  B.op_Colon_Equals rs.top new_top;
  add_ref_impl_lemma hs fs (SZ.v top_val) (SZ.v rs.cap)
    ({ holder; field_idx }) 'rt;
  fold (is_rem_set rs (add_ref 'rt ({ holder; field_idx })))
}

/// Reset to empty (used after a minor collect drains all entries).
fn clear_rem_set (rs: rem_set)
  requires is_rem_set rs 'rt
  ensures is_rem_set rs empty_ref_table
{
  unfold is_rem_set;
  with _t _hs _fs. _;
  B.op_Colon_Equals rs.top 0sz;
  fold (is_rem_set rs empty_ref_table)
}

// get_holder / get_field_idx accessors will be added in Stage 3 alongside
// the minor-collect drain loop that consumes them. They need a refinement
// propagation from `pure (SZ.v i < Seq.length 'rt)` into the ensures of
// `get_ref`, which is easier to handle in tandem with the worklist code.
