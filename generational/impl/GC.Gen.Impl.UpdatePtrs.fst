/// ---------------------------------------------------------------------------
/// GC.Gen.Impl.UpdatePtrs — Rewrite roots after promotion
/// ---------------------------------------------------------------------------
///
/// Implements rewrite_roots: for each root that is a minor pointer with a
/// forwarding entry, replace it with the new major-heap address.

module GC.Gen.Impl.UpdatePtrs

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Impl.Heap
module PromoteSpec = GC.Gen.Promote

/// ---------------------------------------------------------------------------
/// Pure helper: compute rewrite for a single value
/// ---------------------------------------------------------------------------

/// Compute what rewrite_root does, purely in terms of the array contents
let rewrite_root_arr (farr: Seq.seq U64.t) (v: U64.t) : GTot U64.t =
  if Seq.length farr = fwd_array_size &&
     U64.v v >= 8 && U64.v v < minor_heap_size && U64.v v % 8 = 0 then
    let idx = U64.v v / 8 in
    let fv = Seq.index farr idx in
    if fv <> 0UL then fv else v
  else v

/// Connection lemma: rewrite_root_arr matches rewrite_root when represents_fwd holds
let rewrite_root_arr_spec (farr: Seq.seq U64.t)
                          (fwd: PromoteSpec.forwarding_map) (v: U64.t)
  : Lemma (requires Seq.length farr == fwd_array_size /\ represents_fwd farr fwd)
          (ensures rewrite_root_arr farr v == PromoteSpec.rewrite_root v fwd) =
  ()

/// Safe wrapper: compute the result of rewriting at a given index
let rewrite_at_spec (rs: Seq.seq U64.t) (farr: Seq.seq U64.t) (iv: nat) : GTot (Seq.seq U64.t) =
  if iv < Seq.length rs && Seq.length farr = fwd_array_size
  then Seq.upd rs iv (rewrite_root_arr farr (Seq.index rs iv))
  else rs

/// ---------------------------------------------------------------------------
/// Rewrite one root at a given index (factored out for clean branch merging)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_at_index (roots: array U64.t) (fwd_arr: array U64.t) (iv: SZ.t)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v iv < Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (rs2 == rewrite_at_spec 'rs 'farr (SZ.v iv))
{
  let r = roots.(iv);
  if U64.gte r 8UL {
    if U64.lt r minor_heap_size_u64 {
      if U64.eq (U64.rem r 8UL) 0UL {
        let idx = SZ.uint64_to_sizet (U64.div r 8UL);
        let fwd_val = fwd_arr.(idx);
        if U64.eq fwd_val 0UL {
          roots.(iv) <- r
        } else {
          roots.(iv) <- fwd_val
        }
      } else {
        roots.(iv) <- r
      }
    } else {
      roots.(iv) <- r
    }
  } else {
    roots.(iv) <- r
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// Rewrite roots loop
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
inline_for_extraction
fn rewrite_roots_impl
  (roots: array U64.t)
  (fwd_arr: array U64.t)
  (n: SZ.t)
  requires pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (SZ.v n == Seq.length 'rs /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr 'fwd)
  ensures exists* rs2.
    pts_to roots rs2 **
    pts_to fwd_arr 'farr **
    pure (Seq.length rs2 == Seq.length 'rs /\
          rs2 == PromoteSpec.rewrite_roots 'rs 'fwd)
{
  let mut i = 0sz;
  while (SZ.lt !i n)
    invariant exists* rs_i iv.
      pts_to roots rs_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (SZ.v iv <= Seq.length 'rs /\
            SZ.v n == Seq.length 'rs /\
            Seq.length rs_i == Seq.length 'rs /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr 'fwd /\
            (forall (j: nat). j < SZ.v iv ==>
              Seq.index rs_i j == PromoteSpec.rewrite_root (Seq.index 'rs j) 'fwd) /\
            (forall (j: nat). j >= SZ.v iv /\ j < Seq.length 'rs ==>
              Seq.index rs_i j == Seq.index 'rs j))
  {
    let iv = !i;
    rewrite_at_index roots fwd_arr iv;
    rewrite_root_arr_spec 'farr 'fwd (Seq.index 'rs (SZ.v iv));
    i := SZ.add iv 1sz
  };
  // After loop: iv == n, so forall j < n. Seq.index rs_final j == rewrite_root ...
  // Bind the array witness and establish the connection
  with rs_final. assert (pts_to roots rs_final);
  assert (pure (Seq.length rs_final == Seq.length 'rs));
  assert (pure (forall (j: nat). j < Seq.length 'rs ==>
    Seq.index rs_final j == PromoteSpec.rewrite_root (Seq.index 'rs j) 'fwd));
  PromoteSpec.rewrite_roots_pointwise 'rs 'fwd rs_final;
  PromoteSpec.rewrite_roots_length 'rs 'fwd
}
#pop-options

/// ---------------------------------------------------------------------------
/// Update pointers in one object's fields
/// ---------------------------------------------------------------------------

module U8 = FStar.UInt8

/// Factored-out helper: handle one field in the pointer update loop.
/// Reads field, checks if minor pointer + forwarded, conditionally writes.
#push-options "--z3rlimit 150 --fuel 0 --ifuel 0"
inline_for_extraction
fn update_one_field (major: heap_t) (fwd_arr: array U64.t)
                    (obj: U64.t) (wosize: U64.t) (iv: U64.t)
                    (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v iv < U64.v wosize /\
                 U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
                 U64.v obj + U64.v wosize * 8 <= heap_size /\
                 U64.v wosize > 0 /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (PromoteSpec.update_object_pointers ms2 obj (U64.v wosize) fwd (U64.v iv + 1) ==
          PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd (U64.v iv))
{
  let field_addr_u64 = U64.add obj (U64.mul iv 8UL);
  let field_val = read_word major field_addr_u64;
  // Invoke the unfold lemma to establish the one-step equality
  PromoteSpec.update_object_pointers_step 'ms obj (U64.v wosize) fwd (U64.v iv);
  if U64.gte field_val 8UL {
    if U64.lt field_val minor_heap_size_u64 {
      if U64.eq (U64.rem field_val 8UL) 0UL {
        // Minor pointer — look up forwarding
        let idx = SZ.uint64_to_sizet (U64.div field_val 8UL);
        let fwd_val = fwd_arr.(idx);
        if U64.eq fwd_val 0UL {
          ()
        } else {
          write_word major field_addr_u64 fwd_val
        }
      } else {
        ()
      }
    } else {
      ()
    }
  } else {
    ()
  }
}
#pop-options

/// Update pointers in one object: iterate fields [0, wosize) and rewrite
/// minor-heap pointers via the forwarding array.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
inline_for_extraction
fn update_one_object (major: heap_t) (fwd_arr: array U64.t)
                     (obj: U64.t) (wosize: U64.t)
                     (#fwd: erased PromoteSpec.forwarding_map)
  requires is_heap major 'ms **
           pts_to fwd_arr 'farr **
           pure (U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
                 U64.v wosize > 0 /\
                 U64.v obj + U64.v wosize * 8 <= heap_size /\
                 Seq.length 'farr == fwd_array_size /\
                 represents_fwd 'farr fwd)
  ensures exists* ms2.
    is_heap major ms2 **
    pts_to fwd_arr 'farr **
    pure (ms2 == PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0)
{
  let mut i = 0UL;
  while (U64.lt !i wosize)
    invariant exists* ms_i iv.
      is_heap major ms_i **
      pts_to fwd_arr 'farr **
      R.pts_to i iv **
      pure (U64.v iv <= U64.v wosize /\
            U64.v obj >= 8 /\ U64.v obj % 8 == 0 /\
            U64.v obj + U64.v wosize * 8 <= heap_size /\
            U64.v wosize > 0 /\
            Seq.length 'farr == fwd_array_size /\
            represents_fwd 'farr fwd /\
            PromoteSpec.update_object_pointers ms_i obj (U64.v wosize) fwd (U64.v iv) ==
            PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0)
  {
    let iv = !i;
    update_one_field major fwd_arr obj wosize iv #fwd;
    i := U64.add iv 1UL
  };
  // After loop: iv == wosize, so update_object_pointers ms_final ... wosize == ms_final
  with ms_final. assert (is_heap major ms_final);
  with iv_final. assert (R.pts_to i iv_final);
  PromoteSpec.update_object_pointers_done ms_final obj (U64.v wosize) fwd (U64.v iv_final);
  // Now we know:
  //   (1) update_object_pointers ms_final obj wosize fwd (v iv_final) == ms_final  [from done lemma]
  //   (2) update_object_pointers ms_final obj wosize fwd (v iv_final) == update_object_pointers 'ms obj wosize fwd 0  [from invariant]
  // Therefore ms_final == update_object_pointers 'ms obj wosize fwd 0
  assert (pure (ms_final == PromoteSpec.update_object_pointers 'ms obj (U64.v wosize) fwd 0))
}
#pop-options
