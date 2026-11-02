module GC.Gen.SweepPhase.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FusedSweep
open GC.Spec.SweepPhase.Intrinsic
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module PCS = GC.Gen.PostCollectionShape

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let sweep_major_shape g fp st =
  sweep_phase_inv_elim g fp st;
  pending_ok_lemma g st;
  PCS.free_list_shape_of_ascending g fp;
  wf_except_parts ();
  GenInv.major_shape_except_intro g fp (pending g st)

let sweep_collection_shape minor g fp st =
  sweep_major_shape g fp st;
  GenInv.collection_shape_except_intro minor g fp (pending g st)

