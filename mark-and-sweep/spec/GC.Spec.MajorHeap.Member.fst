module GC.Spec.MajorHeap.Member

module Seq = FStar.Seq
module MH = GC.Spec.MajorHeap

open GC.Spec.Base

#push-options "--split_queries always --z3rlimit 5 --fuel 1 --ifuel 1"
let major_objects_member_at_index_small
  (mh: MH.major_heap) (idx: nat) (x: obj_addr)
  : Lemma
      (requires
        idx < Seq.length mh /\
        Seq.mem x (MH.objects_in_chunk (Seq.index mh idx)))
      (ensures Seq.mem x (MH.major_objects mh))
  =
  MH.major_objects_member_at_index mh idx x

let major_objects_member_at_equal_index_small
  (mh: MH.major_heap) (idx: nat) (c: MH.heap_chunk) (x: obj_addr)
  : Lemma
      (requires
        idx < Seq.length mh /\
        Seq.index mh idx == c /\
        Seq.mem x (MH.objects_in_chunk c))
      (ensures Seq.mem x (MH.major_objects mh))
  =
  assert (Seq.mem x (MH.objects_in_chunk (Seq.index mh idx)));
  major_objects_member_at_index_small mh idx x
#pop-options
