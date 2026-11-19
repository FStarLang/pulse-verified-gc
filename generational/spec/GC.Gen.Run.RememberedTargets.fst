module GC.Gen.Run.RememberedTargets

friend GC.Gen.MinorCollectForwarding.Helpers

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap

module U64 = FStar.UInt64
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module GBase = GC.Gen.Base
module Promote = GC.Gen.Promote

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec mem_from (major: heap) (slots: seq U64.t) (n idx: nat) (t: U64.t)
  : Lemma (ensures Seq.mem t (MCFH.remembered_slot_targets_from major slots n idx) <==>
                   (exists (i: nat). idx <= i /\ slot_target major slots n i t))
          (decreases (n - idx))
  = if idx >= n || idx >= Seq.length slots then ()
    else begin
      let slot = Seq.index slots idx in
      let rest = MCFH.remembered_slot_targets_from major slots n (idx + 1) in
      mem_from major slots n (idx + 1) t;
      if U64.v slot < heap_size && U64.v slot % U64.v mword = 0 then begin
        let v = GBase.to_minor_offset (read_word major (slot <: hp_addr)) in
        if Promote.is_minor_pointer v then Seq.Properties.mem_cons v rest
      end
    end
#pop-options

let remembered_mem major slots n t = mem_from major slots n 0 t
