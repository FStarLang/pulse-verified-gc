/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Guard - the nursery's run-time guards, where followed
/// ---------------------------------------------------------------------------
///
/// The Pulse forwarding step decides that an address is a nursery object by
/// run-time guards (aligned, in the nursery, a header with a body that fits,
/// not an infix tag).  akhil's `minor_guards_complete` makes the guards
/// sufficient at every address of the nursery; a field can hold a word that
/// reads as such a header, so the model's nurseries need not meet it.  As
/// for infix addresses (design doc §12), it is asked only where the
/// promotion looks: at the roots (`roots_gd`) and at the scanned fields of
/// nursery objects (`fields_gd`).  akhil's condition gives both
/// (`gd_of_complete`).

module GC.Spec.Pages.Promote.Guard

open FStar.Seq
open GC.Gen.Base
open GC.Gen.MinorHeap

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The guards pass at `addr` only for a nursery object.
let gd_ok (ms: minor_state) (addr: U64.t) : prop =
  U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0 /\
  minor_wosize ms addr > 0 /\ U64.v addr + minor_wosize ms addr * 8 <= minor_heap_size /\
  minor_tag ms addr <> 249 ==> Seq.mem addr (minor_objects ms)

/// At every scanned field of a nursery object.
[@@"opaque_to_smt"]
let fields_gd (ms: minor_state) : prop =
  forall (obj: U64.t) (j: nat).
    Seq.mem obj (minor_objects ms) /\ j < minor_scan_wosize ms obj ==>
    gd_ok ms (to_minor_offset (minor_read_field ms obj j))

let fields_gd_elim (ms: minor_state) (obj: U64.t) (j: nat)
  : Lemma (requires fields_gd ms /\ Seq.mem obj (minor_objects ms) /\ j < minor_scan_wosize ms obj)
          (ensures gd_ok ms (to_minor_offset (minor_read_field ms obj j)))
  = reveal_opaque (`%fields_gd) (fields_gd ms)

let fields_gd_intro (ms: minor_state)
  (h: (obj: U64.t) -> (j: nat) ->
       Lemma (requires Seq.mem obj (minor_objects ms) /\ j < minor_scan_wosize ms obj)
             (ensures gd_ok ms (to_minor_offset (minor_read_field ms obj j))))
  : Lemma (fields_gd ms)
  = reveal_opaque (`%fields_gd) (fields_gd ms);
    let one (obj: U64.t) (j: nat)
      : Lemma (Seq.mem obj (minor_objects ms) /\ j < minor_scan_wosize ms obj ==>
               gd_ok ms (to_minor_offset (minor_read_field ms obj j)))
      = FStar.Classical.move_requires (h obj) j in
    FStar.Classical.forall_intro_2 one

/// At every root.
let roots_gd (ms: minor_state) (roots: seq U64.t) : prop =
  forall (i: nat). i < Seq.length roots ==> gd_ok ms (Seq.index roots i)

/// akhil's condition gives both.
let gd_of_complete (ms: minor_state) (roots: seq U64.t)
  : Lemma (requires minor_guards_complete ms) (ensures fields_gd ms /\ roots_gd ms roots)
  = reveal_opaque (`%minor_guards_complete) minor_guards_complete;
    fields_gd_intro ms (fun obj j -> ())
