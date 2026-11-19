/// ---------------------------------------------------------------------------
/// GC.Gen.Run.MinorRefTable - after a minor collection the empty remembered
/// set covers the major heap
/// ---------------------------------------------------------------------------
///
/// A minor collection (`minor_step`) empties the remembered set.  That is
/// sound because it leaves no nursery pointer in any field of a scannable
/// block that is not free at the phase: an old block's nursery pointers were
/// at remembered slots, so their targets were among the collector's roots and
/// were forwarded; a promoted copy's nursery pointers are its nursery
/// fields, which name nursery objects (`nursery_fields_valid`) that the BFS
/// forwarded with it.  Every such field is rewritten to a major address.

module GC.Gen.Run.MinorRefTable

open FStar.Seq
open GC.Gen.Run.Step
open GC.Gen.Run.Invariant.Defs

module GI = GC.Gen.Incremental
module RT = GC.Gen.RefTable

val minor_ref_table_empty (r: real_state) (roots: seq FStar.UInt64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ minor_step r roots r')
          (ensures RT.ref_table_covers_with (GI.phase_free r'.phase) r'.memory.major Seq.empty 0)
