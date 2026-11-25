/// The nursery's base address is 0 (`GC.Gen.Base.minor_base_addr`, abstract
/// in its interface): a pointer into the nursery is its offset, so it is
/// young (`GC.Gen.Barrier.is_young`), whatever block of the nursery it
/// points into.  Used by the hoisted-run corollary (`GC.Gen.Run.Hoisted`).
module GC.Gen.Run.MinorBase

module U64 = FStar.UInt64

val minor_base_addr_zero (_: unit) : Lemma (GC.Gen.Base.minor_base_addr == 0UL)
