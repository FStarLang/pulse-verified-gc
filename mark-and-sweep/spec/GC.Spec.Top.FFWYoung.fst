/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWYoung - the witness runs' young allocations
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  The runs allocate two one-field young blocks in the empty
/// nursery: Y1 at 0, whose field is an infix pointer into the old closure K,
/// and Y2 at 2, whose field is an integer that reads as an infix header.

module GC.Spec.Top.FFWYoung

open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.FFWState
module M = GC.Spec.Top.Heap
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Y = GC.Spec.Top.Young
module FM0 = GC.Spec.Top.FFWMinor0
module GMH = GC.Gen.MinorHeap
module GB = GC.Gen.Base

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let ms1 (v: M.value) : GTot GMH.minor_state =
  match Y.yalloc FM0.ms0 1 0 [v] with Some (_, ms) -> ms | None -> FM0.ms0

let ms2 (v w: M.value) : GTot GMH.minor_state =
  match Y.yalloc (ms1 v) 1 0 [w] with Some (_, ms) -> ms | None -> FM0.ms0

#push-options "--fuel 1"
let yal1 (v: M.value)
  : Lemma (requires ff_room)
          (ensures Y.yalloc FM0.ms0 1 0 [v] == Some (0, ms1 v) /\ U64.v (ms1 v).GMH.bump == 16)
  = base_facts ()

let yal2 (v w: M.value)
  : Lemma (requires ff_room)
          (ensures Y.yalloc (ms1 v) 1 0 [w] == Some (2, ms2 v w))
  = base_facts ();
    yal1 v
#pop-options

let ym1 (v: M.value) : M.mheap = M.young_alloc (M.empty_heap ywords) 0 1 0 [v]
let ym2 (v w: M.value) : M.mheap = M.young_alloc (ym1 v) 2 1 0 [w]

let yblocks (v w: M.value)
  : Lemma (requires ff_room)
          (ensures M.resolve (ym1 v) 0 == Some 0 /\ M.resolve (ym2 v w) 0 == Some 0 /\ M.resolve (ym2 v w) 2 == Some 2)
  = ()
