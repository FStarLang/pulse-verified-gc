module Test2

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
module U64 = FStar.UInt64

fn test_mut (heap: heap_t)
  requires is_heap heap 's
  ensures is_heap heap 's  
{
  let mut i = 1UL;
  
  while (U64.lte !i 10UL)
    invariant exists* vi. pts_to i vi ** is_heap heap 's ** pure (U64.v vi >= 1)
  {
    let curr = !i;
    i := U64.add curr 1UL
  }
}
