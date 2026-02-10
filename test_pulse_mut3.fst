module Test3

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
module U64 = FStar.UInt64

fn test_mut (heap: heap_t) (h_addr: hp_addr)
  (callback: hp_addr -> stt unit (requires emp) (ensures fun _ -> emp))
  requires is_heap heap 's
  ensures is_heap heap 's  
{
  let mut i = 1UL;
  
  while (U64.lte !i 10UL)
    invariant exists* vi. pts_to i vi ** is_heap heap 's ** pure (U64.v vi >= 1)
  {
    let curr = !i;
    
    let v = read_word heap h_addr;
    
    if (U64.gt v 0UL) {
      callback h_addr
    };
    
    i := U64.add curr 1UL
  }
}
