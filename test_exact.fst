module TestExact

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Fields
module U64 = FStar.UInt64

fn test_for_each (heap: heap_t) (h_addr: hp_addr) (wz: wosize)
                  (callback: hp_addr -> stt unit (requires emp) (ensures fun _ -> emp))
  requires is_heap heap 's
  ensures  is_heap heap 's
{
  let mut i = 1UL;
  
  while (U64.lte !i wz)
    invariant exists* vi.
      pts_to i vi **
      is_heap heap 's **
      pure (U64.v vi >= 1 /\ U64.v vi <= U64.v wz + 1)
  {
    let v = read_field heap h_addr !i;
    let is_ptr = is_pointer v;
    if (is_ptr) {
      callback (hd_address v)
    };
    i := U64.add !i 1UL
  }
}
