module Test

#lang-pulse

open Pulse.Lib.Pervasives
module U64 = FStar.UInt64

fn test_mut ()
  requires emp
  ensures emp
{
  let mut i = 1UL;
  
  while (U64.lte !i 10UL)
    invariant exists* vi. pts_to i vi ** pure (U64.v vi >= 1)
  {
    let curr = !i;
    i := U64.add curr 1UL
  }
}
