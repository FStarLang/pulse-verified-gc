module GC.Gen.SPOT.MinimalRepro

open FStar.Seq
open FStar.UInt64

/// Minimal reproduction of dependent tuple syntax issue

// This works: assume val returning a dependent tuple
assume val make_tuple : unit -> (x:UInt64.t & y:UInt64.t & squash (v x < v y))

// This FAILS: trying to extract components from the dependent tuple
let get_first () : UInt64.t =
  let (|x, _, _|) = make_tuple () in x

// Alternative approach: separate assume vals (this works)
assume val get_x : unit -> UInt64.t
assume val get_y : unit -> UInt64.t
assume val x_less_than_y : unit -> Lemma (v (get_x ()) < v (get_y ()))
