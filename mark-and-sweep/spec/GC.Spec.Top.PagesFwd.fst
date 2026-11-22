/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesFwd - the forwarding map, on the model
/// ---------------------------------------------------------------------------
///
/// The minor collection's forwarding map is the lookup in the list of
/// promotions (`PagesMinor.fwd_of`, over `PagesQueue.copies`).  Its entries
/// are exactly the queued objects' (`fwd_some`, `fwd_queue`), when no two
/// queued objects share a young block.

module GC.Spec.Top.PagesFwd

open FStar.Seq
open GC.Gen.Promote
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Q = GC.Spec.Top.PagesQueue
module ByteFacts = GC.Spec.Top.ByteFacts

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let fwd_of (cps: list (nat & nat)) (o: nat) : option nat = L.assoc o cps

/// No two of the first `n` queued objects share a young block.
let keys_distinct (q: seq U64.t) (n: nat) : prop =
  forall (i j: nat). i < n /\ j < n /\ i < Seq.length q /\ j < Seq.length q /\
    Q.yof (Seq.index q i) == Q.yof (Seq.index q j) ==> i == j

/// An entry is a queued object's.
let rec fwd_some (q: seq U64.t) (fwd: forwarding_map) (n: nat) (o c: nat)
  : Lemma (requires L.assoc o (Q.copies q fwd n) == Some c)
          (ensures exists (i: nat). i < n /\ i < Seq.length q /\ o == Q.yof (Seq.index q i) /\
                               c == ByteFacts.maddr (fwd (Seq.index q i)))
          (decreases n)
  = if n = 0 || n > Seq.length q then ()
    else if o = Q.yof (Seq.index q (n - 1)) then ()
    else fwd_some q fwd (n - 1) o c

/// A queued object's entry.
let rec fwd_queue (q: seq U64.t) (fwd: forwarding_map) (n: nat) (i: nat)
  : Lemma (requires keys_distinct q n /\ i < n /\ n <= Seq.length q)
          (ensures L.assoc (Q.yof (Seq.index q i)) (Q.copies q fwd n) == Some (ByteFacts.maddr (fwd (Seq.index q i))))
          (decreases n)
  = if i = n - 1 then ()
    else begin
      assert (Q.yof (Seq.index q i) <> Q.yof (Seq.index q (n - 1)));
      fwd_queue q fwd (n - 1) i
    end

/// The members of the list are its entries.
let rec mem_some (q: seq U64.t) (fwd: forwarding_map) (n: nat) (o c: nat)
  : Lemma (requires L.memP (o, c) (Q.copies q fwd n))
          (ensures exists (i: nat). i < n /\ i < Seq.length q /\ o == Q.yof (Seq.index q i) /\
                               c == ByteFacts.maddr (fwd (Seq.index q i)))
          (decreases n)
  = if n = 0 || n > Seq.length q then ()
    else if (o, c) = (Q.yof (Seq.index q (n - 1)), ByteFacts.maddr (fwd (Seq.index q (n - 1)))) then ()
    else mem_some q fwd (n - 1) o c

let rec some_mem (cps: list (nat & nat)) (o c: nat)
  : Lemma (requires L.assoc o cps == Some c) (ensures L.memP (o, c) cps)
  = match cps with
    | [] -> ()
    | (k, v) :: tl -> if o = k then () else some_mem tl o c
