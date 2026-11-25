/// ---------------------------------------------------------------------------
/// GC.Spec.Top.T1Re - T1, part 2: facts of the reference program
/// ---------------------------------------------------------------------------
///
/// Design doc §16.18.  The store after `m + 1` events is one step from the
/// store after `m` (`rat_succ`); a prefix of the program runs the same
/// stores (`rat_take`, `rev_take`).  A legal program allocates objects of
/// at least one field (`rpos_at`).

module GC.Spec.Top.T1Re

open GC.Spec.Top.Heap
open GC.Spec.Top.Run
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
module L = FStar.List.Tot
module RF = GC.Spec.Top.RunFacts
module RA = GC.Spec.Top.RunApp

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let rat_succ (prog: list revent) (m: nat)
  : Lemma (requires m < L.length prog) (ensures rat prog (m + 1) == rstep (rat prog m) (rev_at prog m))
  = RF.take_snoc m prog;
    rexec_snoc rinit (take m prog) (L.index prog m)

let rat_take (prog: list revent) (k m: nat)
  : Lemma (requires m <= k) (ensures rat (take k prog) m == rat prog m)
  = RA.take_take m k prog

let rev_take (prog: list revent) (k m: nat)
  : Lemma (requires m < k /\ k <= L.length prog)
          (ensures L.length (take k prog) == k /\ rev_at (take k prog) m == rev_at prog m)
  = RA.take_len k prog;
    RA.index_take m k prog

/// One more event of a prefix.
let take_succ_rev (prog: list revent) (m: nat)
  : Lemma (requires m < L.length prog) (ensures take (m + 1) prog == L.append (take m prog) [rev_at prog m])
  = RF.take_snoc m prog

/// ---------------------------------------------------------------------------
/// Objects have a field
/// ---------------------------------------------------------------------------

let rpos (r: rstore) : prop = forall (k: nat). Some? (r.objs k) ==> (Some?.v (r.objs k)).rsz >= 1

let rpos_step (r: rstore) (e: revent) : Lemma (requires rpos r /\ rok r e) (ensures rpos (rstep r e))
  = ()

let rok_all (prog: list revent) : prop = forall (m: nat). m < L.length prog ==> rok (rat prog m) (rev_at prog m)

let rec rpos_at (prog: list revent) (m: nat)
  : Lemma (requires rok_all prog /\ m <= L.length prog) (ensures rpos (rat prog m)) (decreases m)
  = if m = 0 then ()
    else begin
      rpos_at prog (m - 1);
      rat_succ prog (m - 1);
      rpos_step (rat prog (m - 1)) (rev_at prog (m - 1))
    end
