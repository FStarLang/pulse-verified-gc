/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrRef - the reference semantics: bookkeeping for T1
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  The reference store's names are exactly those below
/// `next` (`rwf`); appending an event to a program runs it on the store
/// after the program (`rat_snoc`); program events counted along a run
/// (`mc_succ`).

module GC.Spec.Top.TrRef

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Transp
module L = FStar.List.Tot
module RF = GC.Spec.Top.RunFacts
module RA = GC.Spec.Top.RunApp

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// The store's names: those below `next`.
let rwf (r: rstore) : prop = forall (k: nat). Some? (r.objs k) <==> k < r.next

let rwf_init () : Lemma (rwf rinit) = ()

let rwf_step (r: rstore) (e: revent) : Lemma (requires rwf r) (ensures rwf (rstep r e))
  = match e with
    | RWrite k _ _ -> (match r.objs k with Some _ -> () | None -> ())
    | RRead k _ -> (match r.objs k with Some _ -> () | None -> ())
    | _ -> ()

let rec rwf_exec (r: rstore) (ps: list revent) : Lemma (requires rwf r) (ensures rwf (rexec r ps)) (decreases ps)
  = match ps with
    | [] -> ()
    | e :: tl -> rwf_step r e; rwf_exec (rstep r e) tl

let rwf_rat (prog: list revent) (m: nat) : Lemma (rwf (rat prog m))
  = rwf_init (); rwf_exec rinit (take m prog)

let rec rexec_snoc (r: rstore) (ps: list revent) (e: revent)
  : Lemma (ensures rexec r (L.append ps [e]) == rstep (rexec r ps) e) (decreases ps)
  = match ps with
    | [] -> assert_norm (rexec (rstep r e) [] == rstep r e)
    | e0 :: tl -> rexec_snoc (rstep r e0) tl e

let rec take_all (#t: Type) (l: list t) : Lemma (ensures take (L.length l) l == l) (decreases l)
  = match l with [] -> () | _ :: tl -> take_all tl

/// **Appending an event to the program.**
let rat_snoc_pre (prog: list revent) (re: revent) (m: nat)
  : Lemma (requires m <= L.length prog) (ensures rat (L.append prog [re]) m == rat prog m)
  = RA.take_app_le m prog [re]

let rat_snoc_last (prog: list revent) (re: revent)
  : Lemma (ensures rat (L.append prog [re]) (L.length prog + 1) == rstep (rat prog (L.length prog)) re)
  = L.append_length prog [re];
    assert_norm (L.length [re] == 1);
    take_all (L.append prog [re]);
    take_all prog;
    rexec_snoc rinit prog re;
    assert (take (L.length prog + 1) (L.append prog [re]) == L.append prog [re]);
    assert (take (L.length prog) prog == prog);
    assert (rat (L.append prog [re]) (L.length prog + 1) == rexec rinit (L.append prog [re]));
    assert (rat prog (L.length prog) == rexec rinit prog)

let rev_at_snoc (prog: list revent) (re: revent)
  : Lemma (ensures L.length (L.append prog [re]) == L.length prog + 1 /\
                   rev_at (L.append prog [re]) (L.length prog) == re)
  = L.append_length prog [re];
    assert_norm (L.length [re] == 1);
    RA.index_app_ge prog [re] 0;
    assert_norm (L.index [re] 0 == re)

let rec mcount_append (a b: list event)
  : Lemma (ensures mcount (L.append a b) == mcount a + mcount b) (decreases a)
  = match a with [] -> () | _ :: tl -> mcount_append tl b

let mcount_one (e: event) : Lemma (mcount [e] == (if is_mutator_event e then 1 else 0))
  = assert_norm (mcount [e] == (if is_mutator_event e then 1 else 0) + mcount [])

/// Program events counted along a run.
let mc_succ (es: list event) (i: nat)
  : Lemma (requires i < L.length es)
          (ensures mc es (i + 1) == mc es i + (if is_mutator_event (ev es i) then 1 else 0))
  = RF.take_snoc i es;
    mcount_append (take i es) [L.index es i];
    mcount_one (L.index es i)

let mc_zero (es: list event) : Lemma (mc es 0 == 0) = ()
