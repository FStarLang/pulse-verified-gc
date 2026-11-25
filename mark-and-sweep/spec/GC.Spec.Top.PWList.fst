/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWList - the pages witness runs' event lists
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  The runs' event lists are a fixed prefix, the sweep's
/// steps (`PWSweep.repl k`, `k` the steps left), and a fixed suffix.  Their
/// events by index, the configuration after a prefix, and the check that
/// every kind of event occurs.

module GC.Spec.Top.PWList

open GC.Spec.Top.Run
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module RF = GC.Spec.Top.RunFacts
module PWS = GC.Spec.Top.PWSweep

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let rec repl_len (k: nat) : Lemma (L.length (PWS.repl k) == k) = if k = 0 then () else repl_len (k - 1)

let rec repl_idx (k i: nat)
  : Lemma (requires i < k) (ensures i < L.length (PWS.repl k) /\ L.index (PWS.repl k) i == ESweep) (decreases k)
  = repl_len k;
    if i = 0 then () else repl_idx (k - 1) (i - 1)

/// The run `p @ (repl k @ q)`: its length and its events.
let es3 (p: list event) (k: nat) (q: list event) : list event = L.append p (L.append (PWS.repl k) q)

let len3 (p: list event) (k: nat) (q: list event)
  : Lemma (L.length (es3 p k q) == L.length p + k + L.length q)
  = repl_len k;
    L.append_length (PWS.repl k) q;
    L.append_length p (L.append (PWS.repl k) q)

let ev_p (p: list event) (k: nat) (q: list event) (i: nat)
  : Lemma (requires i < L.length p) (ensures i < L.length (es3 p k q) /\ ev (es3 p k q) i == L.index p i)
  = len3 p k q;
    RA.index_app_lt p (L.append (PWS.repl k) q) i

let ev_r (p: list event) (k: nat) (q: list event) (i: nat)
  : Lemma (requires i < k) (ensures L.length p + i < L.length (es3 p k q) /\ ev (es3 p k q) (L.length p + i) == ESweep)
  = len3 p k q;
    repl_len k;
    L.append_length (PWS.repl k) q;
    RA.index_app_ge p (L.append (PWS.repl k) q) i;
    RA.index_app_lt (PWS.repl k) q i;
    repl_idx k i

let ev_q (p: list event) (k: nat) (q: list event) (i: nat)
  : Lemma (requires i < L.length q)
          (ensures L.length p + k + i < L.length (es3 p k q) /\ ev (es3 p k q) (L.length p + k + i) == L.index q i)
  = len3 p k q;
    repl_len k;
    L.append_length (PWS.repl k) q;
    RA.index_app_ge p (L.append (PWS.repl k) q) (k + i);
    RA.index_app_ge (PWS.repl k) q i

/// The configuration after the prefix and some of the rest.
let at_p (c: comps) (n ny: nat) (p: list event) (k: nat) (q: list event) (i: nat)
  : Lemma (at c n ny (es3 p k q) (L.length p + i) ==
           exec c (exec c (init_config c n ny) p) (take i (L.append (PWS.repl k) q)))
  = RA.take_app_ge i p (L.append (PWS.repl k) q);
    RF.exec_append c (init_config c n ny) p (take i (L.append (PWS.repl k) q))

let at_q (c: comps) (n ny: nat) (p: list event) (k: nat) (q: list event) (i: nat)
  : Lemma (at c n ny (es3 p k q) (L.length p + k + i) ==
           exec c (exec c (exec c (init_config c n ny) p) (PWS.repl k)) (take i q))
  = repl_len k;
    at_p c n ny p k q (k + i);
    RA.take_app_ge i (PWS.repl k) q;
    RF.exec_append c (exec c (init_config c n ny) p) (PWS.repl k) (take i q)

/// Every kind of event.
let every_event (es: list event) : bool =
  L.existsb EAlloc? es && L.existsb EYoungAlloc? es && L.existsb EWrite? es && L.existsb ERead? es &&
  L.existsb ERoots? es &&
  L.existsb EMinor? es && L.existsb EStart? es && L.existsb ESlice? es && L.existsb EHandover? es &&
  L.existsb ESweep? es && L.existsb EEnd? es

let rec existsb_app (f: event -> bool) (a b: list event)
  : Lemma (L.existsb f (L.append a b) == (L.existsb f a || L.existsb f b))
  = match a with [] -> () | _ :: tl -> existsb_app f tl b

#push-options "--fuel 2"
let rec exists_repl (g: event -> bool) (j: nat)
  : Lemma (requires j > 0) (ensures L.existsb g (PWS.repl j) == g ESweep) (decreases j)
  = if j = 1 then () else exists_repl g (j - 1)
#pop-options

let every3 (p: list event) (k: nat) (q: list event)
  : Lemma (requires k > 0) (ensures every_event (es3 p k q) == every_event (L.append p (ESweep :: q)))
  = let f (g: event -> bool) : Lemma (L.existsb g (es3 p k q) == L.existsb g (L.append p (ESweep :: q)))
      = existsb_app g p (L.append (PWS.repl k) q);
        existsb_app g (PWS.repl k) q;
        existsb_app g p (ESweep :: q);
        exists_repl g k in
    f EAlloc?; f EYoungAlloc?; f EWrite?; f ERead?; f ERoots?; f EMinor?; f EStart?; f ESlice?;
    f EHandover?; f ESweep?; f EEnd?
