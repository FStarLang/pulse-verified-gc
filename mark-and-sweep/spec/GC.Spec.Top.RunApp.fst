/// ---------------------------------------------------------------------------
/// GC.Spec.Top.RunApp - a run that follows another up to a point, then goes
/// its own way
/// ---------------------------------------------------------------------------
///
/// Design doc §16.7 (T2).  `es' = take s es @ tl`: up to `s` it is `es`
/// (`at_pre`, `ev_pre`); after, it runs `tl` from `at es s` (`at_tail`,
/// `ev_tail`).  `tail_ok` asks of `tl` what `run_ok` and `run_hyps` ask of
/// each step; with it, `es'` is a run (`run_of_tail`).

module GC.Spec.Top.RunApp

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
module L = FStar.List.Tot
module C = FStar.Classical
module RF = GC.Spec.Top.RunFacts

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Lists
/// ---------------------------------------------------------------------------

let rec take_len (#t: Type) (i: nat) (l: list t)
  : Lemma (requires i <= L.length l) (ensures L.length (take i l) == i) (decreases l)
  = match l with [] -> () | _ :: tl -> if i = 0 then () else take_len (i - 1) tl

let rec take_app_le (#t: Type) (i: nat) (p q: list t)
  : Lemma (requires i <= L.length p) (ensures take i (L.append p q) == take i p) (decreases p)
  = match p with [] -> () | _ :: tl -> if i = 0 then () else take_app_le (i - 1) tl q

let rec take_app_ge (#t: Type) (k: nat) (p q: list t)
  : Lemma (ensures take (L.length p + k) (L.append p q) == L.append p (take k q)) (decreases p)
  = match p with [] -> () | _ :: tl -> take_app_ge k tl q

let rec take_take (#t: Type) (i j: nat) (l: list t)
  : Lemma (requires i <= j) (ensures take i (take j l) == take i l) (decreases l)
  = match l with [] -> () | _ :: tl -> if i = 0 then () else take_take (i - 1) (j - 1) tl

let rec index_take (#t: Type) (i j: nat) (l: list t)
  : Lemma (requires i < j /\ j <= L.length l)
          (ensures i < L.length (take j l) /\ L.index (take j l) i == L.index l i) (decreases l)
  = take_len j l;
    match l with _ :: tl -> if i = 0 then () else index_take (i - 1) (j - 1) tl

let rec index_app_lt (#t: Type) (p q: list t) (i: nat)
  : Lemma (requires i < L.length p)
          (ensures i < L.length (L.append p q) /\ L.index (L.append p q) i == L.index p i) (decreases p)
  = L.append_length p q;
    match p with _ :: tl -> if i = 0 then () else index_app_lt tl q (i - 1)

let rec index_app_ge (#t: Type) (p q: list t) (k: nat)
  : Lemma (requires k < L.length q)
          (ensures L.length p + k < L.length (L.append p q) /\ L.index (L.append p q) (L.length p + k) == L.index q k)
          (decreases p)
  = L.append_length p q;
    match p with [] -> () | _ :: tl -> index_app_ge tl q k

/// ---------------------------------------------------------------------------
/// The two runs
/// ---------------------------------------------------------------------------

let at_pre (c: comps) (n ny: nat) (es: list event) (s: nat) (tl: list event) (i: nat)
  : Lemma (requires s <= L.length es /\ i <= s)
          (ensures at c n ny (L.append (take s es) tl) i == at c n ny es i)
  = take_len s es;
    take_app_le i (take s es) tl;
    take_take i s es

let at_tail (c: comps) (n ny: nat) (es: list event) (s: nat) (tl: list event) (k: nat)
  : Lemma (requires s <= L.length es)
          (ensures at c n ny (L.append (take s es) tl) (s + k) == exec c (at c n ny es s) (take k tl))
  = take_len s es;
    take_app_ge k (take s es) tl;
    RF.exec_append c (init_config c n ny) (take s es) (take k tl)

let len_app (es: list event) (s: nat) (tl: list event)
  : Lemma (requires s <= L.length es) (ensures L.length (L.append (take s es) tl) == s + L.length tl)
  = take_len s es;
    L.append_length (take s es) tl

let ev_pre (es: list event) (s: nat) (tl: list event) (i: nat)
  : Lemma (requires s <= L.length es /\ i < s)
          (ensures i < L.length (L.append (take s es) tl) /\ ev (L.append (take s es) tl) i == ev es i)
  = take_len s es;
    index_app_lt (take s es) tl i;
    index_take i s es

let ev_tail (es: list event) (s: nat) (tl: list event) (k: nat)
  : Lemma (requires s <= L.length es /\ k < L.length tl)
          (ensures s + k < L.length (L.append (take s es) tl) /\ ev (L.append (take s es) tl) (s + k) == L.index tl k)
  = take_len s es;
    index_app_ge (take s es) tl k

/// ---------------------------------------------------------------------------
/// A tail that is a run
/// ---------------------------------------------------------------------------

/// What `run_ok` and `run_hyps` ask of one step.
let conds (c: comps) (sty: style) (x: config c) (e: event) : prop =
  enabled c x e /\ style_ok sty x e /\ mutator_ok x e /\ hyps_at c x e

let rec tail_ok (c: comps) (sty: style) (x: config c) (tl: list event) : Tot prop (decreases tl) =
  match tl with
  | [] -> True
  | e :: r -> conds c sty x e /\ tail_ok c sty (step c x e) r

let rec tail_idx (c: comps) (sty: style) (x: config c) (tl: list event) (k: nat)
  : Lemma (requires tail_ok c sty x tl /\ k < L.length tl)
          (ensures conds c sty (exec c x (take k tl)) (L.index tl k)) (decreases tl)
  = match tl with
    | e :: r -> if k = 0 then () else tail_idx c sty (step c x e) r (k - 1)

let run_pt (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (tl: list event) (i: nat)
  : Lemma (requires run_ok c sty n ny es /\ run_hyps c n ny es /\ s <= L.length es /\
                    tail_ok c sty (at c n ny es s) tl /\ i < L.length (L.append (take s es) tl))
          (ensures conds c sty (at c n ny (L.append (take s es) tl) i) (ev (L.append (take s es) tl) i))
  = len_app es s tl;
    if i < s then begin
      at_pre c n ny es s tl i;
      ev_pre es s tl i
    end else begin
      let k = i - s in
      at_tail c n ny es s tl k;
      ev_tail es s tl k;
      tail_idx c sty (at c n ny es s) tl k
    end

/// **`es` up to `s`, then a good tail, is a run.**
let run_of_tail (c: comps) (sty: style) (n ny: nat) (es: list event) (s: nat) (tl: list event)
  : Lemma (requires run_ok c sty n ny es /\ run_hyps c n ny es /\ s <= L.length es /\
                    tail_ok c sty (at c n ny es s) tl)
          (ensures run_ok c sty n ny (L.append (take s es) tl) /\ run_hyps c n ny (L.append (take s es) tl))
  = let es' = L.append (take s es) tl in
    let f (i: nat) : Lemma (i < L.length es' ==> conds c sty (at c n ny es' i) (ev es' i))
      = if i < L.length es' then run_pt c sty n ny es s tl i in
    C.forall_intro f
