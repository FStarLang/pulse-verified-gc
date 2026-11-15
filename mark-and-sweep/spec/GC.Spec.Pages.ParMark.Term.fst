/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Term - the parallel mark terminates under a fair schedule
/// ---------------------------------------------------------------------------
///
/// A schedule is an infinite sequence of worker numbers; `runf` runs it.  A
/// worker may spin for ever while another holds the lock or still has work,
/// so termination needs fairness: every worker is scheduled infinitely often
/// (`fair`).  **`terminates`**: under a fair schedule, from the start, every
/// worker finishes.
///
/// The proof: `mu` never grows, and drops at every step that does not wait
/// (`Decrease.step_mu`).  A waiting step changes no shared state and no other
/// worker, so a worker's own steps go the same way whatever waiting steps the
/// others take between them (`agree`).  And in any state where some worker is
/// not finished, some worker reaches a step that does not wait within 3 of
/// its own steps (`progress`).  So if `mu` stopped dropping, that worker's
/// fourth turn would make it drop.

module GC.Spec.Pages.ParMark.Term

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Bits
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach
open GC.Spec.Pages.ParMark.Inv
open GC.Spec.Pages.ParMark.Measure
open GC.Spec.Pages.ParMark.Decrease

module U32 = FStar.UInt32
module Seq = FStar.Seq
module L = FStar.List.Tot
module Sf = GC.Spec.Pages.ParMark.Safety
module PI = GC.Spec.Pages.ParMark.Init

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Runs and fairness
/// ---------------------------------------------------------------------------

let step_any (p: params) (s: mstate) (w: nat) : mstate =
  if w < Seq.length s.ws then wstep p s w else s

let rec runf (p: params) (s: mstate) (sched: nat -> nat) (n: nat) : Tot mstate (decreases n) =
  if n = 0 then s else step_any p (runf p s sched (n - 1)) (sched (n - 1))

let fair (k: nat) (sched: nat -> nat) : prop =
  forall (w n: nat). w < k ==> (exists (m: nat). m >= n /\ sched m == w)

/// A worker's own steps.
let rec iter (p: params) (s: mstate) (w: nat) (j: nat) : Tot mstate (decreases j) =
  if j = 0 then s else step_any p (iter p s w (j - 1)) w

let wat (s: mstate) (w: nat) : bool = w < Seq.length s.ws && waiting s (Seq.index s.ws w)

#push-options "--fuel 1"
let runf_succ (p: params) (s: mstate) (sched: nat -> nat) (n: nat)
  : Lemma (runf p s sched (n + 1) == step_any p (runf p s sched n) (sched n)) = ()
let iter_succ (p: params) (s: mstate) (w j: nat)
  : Lemma (iter p s w (j + 1) == step_any p (iter p s w j) w) = ()
let iter_zero (p: params) (s: mstate) (w: nat) : Lemma (iter p s w 0 == s) = ()
let runf_zero (p: params) (s: mstate) (sched: nat -> nat) : Lemma (runf p s sched 0 == s) = ()
#pop-options

let step_any_inv (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat)
  : Lemma (requires view_ok p v rts /\ inv p v rts s) (ensures inv p v rts (step_any p s w))
  = if w < Seq.length s.ws then Sf.step_inv p v rts s w

let rec runf_inv (p: params) (v: view) (rts: list nat) (s: mstate) (sched: nat -> nat) (n: nat)
  : Lemma (requires view_ok p v rts /\ inv p v rts s) (ensures inv p v rts (runf p s sched n)) (decreases n)
  = if n = 0 then runf_zero p s sched
    else begin
      runf_inv p v rts s sched (n - 1);
      runf_succ p s sched (n - 1);
      step_any_inv p v rts (runf p s sched (n - 1)) (sched (n - 1))
    end

let rec iter_inv (p: params) (v: view) (rts: list nat) (s: mstate) (w j: nat)
  : Lemma (requires view_ok p v rts /\ inv p v rts s) (ensures inv p v rts (iter p s w j)) (decreases j)
  = if j = 0 then iter_zero p s w
    else begin
      iter_inv p v rts s w (j - 1);
      iter_succ p s w (j - 1);
      step_any_inv p v rts (iter p s w (j - 1)) w
    end

let len_inv (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires inv p v rts s) (ensures Seq.length s.ws == p.k)
  = inv_reveal p v rts s

/// One step, by any worker: `mu` drops unless the step waits.
let step_any_mu (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat)
  : Lemma (requires view_ok p v rts /\ inv p v rts s)
          (ensures (let s' = step_any p s w in
                    if w < Seq.length s.ws && waiting s (Seq.index s.ws w) || w >= Seq.length s.ws
                    then shared_eq s s' /\ mu p v s' == mu p v s
                    else mu p v s' < mu p v s))
  = if w < Seq.length s.ws then step_mu p v rts s w

/// ---------------------------------------------------------------------------
/// A worker's steps depend only on the shared state and its own state
/// ---------------------------------------------------------------------------

let agree (s1 s2: mstate) (w: nat) : prop =
  shared_eq s1 s2 /\ Seq.length s1.ws == Seq.length s2.ws /\ w < Seq.length s1.ws /\
  Seq.index s1.ws w == Seq.index s2.ws w

let lres (s1 s2: mstate) (w: nat) (t1 t2: mstate) : prop =
  shared_eq t1 t2 /\ Seq.length s1.ws == Seq.length s2.ws /\
  Seq.length t1.ws == Seq.length s1.ws /\ Seq.length t2.ws == Seq.length s2.ws /\
  w < Seq.length t1.ws /\ Seq.index t1.ws w == Seq.index t2.ws w

let run_local (p: params) (s1 s2: mstate) (w: nat)
  : Lemma (requires agree s1 s2 w /\ (Seq.index s1.ws w).pc == Run)
          (ensures lres s1 s2 w (wstep p s1 w) (wstep p s2 w))
  = let x = Seq.index s1.ws w in
    match x.vis with
    | CLoad _ -> ()
    | CCas _ -> ()
    | CNone ->
      if Cons? x.pend then ()
      else if x.scan.el > 0 then begin
        assert (wstep p s1 w == upd s1 w (Sf.visit_x p s1.bs x));
        assert (wstep p s2 w == upd s2 w (Sf.visit_x p s2.bs x))
      end
      else if x.chk then ()
      else if Nil? x.inp && Nil? x.out then ()
      else if Nil? x.inp then ()
      else ()

let sh3_local (p: params) (s1 s2: mstate) (w: nat)
  : Lemma (requires agree s1 s2 w /\ (Seq.index s1.ws w).pc == Sh3)
          (ensures lres s1 s2 w (wstep p s1 w) (wstep p s2 w))
  = let x = Seq.index s1.ws w in
    if s1.flag then begin
      if L.length (share_src x) / 2 = 0 then ()
      else begin
        Sf.share_x_eq x;
        assert (wstep p s1 w == upd ({ s1 with flag = false }) w (Sf.share_x x));
        assert (wstep p s2 w == upd ({ s2 with flag = false }) w (Sf.share_x x))
      end
    end

/// The step of `w` from two states that agree on its part.
let wstep_local (p: params) (s1 s2: mstate) (w: nat)
  : Lemma (requires agree s1 s2 w)
          (ensures waiting s1 (Seq.index s1.ws w) == waiting s2 (Seq.index s2.ws w) /\
                   lres s1 s2 w (wstep p s1 w) (wstep p s2 w))
  = match (Seq.index s1.ws w).pc with
    | Run -> run_local p s1 s2 w
    | Sh3 -> sh3_local p s1 s2 w
    | Tk1 -> (match s1.pool with [] -> () | _ :: _ -> ())
    | Tk2 -> (match (Seq.index s1.ws w).got with Some _ -> () | None -> ())
    | _ -> ()

let fres (s: mstate) (u w: nat) (t: mstate) : prop =
  Seq.length t.ws == Seq.length s.ws /\ w < Seq.length s.ws /\ Seq.index t.ws w == Seq.index s.ws w

let run_frame (p: params) (s: mstate) (u w: nat)
  : Lemma (requires u < Seq.length s.ws /\ w < Seq.length s.ws /\ u <> w /\ (Seq.index s.ws u).pc == Run)
          (ensures fres s u w (wstep p s u))
  = let x = Seq.index s.ws u in
    match x.vis with
    | CLoad _ -> ()
    | CCas _ -> ()
    | CNone ->
      if Cons? x.pend then ()
      else if x.scan.el > 0 then assert (wstep p s u == upd s u (Sf.visit_x p s.bs x))
      else ()

/// Another worker's step leaves `w`'s part alone.
let wstep_frame (p: params) (s: mstate) (u w: nat)
  : Lemma (requires u < Seq.length s.ws /\ w < Seq.length s.ws /\ u <> w)
          (ensures fres s u w (wstep p s u))
  = let x = Seq.index s.ws u in
    match x.pc with
    | Run -> run_frame p s u w
    | Sh3 ->
      if s.flag && L.length (share_src x) / 2 <> 0 then begin
        Sf.share_x_eq x;
        assert (wstep p s u == upd ({ s with flag = false }) u (Sf.share_x x))
      end
    | Tk1 -> (match s.pool with [] -> () | _ :: _ -> ())
    | Tk2 -> (match x.got with Some _ -> () | None -> ())
    | _ -> ()

let other_wait (p: params) (s: mstate) (u w: nat)
  : Lemma (requires u < Seq.length s.ws /\ w < Seq.length s.ws /\ u <> w /\
                    shared_eq s (wstep p s u))
          (ensures agree (wstep p s u) s w)
  = wstep_frame p s u w

/// ---------------------------------------------------------------------------
/// Progress
/// ---------------------------------------------------------------------------

/// Worker `w`'s first `j` own steps wait, and its next one does not.
let ready (p: params) (s: mstate) (w: nat) (j: nat) : prop =
  w < Seq.length s.ws /\
  (forall (i: nat). i < j ==> wat (iter p s w i) w) /\ ~(wat (iter p s w j) w)

/// The idle loop's next phase, when nothing is found.
let next_idle (s: mstate) (c: pc) : pc =
  match c with
  | Id1 -> if s.nfull > 0 then Id2 else Id3
  | Id3 -> if s.flag then Id5 else Id4
  | Id4 -> Id5
  | Id5 -> Id1
  | c -> c

let idle_step (p: params) (s: mstate) (w: nat)
  : Lemma (requires w < Seq.length s.ws /\
                    (let c = (Seq.index s.ws w).pc in c == Id1 \/ c == Id3 \/ (c == Id4 /\ s.flag) \/ (c == Id5 /\ s.cnt <> 0)))
          (ensures (let x = Seq.index s.ws w in
                    let t = iter p s w 1 in
                    shared_eq s t /\ Seq.length t.ws == Seq.length s.ws /\
                    Seq.index t.ws w == { x with pc = next_idle s x.pc } /\
                    iter p t w 0 == t))
  = iter_succ p s w 0; iter_zero p s w;
    let t = iter p s w 1 in
    iter_zero p t w

/// Two more steps of `w` are one step from the state after the first.
#push-options "--fuel 1"
let rec iter_shift (p: params) (s: mstate) (w: nat) (j: nat)
  : Lemma (ensures iter p s w (j + 1) == iter p (iter p s w 1) w j) (decreases j)
  = if j = 0 then () else iter_shift p s w (j - 1)
#pop-options

let ready_shift (p: params) (s: mstate) (w: nat) (j: nat)
  : Lemma (requires w < Seq.length s.ws /\ wat s w /\ ready p (iter p s w 1) w j)
          (ensures ready p s w (j + 1))
  = iter_zero p s w;
    let aux (i: nat) : Lemma (requires i < j + 1) (ensures wat (iter p s w i) w)
      = if i = 0 then () else iter_shift p s w (i - 1)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    iter_shift p s w j

let ready_now (p: params) (s: mstate) (w: nat)
  : Lemma (requires w < Seq.length s.ws /\ ~(wat s w)) (ensures ready p s w 0)
  = iter_zero p s w

/// How many own steps an idle worker waits, with the lock free and the
/// count equal to the pool's size.
let bnd (s: mstate) (c: pc) : nat =
  let b5 = if s.cnt = 0 then 0 else 2 in
  match c with
  | Id1 -> if s.nfull > 0 then 1 else 2
  | Id2 -> 0
  | Id3 -> if s.flag then 1 + b5 else 1
  | Id4 -> if s.flag then 1 + b5 else 0
  | Id5 -> b5
  | _ -> 0

let pcrank (c: pc) : nat =
  match c with
  | Id2 -> 0 | Id1 -> 1 | Id5 -> 2 | Id4 -> 3 | Id3 -> 4 | _ -> 0

let idle_hyp (s: mstate) (w: nat) : prop =
  w < Seq.length s.ws /\ not s.lk /\ s.nfull == L.length s.pool /\ s.cnt == L.length s.pool /\
  (let c = (Seq.index s.ws w).pc in c == Id1 \/ c == Id2 \/ c == Id3 \/ c == Id4 \/ c == Id5)

let idle_hyp_step (p: params) (s: mstate) (w: nat)
  : Lemma (requires idle_hyp s w /\ wat s w)
          (ensures (let t = iter p s w 1 in
                    shared_eq s t /\ Seq.length t.ws == Seq.length s.ws /\
                    (Seq.index t.ws w).pc == next_idle s (Seq.index s.ws w).pc /\
                    (next_idle s (Seq.index s.ws w).pc <> Id3 ==> idle_hyp t w)))
  = idle_step p s w

/// An idle worker reaches a step that does not wait.
let rec idle_ready (p: params) (s: mstate) (w: nat)
  : Lemma (requires idle_hyp s w)
          (ensures exists (j: nat). j <= bnd s (Seq.index s.ws w).pc /\ ready p s w j)
          (decreases (if w < Seq.length s.ws then pcrank (Seq.index s.ws w).pc else 0))
  = let x = Seq.index s.ws w in
    if not (wat s w) then ready_now p s w
    else begin
      idle_hyp_step p s w;
      let t = iter p s w 1 in
      Sf.len_pos s.pool;
      match x.pc with
      | Id1 ->
        if s.nfull > 0 then begin
          assert (~(wat t w));
          ready_now p t w;
          ready_shift p s w 0
        end else begin
          idle_step p t w;
          let t2 = iter p t w 1 in
          assert (~(wat t2 w));
          ready_now p t2 w;
          ready_shift p t w 0;
          ready_shift p s w 1
        end
      | Id3 | Id4 | Id5 ->
        idle_ready p t w;
        eliminate exists (j: nat). j <= bnd t (Seq.index t.ws w).pc /\ ready p t w j
        with ready_shift p s w j
    end

let bnd_le (s: mstate) (c: pc) : Lemma (bnd s c <= 3) = ()

#push-options "--fuel 1"
let rec sum_all_zero (f: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws})
  : Lemma (requires forall (w: nat). w < n ==> f (Seq.index ws w) == 0) (ensures sumw f ws n == 0) (decreases n)
  = if n = 0 then () else sum_all_zero f ws (n - 1)
#pop-options

/// When every worker waits: nobody holds the lock or any work, and the
/// count is the pool's size.
let all_wait_facts (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires inv p v rts s /\ (forall (w: nat). w < Seq.length s.ws ==> wat s w))
          (ensures not s.lk /\ s.nfull == L.length s.pool /\ s.cnt == L.length s.pool /\
                   (forall (w: nat). w < Seq.length s.ws ==>
                      (let c = (Seq.index s.ws w).pc in c == Id1 \/ c == Id3 \/ c == Id4 \/ c == Id5 \/ c == Done)))
  = inv_reveal p v rts s;
    let unit0 (w: nat) : Lemma (w < Seq.length s.ws ==> units (Seq.index s.ws w) == 0)
      = if w < Seq.length s.ws then assert (wat s w)
    in
    FStar.Classical.forall_intro unit0;
    sum_all_zero units s.ws (Seq.length s.ws)

/// **Progress**: in a state where some worker has not finished, some worker
/// reaches a step that does not wait within 3 of its own steps.
let progress (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires view_ok p v rts /\ inv p v rts s /\ ~(all_done s))
          (ensures exists (w j: nat). j <= 3 /\ ready p s w j)
  = if FStar.IndefiniteDescription.strong_excluded_middle
         (exists (w: nat). w < Seq.length s.ws /\ ~(wat s w)) then
      eliminate exists (w: nat). w < Seq.length s.ws /\ ~(wat s w)
      with ready_now p s w
    else begin
      all_wait_facts p v rts s;
      eliminate exists (w: nat). w < Seq.length s.ws /\ ~((Seq.index s.ws w).pc == Done)
      with begin
        idle_ready p s w;
        bnd_le s (Seq.index s.ws w).pc
      end
    end

/// ---------------------------------------------------------------------------
/// Fair runs
/// ---------------------------------------------------------------------------

/// The step at time `u` waits (a step of a worker number out of range does
/// nothing).
let waits_at (p: params) (s0: mstate) (sched: nat -> nat) (u: nat) : prop =
  let s = runf p s0 sched u in
  sched u >= Seq.length s.ws \/ wat s (sched u)

[@@"opaque_to_smt"]
let waits_from (p: params) (s0: mstate) (sched: nat -> nat) (n: nat) : prop =
  forall (u: nat). u >= n ==> waits_at p s0 sched u

let waits_from_elim (p: params) (s0: mstate) (sched: nat -> nat) (n u: nat)
  : Lemma (requires waits_from p s0 sched n /\ u >= n) (ensures waits_at p s0 sched u)
  = reveal_opaque (`%waits_from) (waits_from p s0 sched n)

let waits_from_intro (p: params) (s0: mstate) (sched: nat -> nat) (n: nat)
  : Lemma (requires ~(exists (u: nat). u >= n /\ ~(waits_at p s0 sched u))) (ensures waits_from p s0 sched n)
  = reveal_opaque (`%waits_from) (waits_from p s0 sched n)

let mu_step (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (u: nat)
  : Lemma (requires view_ok p v rts /\ inv p v rts s0)
          (ensures (let s = runf p s0 sched u in let s' = runf p s0 sched (u + 1) in
                    (waits_at p s0 sched u ==> shared_eq s s' /\ mu p v s' == mu p v s) /\
                    (~(waits_at p s0 sched u) ==> mu p v s' < mu p v s)))
  = runf_inv p v rts s0 sched u;
    runf_succ p s0 sched u;
    step_any_mu p v rts (runf p s0 sched u) (sched u)

let rec mu_mono (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (n u: nat)
  : Lemma (requires view_ok p v rts /\ inv p v rts s0 /\ n <= u)
          (ensures mu p v (runf p s0 sched u) <= mu p v (runf p s0 sched n)) (decreases u)
  = if u = n then () else (mu_mono p v rts s0 sched n (u - 1); mu_step p v rts s0 sched (u - 1))

/// The turns of `w` in `[n, t)`.
let rec cw (sched: nat -> nat) (w n t: nat) : Tot nat (decreases t) =
  if t <= n then 0 else cw sched w n (t - 1) + (if sched (t - 1) = w then 1 else 0)

#push-options "--fuel 1"
let cw_succ (sched: nat -> nat) (w n t: nat)
  : Lemma (requires n <= t) (ensures cw sched w n (t + 1) == cw sched w n t + (if sched t = w then 1 else 0))
  = ()

let rec cw_mono (sched: nat -> nat) (w n t t': nat)
  : Lemma (requires t <= t') (ensures cw sched w n t <= cw sched w n t') (decreases t')
  = if t = t' then () else cw_mono sched w n t (t' - 1)

let cw_zero (sched: nat -> nat) (w n: nat) : Lemma (cw sched w n n == 0) = ()
#pop-options

[@@"opaque_to_smt"]
let turns (sched: nat -> nat) (w: nat) : prop = forall (n: nat). exists (m: nat). m >= n /\ sched m == w

[@@"opaque_to_smt"]
let fair_o (k: nat) (sched: nat -> nat) : prop = fair k sched

let fair_o_intro (k: nat) (sched: nat -> nat) : Lemma (requires fair k sched) (ensures fair_o k sched)
  = reveal_opaque (`%fair_o) (fair_o k sched)

let turns_of (k: nat) (sched: nat -> nat) (w: nat)
  : Lemma (requires fair_o k sched /\ w < k) (ensures turns sched w)
  = reveal_opaque (`%fair_o) (fair_o k sched);
    reveal_opaque (`%turns) (turns sched w)

let turns_elim (sched: nat -> nat) (w t: nat)
  : Lemma (requires turns sched w) (ensures exists (m: nat). m >= t /\ sched m == w)
  = reveal_opaque (`%turns) (turns sched w)

let cw_next (sched: nat -> nat) (w n t: nat) (b: nat)
  : Lemma (requires turns sched w /\ t >= n /\ cw sched w n t >= b)
          (ensures exists (t': nat). t' >= n /\ cw sched w n t' >= b + 1)
  = turns_elim sched w t;
    eliminate exists (m: nat). m >= t /\ sched m == w
    with begin
      cw_mono sched w n t m;
      cw_succ sched w n m
    end

/// Under a fair schedule, `w` has as many turns as wanted.
let rec cw_unbounded (sched: nat -> nat) (w n b: nat)
  : Lemma (requires turns sched w)
          (ensures exists (t: nat). t >= n /\ cw sched w n t >= b) (decreases b)
  = if b = 0 then cw_zero sched w n
    else begin
      cw_unbounded sched w n (b - 1);
      eliminate exists (t: nat). t >= n /\ cw sched w n t >= b - 1
      with cw_next sched w n t (b - 1)
    end

let agree_trans (s1 s2 s3: mstate) (w: nat)
  : Lemma (requires agree s1 s2 w /\ agree s2 s3 w) (ensures agree s1 s3 w) = ()

let agree_refl (s: mstate) (w: nat) : Lemma (requires w < Seq.length s.ws) (ensures agree s s w) = ()

/// The same facts, under the opaque form of `view_ok` (keeps contexts small).
let runf_inv' (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (n: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0) (ensures inv p v rts (runf p s0 sched n))
  = Sf.vok_reveal p v rts; runf_inv p v rts s0 sched n

let iter_inv' (p: params) (v: view) (rts: list nat) (s: mstate) (w j: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s) (ensures inv p v rts (iter p s w j))
  = Sf.vok_reveal p v rts; iter_inv p v rts s w j

let mu_step' (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (u: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0)
          (ensures (let s = runf p s0 sched u in let s' = runf p s0 sched (u + 1) in
                    (waits_at p s0 sched u ==> shared_eq s s' /\ mu p v s' == mu p v s) /\
                    (~(waits_at p s0 sched u) ==> mu p v s' < mu p v s)))
  = Sf.vok_reveal p v rts; mu_step p v rts s0 sched u

let mu_mono' (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (n u: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0 /\ n <= u)
          (ensures mu p v (runf p s0 sched u) <= mu p v (runf p s0 sched n))
  = Sf.vok_reveal p v rts; mu_mono p v rts s0 sched n u

let progress' (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s /\ ~(all_done s))
          (ensures exists (w j: nat). j <= 3 /\ ready p s w j)
  = Sf.vok_reveal p v rts; progress p v rts s

/// While every step waits, `w`'s part follows its own steps alone, and it
/// has had at most `j` turns.
let rec frozen (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (n w j t: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0 /\ n <= t /\
                    waits_from p s0 sched n /\
                    ready p (runf p s0 sched n) w j)
          (ensures cw sched w n t <= j /\
                   agree (runf p s0 sched t) (iter p (runf p s0 sched n) w (cw sched w n t)) w)
          (decreases t)
  = let sn = runf p s0 sched n in
    if t = n then (cw_zero sched w n; iter_zero p sn w; agree_refl sn w)
    else begin
      let u = t - 1 in
      frozen p v rts s0 sched n w j u;
      let su = runf p s0 sched u in
      let c = cw sched w n u in
      let it = iter p sn w c in
      cw_succ sched w n u;
      mu_step' p v rts s0 sched u;
      runf_succ p s0 sched u;
      runf_inv' p v rts s0 sched u;
      len_inv p v rts su;
      runf_inv' p v rts s0 sched n;
      iter_inv' p v rts (runf p s0 sched n) w c;
      len_inv p v rts it;
      waits_from_elim p s0 sched n u;
      if sched u = w then begin
        wstep_local p su it w;
        if c = j then assert False
        else begin
          assert (wat it w);
          iter_succ p sn w c;
          assert (agree (runf p s0 sched t) (iter p sn w (c + 1)) w)
        end
      end
      else if sched u < Seq.length su.ws then begin
        other_wait p su (sched u) w;
        agree_trans (runf p s0 sched t) su it w
      end
      else ()
    end

let frozen_contra (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (n w j t: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0 /\ n <= t /\ waits_from p s0 sched n /\
                    ready p (runf p s0 sched n) w j /\ cw sched w n t >= j + 1)
          (ensures False)
  = frozen p v rts s0 sched n w j t

let stuck_turns (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (n w j: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0 /\ turns sched w /\ waits_from p s0 sched n /\
                    ready p (runf p s0 sched n) w j)
          (ensures False)
  = cw_unbounded sched w n (j + 1);
    eliminate exists (t: nat). t >= n /\ cw sched w n t >= j + 1
    with frozen_contra p v rts s0 sched n w j t

/// If every step from `n` on waited, the run would be stuck; it is not.
let not_stuck (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (n: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0 /\ fair_o p.k sched /\
                    ~(all_done (runf p s0 sched n)) /\
                    waits_from p s0 sched n)
          (ensures False)
  = let sn = runf p s0 sched n in
    runf_inv' p v rts s0 sched n;
    len_inv p v rts sn;
    progress' p v rts sn;
    eliminate exists (w j: nat). j <= 3 /\ ready p sn w j
    with begin
      assert (w < p.k);
      turns_of p.k sched w;
      stuck_turns p v rts s0 sched n w j
    end

/// By induction on the measure.
let rec term_from (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (m n: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0 /\ fair_o p.k sched /\
                    mu p v (runf p s0 sched n) <= m)
          (ensures exists (t: nat). all_done (runf p s0 sched t)) (decreases m)
  = if FStar.IndefiniteDescription.strong_excluded_middle (all_done (runf p s0 sched n)) then ()
    else if FStar.IndefiniteDescription.strong_excluded_middle
              (exists (u: nat). u >= n /\ ~(waits_at p s0 sched u)) then
      eliminate exists (u: nat). u >= n /\ ~(waits_at p s0 sched u)
      with begin
        mu_mono' p v rts s0 sched n u;
        mu_step' p v rts s0 sched u;
        if m = 0 then () else term_from p v rts s0 sched (m - 1) (u + 1)
      end
    else (waits_from_intro p s0 sched n; not_stuck p v rts s0 sched n)

let done_marks (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat) (n: nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0 /\ all_done (runf p s0 sched n))
          (ensures marks_reach p rts (runf p s0 sched n).bs /\ Seq.length (runf p s0 sched n).bs == bm_len)
  = runf_inv' p v rts s0 sched n;
    Sf.vok_reveal p v rts;
    GC.Spec.Pages.ParMark.Complete.all_done_marks p v rts (runf p s0 sched n)

let terminates_core (p: params) (v: view) (rts: list nat) (s0: mstate) (sched: nat -> nat)
  : Lemma (requires Sf.vok p v rts /\ inv p v rts s0 /\ fair_o p.k sched)
          (ensures exists (n: nat). all_done (runf p s0 sched n) /\ marks_reach p rts (runf p s0 sched n).bs /\
                               Seq.length (runf p s0 sched n).bs == bm_len)
  = runf_zero p s0 sched;
    term_from p v rts s0 sched (mu p v s0) 0;
    eliminate exists (n: nat). all_done (runf p s0 sched n)
    with done_marks p v rts s0 sched n

/// **Termination**: under a fair schedule, from the start, every worker
/// finishes, and then the bits are exactly the headers of the reachable
/// objects.
let terminates (p: params) (v: view) (rts: list nat) (bs0: Seq.seq U32.t) (sched: nat -> nat)
  : Lemma (requires view_ok p v rts /\ PI.no_marks bs0 /\ fair p.k sched)
          (ensures exists (n: nat). all_done (runf p (init p bs0 rts) sched n) /\
                               marks_reach p rts (runf p (init p bs0 rts) sched n).bs /\
                               Seq.length (runf p (init p bs0 rts) sched n).bs == bm_len)
  = PI.init_inv p v rts bs0;
    Sf.vok_reveal p v rts;
    fair_o_intro p.k sched;
    terminates_core p v rts (init p bs0 rts) sched
