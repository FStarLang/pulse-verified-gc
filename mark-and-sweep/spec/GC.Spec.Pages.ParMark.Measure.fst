/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Measure - the termination measure
/// ---------------------------------------------------------------------------
///
/// `mu p v s`: a natural number that every step of the model decreases,
/// except the steps of a worker that waits (`waiting`): one that spins for
/// the pool lock, or goes round the idle loop without finding work, or has
/// finished.  A waiting step changes no shared state and keeps `mu`.
///
/// `mu` weighs, from heaviest to lightest: the claimable objects not yet
/// marked (`W_U` each); the entries and fields still to visit, by where they
/// are (pending push > output packet > input packet, the pool, a packet being
/// published or taken; a field in the range being scanned weighs least); the
/// phase of each worker, so that each multi-step operation (share check,
/// publish, take) runs down; the share flag clear and the lock free (one
/// unit each, paid by whoever sets or takes them); and a bounded term `psi`
/// for what another worker's step can undo (a CAS that makes a worker's
/// read stale; a take that empties the pool under an idle worker).  The
/// constants grow with `k` only to pay for that bounded term.

module GC.Spec.Pages.ParMark.Measure

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Bits
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach
open GC.Spec.Pages.ParMark.Inv

module U32 = FStar.UInt32
module Seq = FStar.Seq
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Weights
/// ---------------------------------------------------------------------------

let kk (p: params) : nat = 3 * p.k

let w_lock : nat = 2
let w_act : nat = 2
let ph_cs3 : nat = 3
let p_pool (p: params) : nat = 4 + kk p
let ph_cs2 (p: params) : nat = 8 + kk p
let ph_cs1 (p: params) : nat = 9 + kk p
let ph_lk (p: params) : nat = 8 + kk p
let ph_sh3 (p: params) : nat = 10 + kk p
let ph_sh2 (p: params) : nat = 11 + kk p
let ph_sh1 (p: params) : nat = 12 + kk p
let c_chk (p: params) : nat = 13 + kk p
let e_in (p: params) : nat = 14 + kk p
let e_out (p: params) : nat = 23 + 2 * kk p
let e_p (p: params) : nat = 24 + 2 * kk p
let c_s : nat = 4
let ce (p: params) : nat = 28 + 2 * kk p
let w_u (p: params) (v: view) : nat = (e_p p + ce p) * v.maxnf + kk p + 3

/// ---------------------------------------------------------------------------
/// The parts
/// ---------------------------------------------------------------------------

let entw (wt c: nat) (e: entry) : nat = wt + c * e.el

let rec lsum (wt c: nat) (l: list entry) : nat =
  match l with
  | [] -> 0
  | e :: r -> entw wt c e + lsum wt c r

let rec psum (p: params) (q: list (list entry)) : nat =
  match q with
  | [] -> 0
  | l :: r -> p_pool p + lsum (e_in p) (ce p) l + psum p r

let ph (p: params) (x: wst) : nat =
  match x.pc with
  | Run -> 0
  | Sh1 -> ph_sh1 p
  | Sh2 -> ph_sh2 p
  | Sh3 -> ph_sh3 p
  | Lk -> ph_lk p
  | Cs1 -> ph_cs1 p
  | Cs2 -> ph_cs2 p
  | Cs3 -> ph_cs3
  | Id1 | Id2 | Id3 | Id4 | Id5 -> 1
  | Tk1 -> 2
  | Tk2 -> if Some? x.got then 5 else 4
  | Done -> 0

let visw (x: wst) : nat =
  match x.vis with
  | CNone -> 0
  | CLoad _ -> 3
  | CCas _ -> 2

/// A worker's own weight.
let phi0 (p: params) (x: wst) : nat =
  lsum (e_in p) (ce p) x.inp + lsum (e_out p) (ce p) x.out + lsum (e_p p) (ce p) x.pend +
  lsum (e_in p) (ce p) x.pub + lsum (e_in p) (ce p) (gl x.got) + c_s * x.scan.el + visw x +
  (if x.active then w_act else 0) + (if x.chk then c_chk p else 0) + ph p x

/// The CAS of a claim will succeed.
let fresh (bs: Seq.seq U32.t) (y: nat) (old: U32.t) : bool =
  in_pages (ybit y) && Seq.length bs = bm_len && bword bs (ybit y) = old

/// What other workers' steps can add to a worker's weight (at most 3).
let psi (s: mstate) (x: wst) : nat =
  if x.pc = Id2 || x.pc = Tk1 then (if Nil? s.pool then 3 else 0)
  else (match x.vis with
        | CCas (y, old) -> if fresh s.bs y old then 0 else 2
        | _ -> 0)

let phi (p: params) (s: mstate) (x: wst) : nat = phi0 p x + psi s x

let rec unmarked (bs: Seq.seq U32.t) (u: list nat) : nat =
  match u with
  | [] -> 0
  | y :: r -> (if marked bs (ybit y) then 0 else 1) + unmarked bs r

let glob (p: params) (v: view) (s: mstate) : nat =
  w_u p v * unmarked s.bs v.univ + (if s.flag then 0 else 1) + (if s.lk then 0 else w_lock) + psum p s.pool

/// **The measure.**
let mu (p: params) (v: view) (s: mstate) : nat =
  glob p v s + sumw (phi p s) s.ws (Seq.length s.ws)

/// ---------------------------------------------------------------------------
/// Waiting
/// ---------------------------------------------------------------------------

/// The step of a worker in state `x` waits: it spins for the lock, goes
/// round the idle loop, or the worker has finished.
let waiting (s: mstate) (x: wst) : bool =
  match x.pc with
  | Lk -> s.lk
  | Id1 | Id3 -> true
  | Id2 -> s.lk && Cons? s.pool
  | Id4 -> s.flag
  | Id5 -> s.cnt <> 0
  | Done -> true
  | _ -> false

/// The shared state.
let shared_eq (s s': mstate) : prop =
  s'.bs == s.bs /\ s'.cnt == s.cnt /\ s'.flag == s.flag /\ s'.lk == s.lk /\ s'.pool == s.pool /\
  s'.nfull == s.nfull
