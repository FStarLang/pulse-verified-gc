/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Complete - when the count is 0, the mark is complete
/// ---------------------------------------------------------------------------
///
/// `cnt_zero_complete`: in any state of the invariant where the work count is
/// 0, nothing is pending anywhere (I3), so the marks are closed under edges
/// (I2), and every reachable object is marked.  With I1, the bits are then
/// exactly the headers of the reachable objects (`cnt_zero_marks`).  A
/// worker finishes only after reading 0, and 0 is final (`done_ok`), so when
/// every worker has finished the bitmap is the mark's result
/// (`all_done_marks`).

module GC.Spec.Pages.ParMark.Complete

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

#push-options "--fuel 1"
let rec sum_zero (f: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws}) (w: nat)
  : Lemma (requires sumw f ws n == 0 /\ w < n) (ensures f (Seq.index ws w) == 0) (decreases n)
  = if w = n - 1 then () else sum_zero f ws (n - 1) w

let cl_empty (a: nat) : Lemma (cl [] a == false) = ()
let len0_ (#a: Type) (l: list a) : Lemma (requires L.length l == 0) (ensures l == []) = ()
#pop-options

/// A worker holding no unit holds nothing.
let no_units_nothing (p: params) (v: view) (rts: list nat) (bs: Seq.seq U32.t) (x: wst) (a y: nat)
  : Lemma (requires winv p v rts bs x /\ units x == 0) (ensures not (obl x a y))
  = cl_empty a

let len0 (#a: Type) (l: list a) : Lemma (requires L.length l == 0) (ensures l == []) = len0_ l

let count_facts (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires inv p v rts s)
          (ensures s.cnt == sumw units s.ws (Seq.length s.ws) + L.length s.pool /\
                   (forall (w: nat). w < Seq.length s.ws ==> winv p v rts s.bs (Seq.index s.ws w)))
  = inv_reveal p v rts s

/// **Count 0: nothing is pending.**
let cnt_zero_nothing (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires inv p v rts s /\ s.cnt == 0)
          (ensures s.pool == [] /\
                   (forall (w: nat) (a y: nat). w < Seq.length s.ws ==> not (obl (Seq.index s.ws w) a y)))
  = count_facts p v rts s;
    len0 s.pool;
    let aux (w: nat) (a y: nat) : Lemma (w < Seq.length s.ws ==> not (obl (Seq.index s.ws w) a y))
      = if w < Seq.length s.ws then begin
          sum_zero units s.ws (Seq.length s.ws) w;
          no_units_nothing p v rts s.bs (Seq.index s.ws w) a y
        end
    in
    FStar.Classical.forall_intro_3 aux

#push-options "--fuel 1"
let cp_empty (a: nat) : Lemma (cp [] a == false) = ()
#pop-options

/// **Count 0: the marks are closed under edges.**
let cnt_zero_closed (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires inv p v rts s /\ s.cnt == 0)
          (ensures forall (x a y: nat). v.ok x /\ marked s.bs (ybit x) /\ field_of p x a /\ p.tgt a == Some y ==>
                     marked s.bs (ybit y))
  = cnt_zero_nothing p v rts s;
    inv_reveal p v rts s;
    FStar.Classical.forall_intro cp_empty

/// **Count 0: every reachable object is marked.**
let cnt_zero_complete (p: params) (v: view) (rts: list nat) (s: mstate) (y: nat)
  : Lemma (requires view_ok p v rts /\ inv p v rts s /\ s.cnt == 0 /\ reach p rts y)
          (ensures marked s.bs (ybit y))
  = cnt_zero_closed p v rts s;
    inv_reveal p v rts s;
    closed_reach p rts (fun z -> v.ok z /\ marked s.bs (ybit z)) y

/// **Count 0: the bits are exactly the headers of the reachable objects.**
let cnt_zero_marks (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires view_ok p v rts /\ inv p v rts s /\ s.cnt == 0)
          (ensures marks_reach p rts s.bs /\ Seq.length s.bs == bm_len)
  = inv_reveal p v rts s;
    let aux (a: nat) : Lemma (marked s.bs a <==> (exists (y: nat). reach p rts y /\ a == y - 8))
      = if marked s.bs a then assert (reach p rts (a + 8) /\ a == (a + 8) - 8)
        else begin
          let no (y: nat) : Lemma (~(reach p rts y /\ a == y - 8))
            = if FStar.IndefiniteDescription.strong_excluded_middle (reach p rts y) && a = y - 8 then begin
                reach_ok p v rts y;
                cnt_zero_complete p v rts s y
              end
          in
          FStar.Classical.forall_intro no
        end
    in
    FStar.Classical.forall_intro aux

/// **When every worker has finished, the bitmap is the mark's result.**
let all_done_marks (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires view_ok p v rts /\ inv p v rts s /\ all_done s)
          (ensures marks_reach p rts s.bs /\ Seq.length s.bs == bm_len)
  = inv_reveal p v rts s;
    assert ((Seq.index s.ws 0).pc == Done);
    cnt_zero_marks p v rts s
