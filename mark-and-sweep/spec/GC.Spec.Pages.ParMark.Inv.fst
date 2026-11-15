/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Inv - the parallel mark's invariant
/// ---------------------------------------------------------------------------
///
/// docs/pages-parallel-gc-design.md §1.6.  Over the model's state:
///
///   - I1 (soundness): a set bit is the header of a claimable object
///     reachable from the roots; the roots' targets are marked.
///   - I0 (entries): every entry held anywhere lies in the fields of a
///     marked object, and a claim in progress is for a reachable object.
///   - I2 (closure obligation): for every field of a marked object, its
///     target is marked, or the field is pending (in an entry held by a
///     worker or the pool, or in the range a worker is scanning), or a worker
///     is claiming the target.
///   - I3 (accounting): the work count is the number of workers holding a
///     unit (busy, or between counting and pooling a packet, or holding a
///     taken packet) plus the packets in the pool; an idle or finished worker
///     holds nothing; `nfull` is the pool's length; the lock is held exactly
///     by the one worker in a critical section; a finished worker has seen 0,
///     and 0 is final.
///
/// `preserve` reduces a step to local facts about the stepping worker; the
/// steps are in `GC.Spec.Pages.ParMark.Safety`.

module GC.Spec.Pages.ParMark.Inv

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Bits
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach

module U32 = FStar.UInt32
module Seq = FStar.Seq
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Pending words
/// ---------------------------------------------------------------------------

let covers (e: entry) (a: nat) : bool =
  e.es <= a && a < e.es + 8 * e.el && (a - e.es) % 8 = 0

let rec cl (l: list entry) (a: nat) : bool =
  match l with
  | [] -> false
  | e :: r -> covers e a || cl r a

let rec cp (q: list (list entry)) (a: nat) : bool =
  match q with
  | [] -> false
  | l :: r -> cl l a || cp r a

let gl (g: option (list entry)) : list entry =
  match g with
  | Some l -> l
  | None -> []

let claims (x: wst) (y: nat) : bool =
  match x.vis with
  | CNone -> false
  | CLoad y' -> y' = y
  | CCas (y', _) -> y' = y

/// Worker `x` keeps the obligation of the field at `a`, whose target is `y`.
let obl (x: wst) (a y: nat) : bool =
  cl x.inp a || cl x.out a || cl x.pend a || cl x.pub a || cl (gl x.got) a ||
  covers x.scan a || claims x y

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// An entry lies in the fields of a marked claimable object.
let eok (p: params) (v: view) (bs: Seq.seq U32.t) (e: entry) : prop =
  e.el == 0 \/
  (exists (x: nat). v.ok x /\ marked bs (ybit x) /\ x <= e.es /\ e.es + 8 * e.el <= x + 8 * p.nf x /\
               (e.es - x) % 8 == 0)

let lok (p: params) (v: view) (bs: Seq.seq U32.t) (l: list entry) : prop =
  forall (e: entry). L.memP e l ==> eok p v bs e

let busy (c: pc) : bool =
  match c with
  | Run | Sh1 | Sh2 | Sh3 | Lk | Cs1 | Cs2 | Cs3 -> true
  | _ -> false

/// In a critical section: holds the pool lock.
let incs (c: pc) : bool =
  match c with
  | Cs1 | Cs2 | Cs3 | Tk1 | Tk2 -> true
  | _ -> false

let publishing (c: pc) : bool =
  match c with
  | Lk | Cs1 | Cs2 -> true
  | _ -> false

/// The units of the work count a worker holds.
let units (x: wst) : nat =
  (if x.active then 1 else 0) + (if x.pc = Cs2 then 1 else 0) + (if x.pc = Tk2 && Some? x.got then 1 else 0)

/// What a worker holds, and in which phase.
let wshape (x: wst) : prop =
  (busy x.pc ==>
     x.active /\ x.got == None /\ (x.pc <> Run ==> x.vis == CNone) /\
     (~(CNone? x.vis) ==> x.pend == []) /\
     (publishing x.pc <==> Cons? x.pub)) /\
  (~(busy x.pc) ==>
     ~x.active /\ x.inp == [] /\ x.out == [] /\ x.pend == [] /\ x.pub == [] /\ x.scan.el == 0 /\
     x.vis == CNone /\ (x.pc <> Tk2 ==> x.got == None) /\ (Some? x.got ==> Cons? (gl x.got)))

let vis_ok (p: params) (v: view) (rts: list nat) (x: wst) : prop =
  match x.vis with
  | CNone -> True
  | CLoad y -> v.ok y /\ reach p rts y
  | CCas (y, old) -> v.ok y /\ reach p rts y /\ ~(in_pages (ybit y) /\ bit_of old (widx (ybit y) % 32))

let winv (p: params) (v: view) (rts: list nat) (bs: Seq.seq U32.t) (x: wst) : prop =
  lok p v bs x.inp /\ lok p v bs x.out /\ lok p v bs x.pend /\ lok p v bs x.pub /\
  lok p v bs (gl x.got) /\ eok p v bs x.scan /\ vis_ok p v rts x /\ wshape x

let rec sumw (f: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws}) : Tot nat (decreases n) =
  if n = 0 then 0 else sumw f ws (n - 1) + f (Seq.index ws (n - 1))

let held_units (s: mstate) : nat = sumw units s.ws (Seq.length s.ws)

let i1 (p: params) (v: view) (rts: list nat) (bs: Seq.seq U32.t) : prop =
  Seq.length bs == bm_len /\
  (forall (a: nat). marked bs a ==> v.ok (a + 8) /\ reach p rts (a + 8)) /\
  (forall (y: nat). L.mem y rts ==> marked bs (ybit y))

let i2 (p: params) (v: view) (s: mstate) : prop =
  forall (x a y: nat). v.ok x /\ marked s.bs (ybit x) /\ field_of p x a /\ p.tgt a == Some y ==>
    marked s.bs (ybit y) \/ cp s.pool a \/
    (exists (w: nat). w < Seq.length s.ws /\ obl (Seq.index s.ws w) a y)

let pool_ok (p: params) (v: view) (bs: Seq.seq U32.t) (q: list (list entry)) : prop =
  forall (l: list entry). L.memP l q ==> Cons? l /\ lok p v bs l

let lock_ok (s: mstate) : prop =
  (s.lk <==> (exists (w: nat). w < Seq.length s.ws /\ incs (Seq.index s.ws w).pc)) /\
  (forall (w1 w2: nat). w1 < Seq.length s.ws /\ w2 < Seq.length s.ws /\
     incs (Seq.index s.ws w1).pc /\ incs (Seq.index s.ws w2).pc ==> w1 == w2)

let done_ok (s: mstate) : prop =
  (exists (w: nat). w < Seq.length s.ws /\ (Seq.index s.ws w).pc == Done) ==> s.cnt == 0

let inv_body (p: params) (v: view) (rts: list nat) (s: mstate) : prop =
  Seq.length s.ws == p.k /\
  i1 p v rts s.bs /\
  (forall (w: nat). w < Seq.length s.ws ==> winv p v rts s.bs (Seq.index s.ws w)) /\
  pool_ok p v s.bs s.pool /\ s.nfull == L.length s.pool /\
  lock_ok s /\
  s.cnt == held_units s + L.length s.pool /\
  done_ok s /\
  i2 p v s

[@@"opaque_to_smt"]
let inv (p: params) (v: view) (rts: list nat) (s: mstate) : prop = inv_body p v rts s

let inv_reveal (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (inv p v rts s <==> inv_body p v rts s)
  = reveal_opaque (`%inv) (inv p v rts s)

/// ---------------------------------------------------------------------------
/// Lemmas on lists and sums
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec cl_append (l1 l2: list entry) (a: nat)
  : Lemma (ensures cl (L.append l1 l2) a == (cl l1 a || cl l2 a)) (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: r -> cl_append r l2 a

let rec cl_mem (l: list entry) (a: nat)
  : Lemma (ensures cl l a <==> (exists (e: entry). L.memP e l /\ covers e a)) (decreases l)
  = match l with
    | [] -> ()
    | _ :: r -> cl_mem r a

let rec cp_mem (q: list (list entry)) (a: nat)
  : Lemma (ensures cp q a <==> (exists (l: list entry). L.memP l q /\ cl l a)) (decreases q)
  = match q with
    | [] -> ()
    | _ :: r -> cp_mem r a

let lok_cons (p: params) (v: view) (bs: Seq.seq U32.t) (e: entry) (l: list entry)
  : Lemma (lok p v bs (e :: l) <==> eok p v bs e /\ lok p v bs l)
  = ()

let lok_append (p: params) (v: view) (bs: Seq.seq U32.t) (l1 l2: list entry)
  : Lemma (lok p v bs (L.append l1 l2) <==> lok p v bs l1 /\ lok p v bs l2)
  = FStar.Classical.forall_intro (L.append_memP l1 l2)

let rec sum_upd (f: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws}) (w: nat{w < Seq.length ws}) (x: wst)
  : Lemma (ensures sumw f (Seq.upd ws w x) n + (if w < n then f (Seq.index ws w) else 0) ==
                   sumw f ws n + (if w < n then f x else 0))
          (decreases n)
  = if n = 0 then () else sum_upd f ws (n - 1) w x

let rec sum_ge (f: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws}) (w: nat)
  : Lemma (ensures w < n ==> sumw f ws n >= f (Seq.index ws w)) (decreases n)
  = if n = 0 then () else sum_ge f ws (n - 1) w

let rec sum_ext (f: wst -> nat) (ws1 ws2: Seq.seq wst) (n: nat{n <= Seq.length ws1 /\ n <= Seq.length ws2})
  : Lemma (requires forall (w: nat). w < n ==> Seq.index ws1 w == Seq.index ws2 w)
          (ensures sumw f ws1 n == sumw f ws2 n) (decreases n)
  = if n = 0 then () else sum_ext f ws1 ws2 (n - 1)

let rec sum_const (f: wst -> nat) (x: wst) (n: nat)
  : Lemma (ensures sumw f (Seq.create n x) n == n * f x) (decreases n)
  = if n = 0 then ()
    else begin
      sum_ext f (Seq.create n x) (Seq.create (n - 1) x) (n - 1);
      sum_const f x (n - 1)
    end
#pop-options

let lok_grows (p: params) (v: view) (bs bs': Seq.seq U32.t) (l: list entry)
  : Lemma (requires lok p v bs l /\ grows bs bs') (ensures lok p v bs' l)
  = ()

let winv_grows (p: params) (v: view) (rts: list nat) (bs bs': Seq.seq U32.t) (x: wst)
  : Lemma (requires winv p v rts bs x /\ grows bs bs') (ensures winv p v rts bs' x)
  = ()

/// A covered word of a sound entry is a field of a marked object.
let covers_field (p: params) (v: view) (bs: Seq.seq U32.t) (e: entry) (a: nat)
  : Lemma (requires eok p v bs e /\ covers e a)
          (ensures exists (x: nat). v.ok x /\ marked bs (ybit x) /\ field_of p x a)
  = ()

/// ---------------------------------------------------------------------------
/// The frame: a step of worker `w`
/// ---------------------------------------------------------------------------

/// What a step of worker `w`, from `x` to `x'`, must show about the
/// obligations: those it held (and the pool's) are still met, and the
/// fields of an object it marked are covered.
let xfer_at (p: params) (v: view) (s s': mstate) (x x': wst) (o a y: nat) : prop =
  v.ok o /\ marked s'.bs (ybit o) /\ field_of p o a /\ p.tgt a == Some y /\
  (marked s.bs (ybit o) ==> (marked s.bs (ybit y) \/ cp s.pool a \/ obl x a y)) ==>
  (marked s'.bs (ybit y) \/ cp s'.pool a \/ obl x' a y)

let xfer (p: params) (v: view) (s s': mstate) (x x': wst) : prop =
  forall (o a y: nat). xfer_at p v s s' x x' o a y

let step_facts (p: params) (v: view) (rts: list nat) (s s': mstate) (w: nat) : prop =
  w < Seq.length s.ws /\ Seq.length s'.ws == Seq.length s.ws /\
  s'.ws == Seq.upd s.ws w (Seq.index s'.ws w) /\
  grows s.bs s'.bs /\
  i1 p v rts s'.bs /\
  winv p v rts s'.bs (Seq.index s'.ws w) /\
  pool_ok p v s'.bs s'.pool /\ s'.nfull == L.length s'.pool /\
  (* the lock *)
  (s'.lk <==> (incs (Seq.index s'.ws w).pc \/
               (exists (w': nat). w' < Seq.length s.ws /\ w' <> w /\ incs (Seq.index s.ws w').pc))) /\
  (incs (Seq.index s'.ws w).pc ==>
     (forall (w': nat). w' < Seq.length s.ws /\ w' <> w ==> ~(incs (Seq.index s.ws w').pc))) /\
  (* the count *)
  s'.cnt + units (Seq.index s.ws w) + L.length s.pool ==
    s.cnt + units (Seq.index s'.ws w) + L.length s'.pool /\
  ((Seq.index s'.ws w).pc == Done ==> s'.cnt == 0) /\
  (s.cnt == 0 ==> s'.cnt == 0) /\
  xfer p v s s' (Seq.index s.ws w) (Seq.index s'.ws w)

let xfer_elim (p: params) (v: view) (s s': mstate) (x x': wst) (o a y: nat)
  : Lemma (requires xfer p v s s' x x' /\ v.ok o /\ marked s'.bs (ybit o) /\ field_of p o a /\
                    p.tgt a == Some y /\
                    (marked s.bs (ybit o) ==> (marked s.bs (ybit y) \/ cp s.pool a \/ obl x a y)))
          (ensures marked s'.bs (ybit y) \/ cp s'.pool a \/ obl x' a y)
  = assert (xfer_at p v s s' x x' o a y)

let i2_elim (p: params) (v: view) (s: mstate) (o a y: nat)
  : Lemma (requires i2 p v s /\ v.ok o /\ marked s.bs (ybit o) /\ field_of p o a /\ p.tgt a == Some y)
          (ensures marked s.bs (ybit y) \/ cp s.pool a \/
                   (exists (w: nat). w < Seq.length s.ws /\ obl (Seq.index s.ws w) a y))
  = ()

let preserve_i2 (p: params) (v: view) (s s': mstate) (w: nat)
  : Lemma (requires i2 p v s /\ w < Seq.length s.ws /\ Seq.length s'.ws == Seq.length s.ws /\
                    s'.ws == Seq.upd s.ws w (Seq.index s'.ws w) /\ grows s.bs s'.bs /\
                    xfer p v s s' (Seq.index s.ws w) (Seq.index s'.ws w))
          (ensures i2 p v s')
  = let x = Seq.index s.ws w in
    let x' = Seq.index s'.ws w in
    let aux (o a y: nat)
      : Lemma (requires v.ok o /\ marked s'.bs (ybit o) /\ field_of p o a /\ p.tgt a == Some y)
              (ensures marked s'.bs (ybit y) \/ cp s'.pool a \/
                       (exists (w': nat). w' < Seq.length s'.ws /\ obl (Seq.index s'.ws w') a y))
      = if marked s.bs (ybit o) then begin
          i2_elim p v s o a y;
          if marked s.bs (ybit y) then ()
          else if cp s.pool a || obl x a y then xfer_elim p v s s' x x' o a y
          else begin
            eliminate exists (w': nat). w' < Seq.length s.ws /\ obl (Seq.index s.ws w') a y
            with begin
              assert (w' <> w);
              assert (Seq.index s'.ws w' == Seq.index s.ws w')
            end
          end
        end
        else xfer_elim p v s s' x x' o a y
    in
    FStar.Classical.forall_intro_3 (fun o a y -> FStar.Classical.move_requires (aux o a) y)

let preserve_lock (s s': mstate) (w: nat)
  : Lemma (requires lock_ok s /\ w < Seq.length s.ws /\ Seq.length s'.ws == Seq.length s.ws /\
                    s'.ws == Seq.upd s.ws w (Seq.index s'.ws w) /\
                    (s'.lk <==> (incs (Seq.index s'.ws w).pc \/
                       (exists (w': nat). w' < Seq.length s.ws /\ w' <> w /\ incs (Seq.index s.ws w').pc))) /\
                    (incs (Seq.index s'.ws w).pc ==>
                       (forall (w': nat). w' < Seq.length s.ws /\ w' <> w ==> ~(incs (Seq.index s.ws w').pc))))
          (ensures lock_ok s')
  = ()

let preserve_count (s s': mstate) (w: nat)
  : Lemma (requires w < Seq.length s.ws /\ Seq.length s'.ws == Seq.length s.ws /\ s'.ws == Seq.upd s.ws w (Seq.index s'.ws w) /\
                    s.cnt == held_units s + L.length s.pool /\
                    s'.cnt + units (Seq.index s.ws w) + L.length s.pool ==
                      s.cnt + units (Seq.index s'.ws w) + L.length s'.pool)
          (ensures s'.cnt == held_units s' + L.length s'.pool)
  = sum_upd units s.ws (Seq.length s.ws) w (Seq.index s'.ws w)

let preserve_done (s s': mstate) (w: nat)
  : Lemma (requires done_ok s /\ w < Seq.length s.ws /\ Seq.length s'.ws == Seq.length s.ws /\ s'.ws == Seq.upd s.ws w (Seq.index s'.ws w) /\
                    ((Seq.index s'.ws w).pc == Done ==> s'.cnt == 0) /\ (s.cnt == 0 ==> s'.cnt == 0))
          (ensures done_ok s')
  = introduce (exists (w': nat). w' < Seq.length s'.ws /\ (Seq.index s'.ws w').pc == Done) ==> s'.cnt == 0
    with eliminate exists (w': nat). w' < Seq.length s'.ws /\ (Seq.index s'.ws w').pc == Done
            with (if w' = w then () else assert ((Seq.index s.ws w').pc == Done))

let preserve_winv (p: params) (v: view) (rts: list nat) (s s': mstate) (w: nat)
  : Lemma (requires w < Seq.length s.ws /\ Seq.length s'.ws == Seq.length s.ws /\
                    s'.ws == Seq.upd s.ws w (Seq.index s'.ws w) /\ grows s.bs s'.bs /\
                    winv p v rts s'.bs (Seq.index s'.ws w) /\
                    (forall (w': nat). w' < Seq.length s.ws ==> winv p v rts s.bs (Seq.index s.ws w')))
          (ensures forall (w': nat). w' < Seq.length s'.ws ==> winv p v rts s'.bs (Seq.index s'.ws w'))
  = let aux (w': nat{w' < Seq.length s'.ws}) : Lemma (winv p v rts s'.bs (Seq.index s'.ws w'))
      = if w' = w then () else winv_grows p v rts s.bs s'.bs (Seq.index s.ws w')
    in
    FStar.Classical.forall_intro aux

/// **The frame lemma.**
let preserve (p: params) (v: view) (rts: list nat) (s s': mstate) (w: nat)
  : Lemma (requires inv p v rts s /\ step_facts p v rts s s' w) (ensures inv p v rts s')
  = inv_reveal p v rts s;
    inv_reveal p v rts s';
    preserve_winv p v rts s s' w;
    preserve_lock s s' w;
    preserve_count s s' w;
    preserve_done s s' w;
    preserve_i2 p v s s' w

/// ---------------------------------------------------------------------------
/// Facts the invariant gives
/// ---------------------------------------------------------------------------

/// A worker's units are part of the count.
let units_le (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat)
  : Lemma (requires inv p v rts s /\ w < Seq.length s.ws) (ensures units (Seq.index s.ws w) <= s.cnt)
  = inv_reveal p v rts s;
    sum_ge units s.ws (Seq.length s.ws) w

/// A marked object, as I1 gives it.
let marked_obj (p: params) (v: view) (rts: list nat) (bs: Seq.seq U32.t) (x: nat)
  : Lemma (requires i1 p v rts bs /\ marked bs (ybit x) /\ x >= 8)
          (ensures v.ok x /\ reach p rts x)
  = assert (ybit x + 8 == x)
