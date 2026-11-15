/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Safety - no step breaks the invariant
/// ---------------------------------------------------------------------------
///
/// `step_inv`: every step of every worker keeps `Inv.inv`, one lemma per
/// case of `Model.wstep`, each through `Inv.preserve`.  With `init_inv`
/// (`GC.Spec.Pages.ParMark.Init`), the invariant holds in every state of
/// every interleaving (`run_inv`).

module GC.Spec.Pages.ParMark.Safety

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
/// Entries
/// ---------------------------------------------------------------------------

let covers_advance (e: entry) (a: nat)
  : Lemma (requires e.el > 0 /\ covers e a /\ a <> e.es) (ensures covers (advance e) a)
  = ()

let covers_split (e: entry) (c: nat) (a: nat)
  : Lemma (requires c <= e.el /\ covers e a)
          (ensures covers ({ es = e.es; el = c }) a \/ covers (rest_of e c) a)
  = ()

let sub_arith (x es el es' el' n: nat)
  : Lemma (requires x <= es /\ es + 8 * el <= x + 8 * n /\ (es - x) % 8 == 0 /\
                    es <= es' /\ es' + 8 * el' <= es + 8 * el /\ (es' - es) % 8 == 0)
          (ensures x <= es' /\ es' + 8 * el' <= x + 8 * n /\ (es' - x) % 8 == 0)
  = FStar.Math.Lemmas.modulo_distributivity (es' - es) (es - x) 8

let eok_intro (p: params) (v: view) (bs: Seq.seq U32.t) (e: entry) (x: nat)
  : Lemma (requires v.ok x /\ marked bs (ybit x) /\ x <= e.es /\ e.es + 8 * e.el <= x + 8 * p.nf x /\
                    (e.es - x) % 8 == 0)
          (ensures eok p v bs e)
  = ()

/// A sub-range of a sound entry is sound.
let eok_sub (p: params) (v: view) (bs: Seq.seq U32.t) (e e': entry)
  : Lemma (requires eok p v bs e /\ e.es <= e'.es /\ e'.es + 8 * e'.el <= e.es + 8 * e.el /\
                    (e'.es - e.es) % 8 == 0 /\ (e'.el > 0 ==> e.el > 0))
          (ensures eok p v bs e')
  = if e'.el = 0 then ()
    else begin
      assert (e.el <> 0);
      assert (exists (x: nat). v.ok x /\ marked bs (ybit x) /\ x <= e.es /\
                          e.es + 8 * e.el <= x + 8 * p.nf x /\ (e.es - x) % 8 == 0);
      eliminate exists (x: nat). v.ok x /\ marked bs (ybit x) /\ x <= e.es /\
                            e.es + 8 * e.el <= x + 8 * p.nf x /\ (e.es - x) % 8 == 0
      with begin
        sub_arith x e.es e.el e'.es e'.el (p.nf x);
        eok_intro p v bs e' x
      end
    end

#push-options "--fuel 2"
/// The entries of an object lie in its fields ...
let rec push_obj_in (ml: pos) (a n: nat) (e: entry)
  : Lemma (requires L.memP e (push_obj ml a n))
          (ensures a <= e.es /\ e.es + 8 * e.el <= a + 8 * n /\ (e.es - a) % 8 == 0)
          (decreases n)
  = if n = 0 then ()
    else if n <= ml then ()
    else if e = { es = a; el = ml } then ()
    else begin
      push_obj_in ml (a + 8 * ml) (n - ml) e;
      FStar.Math.Lemmas.lemma_mod_plus (e.es - (a + 8 * ml)) ml 8
    end

/// ... and cover them.
let rec push_obj_covers (ml: pos) (a n: nat) (b: nat)
  : Lemma (requires a <= b /\ b < a + 8 * n /\ (b - a) % 8 == 0)
          (ensures cl (push_obj ml a n) b)
          (decreases n)
  = if n <= ml then ()
    else if b < a + 8 * ml then ()
    else begin
      FStar.Math.Lemmas.lemma_mod_plus (b - (a + 8 * ml)) ml 8;
      push_obj_covers ml (a + 8 * ml) (n - ml) b
    end
#pop-options

let obj_entries_ok (p: params) (v: view) (bs: Seq.seq U32.t) (y: nat)
  : Lemma (requires v.ok y /\ marked bs (ybit y)) (ensures lok p v bs (obj_entries p y))
  = let aux (e: entry) : Lemma (requires L.memP e (obj_entries p y)) (ensures eok p v bs e)
      = push_obj_in p.maxlen y (p.nf y) e
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let obj_entries_covers (p: params) (y a: nat)
  : Lemma (requires field_of p y a) (ensures cl (obj_entries p y) a)
  = push_obj_covers p.maxlen y (p.nf y) a

#push-options "--fuel 1"
let rec cl_split (n: nat) (l: list entry) (a: nat)
  : Lemma (ensures cl l a == (cl (fst (L.splitAt n l)) a || cl (snd (L.splitAt n l)) a) /\
                   L.length (fst (L.splitAt n l)) + L.length (snd (L.splitAt n l)) == L.length l /\
                   (forall (e: entry). L.memP e (fst (L.splitAt n l)) \/ L.memP e (snd (L.splitAt n l)) ==>
                                  L.memP e l) /\
                   (n <= L.length l ==> L.length (fst (L.splitAt n l)) == n))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: r -> if n = 0 then () else cl_split (n - 1) r a
#pop-options

/// ---------------------------------------------------------------------------
/// Facts the invariant gives about the stepping worker
/// ---------------------------------------------------------------------------

let get_w (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat)
  : Lemma (requires inv p v rts s /\ w < Seq.length s.ws)
          (ensures winv p v rts s.bs (Seq.index s.ws w) /\ units (Seq.index s.ws w) <= s.cnt)
  = inv_reveal p v rts s;
    units_le p v rts s w

/// The lock is free: nobody is in a critical section.
let lock_free (s: mstate) (w: nat)
  : Lemma (requires lock_ok s /\ not s.lk) (ensures forall (w': nat). w' < Seq.length s.ws ==> ~(incs (Seq.index s.ws w').pc))
  = ()

/// The worker in a critical section is the only one.
let lock_mine (s: mstate) (w: nat)
  : Lemma (requires lock_ok s /\ w < Seq.length s.ws /\ incs (Seq.index s.ws w).pc)
          (ensures s.lk /\ (forall (w': nat). w' < Seq.length s.ws /\ w' <> w ==> ~(incs (Seq.index s.ws w').pc)))
  = ()

/// ---------------------------------------------------------------------------
/// Steps that touch no shared state
/// ---------------------------------------------------------------------------

let xfer_mono (p: params) (v: view) (s s': mstate) (x x': wst)
  : Lemma (requires s'.bs == s.bs /\ s'.pool == s.pool /\ (forall (a y: nat). obl x a y ==> obl x' a y))
          (ensures xfer p v s s' x x')
  = ()

let same_shared (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws}) (x': wst)
  : Lemma (requires inv p v rts s /\ winv p v rts s.bs x' /\
                    incs (Seq.index s.ws w).pc == incs x'.pc /\ units x' == units (Seq.index s.ws w) /\
                    (x'.pc == Done ==> s.cnt == 0) /\
                    xfer p v s (upd s w x') (Seq.index s.ws w) x')
          (ensures inv p v rts (upd s w x'))
  = let s' = upd s w x' in
    inv_reveal p v rts s;
    assert (Seq.index s'.ws w == x');
    assert (s'.ws == Seq.upd s.ws w (Seq.index s'.ws w));
    grows_refl s.bs;
    preserve p v rts s s' w

/// A step that changes only the phase (and the share check).
let pc_step (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws}) (c: pc) (ck: bool)
  : Lemma (requires inv p v rts s /\
                    (let x = Seq.index s.ws w in
                     wshape ({ x with pc = c; chk = ck }) /\ incs x.pc == incs c /\
                     units ({ x with pc = c; chk = ck }) == units x /\ (c == Done ==> s.cnt == 0)))
          (ensures inv p v rts (upd s w ({ Seq.index s.ws w with pc = c; chk = ck })))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    let x' = { x with pc = c; chk = ck } in
    xfer_mono p v s (upd s w x') x x';
    same_shared p v rts s w x'

let step_done (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Done) (ensures inv p v rts (wstep p s w))
  = ()

let step_sh1 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Sh1) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    if s.nfull <> 0 then pc_step p v rts s w Run x.chk else pc_step p v rts s w Sh2 x.chk

let step_sh2 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Sh2) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    if not s.flag || L.length (share_src x) < p.smin then pc_step p v rts s w Run x.chk
    else pc_step p v rts s w Sh3 x.chk

let step_id1 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Id1) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    if s.nfull > 0 then pc_step p v rts s w Id2 x.chk else pc_step p v rts s w Id3 x.chk

let step_id3 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Id3) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    if s.flag then pc_step p v rts s w Id5 x.chk else pc_step p v rts s w Id4 x.chk

let step_id5 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Id5) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    if s.cnt = 0 then pc_step p v rts s w Done x.chk else pc_step p v rts s w Id1 x.chk

/// ---------------------------------------------------------------------------
/// Steps on the lock, the count, the pool and the share flag
/// ---------------------------------------------------------------------------

let get_shared (p: params) (v: view) (rts: list nat) (s: mstate)
  : Lemma (requires inv p v rts s)
          (ensures i1 p v rts s.bs /\ pool_ok p v s.bs s.pool /\ s.nfull == L.length s.pool /\
                   lock_ok s /\ Seq.length s.ws == p.k)
  = inv_reveal p v rts s

#push-options "--fuel 1"
let cl_cons (e: entry) (l: list entry) (a: nat) : Lemma (cl (e :: l) a == (covers e a || cl l a)) = ()
let cp_cons (l: list entry) (q: list (list entry)) (a: nat) : Lemma (cp (l :: q) a == (cl l a || cp q a)) = ()
let cl_nil (a: nat) : Lemma (cl [] a == false) = ()
let pool_ok_cons (p: params) (v: view) (bs: Seq.seq U32.t) (l: list entry) (q: list (list entry))
  : Lemma (pool_ok p v bs (l :: q) <==> (Cons? l /\ lok p v bs l /\ pool_ok p v bs q))
  = ()
let length_cons (#a: Type) (x: a) (l: list a) : Lemma (L.length (x :: l) == 1 + L.length l) = ()
let len_pos (#a: Type) (l: list a) : Lemma (L.length l > 0 <==> Cons? l) = ()
#pop-options

let step_lk (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Lk) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    if s.lk then ()
    else begin
      let x' = { x with pc = Cs1 } in
      let s' = upd ({ s with lk = true }) w x' in
      lock_free s w;
      xfer_mono p v s s' x x';
      preserve p v rts s s' w
    end

let step_cs1 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Cs1) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    let x' = { x with pc = Cs2 } in
    let s' = upd ({ s with cnt = s.cnt + 1 }) w x' in
    lock_mine s w;
    xfer_mono p v s s' x x';
    preserve p v rts s s' w

let xfer_to_pool (p: params) (v: view) (s s': mstate) (x x': wst) (l: list entry)
  : Lemma (requires s'.bs == s.bs /\ s'.pool == l :: s.pool /\
                    (forall (a y: nat). obl x a y ==> obl x' a y \/ cl l a))
          (ensures xfer p v s s' x x')
  = FStar.Classical.forall_intro (cp_cons l s.pool)

let step_cs2 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Cs2) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    let x' = { x with pub = []; pc = Cs3 } in
    let s' = upd ({ s with pool = x.pub :: s.pool; nfull = s.nfull + 1 }) w x' in
    lock_mine s w;
    pool_ok_cons p v s.bs x.pub s.pool;
    length_cons x.pub s.pool;
    FStar.Classical.forall_intro (cp_cons x.pub s.pool);
    FStar.Classical.forall_intro cl_nil;
    xfer_to_pool p v s s' x x' x.pub;
    assert (Seq.index s'.ws w == x');
    assert (winv p v rts s'.bs x');
    assert (pool_ok p v s'.bs s'.pool);
    assert (s'.cnt + units x + L.length s.pool == s.cnt + units x' + L.length s'.pool);
    preserve p v rts s s' w

let step_cs3 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Cs3) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    let x' = { x with pc = Run } in
    let s' = upd ({ s with lk = false }) w x' in
    lock_mine s w;
    xfer_mono p v s s' x x';
    preserve p v rts s s' w

let step_id2 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Id2) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    if s.lk then pc_step p v rts s w Id5 x.chk
    else begin
      let x' = { x with pc = Tk1 } in
      let s' = upd ({ s with lk = true }) w x' in
      lock_free s w;
      xfer_mono p v s s' x x';
      preserve p v rts s s' w
    end

let xfer_from_pool (p: params) (v: view) (s s': mstate) (x x': wst) (l: list entry)
  : Lemma (requires s'.bs == s.bs /\ s.pool == l :: s'.pool /\
                    (forall (a y: nat). obl x a y \/ cl l a ==> obl x' a y))
          (ensures xfer p v s s' x x')
  = FStar.Classical.forall_intro (cp_cons l s'.pool)

let step_tk1 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Tk1) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    lock_mine s w;
    match s.pool with
    | [] ->
      let x' = { x with got = None; pc = Tk2 } in
      let s' = upd s w x' in
      xfer_mono p v s s' x x';
      preserve p v rts s s' w
    | q :: rest ->
      let x' = { x with got = Some q; pc = Tk2 } in
      let s' = upd ({ s with pool = rest; nfull = (if s.nfull > 0 then s.nfull - 1 else 0) }) w x' in
      pool_ok_cons p v s.bs q rest;
      length_cons q rest;
      xfer_from_pool p v s s' x x' q;
      assert (Seq.index s'.ws w == x');
      assert (winv p v rts s'.bs x');
      assert (pool_ok p v s'.bs s'.pool /\ s'.nfull == L.length s'.pool);
      assert (not x.active);
      assert (units x == 0 /\ units x' == 1);
      assert (s'.cnt == s.cnt /\ L.length s.pool == 1 + L.length s'.pool);
      assert (Seq.length s'.ws == Seq.length s.ws);
      assert (s'.ws == Seq.upd s.ws w (Seq.index s'.ws w));
      assert (grows s.bs s'.bs);
      assert (i1 p v rts s'.bs);
      assert (s'.lk <==> (incs (Seq.index s'.ws w).pc \/
               (exists (w': nat). w' < Seq.length s.ws /\ w' <> w /\ incs (Seq.index s.ws w').pc)));
      assert (incs (Seq.index s'.ws w).pc ==>
               (forall (w': nat). w' < Seq.length s.ws /\ w' <> w ==> ~(incs (Seq.index s.ws w').pc)));
      assert ((Seq.index s'.ws w).pc == Done ==> s'.cnt == 0);
      assert (s.cnt == 0 ==> s'.cnt == 0);
      assert (xfer p v s s' (Seq.index s.ws w) (Seq.index s'.ws w));
      preserve p v rts s s' w

let step_tk2 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Tk2) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    lock_mine s w;
    FStar.Classical.forall_intro cl_nil;
    match x.got with
    | Some q ->
      let x' = { x with inp = q; got = None; active = true; chk = false; pc = Run } in
      let s' = upd ({ s with lk = false }) w x' in
      preserve p v rts s s' w
    | None ->
      let x' = { x with pc = Id5 } in
      let s' = upd ({ s with lk = false }) w x' in
      xfer_mono p v s s' x x';
      preserve p v rts s s' w

let step_id4 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Id4) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    let x' = { x with pc = Id5 } in
    let s' = upd ({ s with flag = true }) w x' in
    xfer_mono p v s s' x x';
    preserve p v rts s s' w

let share_x (x: wst) : wst =
  let src = share_src x in
  let h = L.length src / 2 in
  let r = L.splitAt (L.length src - h) src in
  let x1 = if share_src_inp x then { x with inp = fst r } else { x with out = fst r } in
  { x1 with pub = snd r; pc = Lk }

let share_x_eq (x: wst)
  : Lemma (share_x x == (let src = share_src x in
                         let h = L.length src / 2 in
                         let (keep, give) = L.splitAt (L.length src - h) src in
                         let x1 = if share_src_inp x then { x with inp = keep } else { x with out = keep } in
                         { x1 with pub = give; pc = Lk }))
  = ()

let share_facts (p: params) (v: view) (rts: list nat) (bs: Seq.seq U32.t) (x: wst)
  : Lemma (requires winv p v rts bs x /\ x.pc == Sh3 /\ L.length (share_src x) / 2 > 0)
          (ensures winv p v rts bs (share_x x) /\ units (share_x x) == units x /\
                   incs (share_x x).pc == false /\ (share_x x).pc <> Done /\
                   (forall (a y: nat). obl x a y ==> obl (share_x x) a y))
  = let src = share_src x in
    let h = L.length src / 2 in
    let n = L.length src - h in
    FStar.Classical.forall_intro (cl_split n src);
    let r = L.splitAt n src in
    assert (lok p v bs src);
    assert (lok p v bs (fst r) /\ lok p v bs (snd r));
    assert (L.length (snd r) == h);
    len_pos (snd r)

let half_pos (n: nat) : Lemma (requires n / 2 <> 0) (ensures n / 2 > 0) = ()

let step_sh3 (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Sh3) (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    if not s.flag then pc_step p v rts s w Run x.chk
    else begin
      let src = share_src x in
      let h = L.length src / 2 in
      if h = 0 then begin
        let x' = { x with pc = Run } in
        let s' = upd ({ s with flag = false }) w x' in
        xfer_mono p v s s' x x';
        preserve p v rts s s' w
      end else begin
        half_pos (L.length (share_src x));
        share_facts p v rts s.bs x;
        let x' = share_x x in
        let s' = upd ({ s with flag = false }) w x' in
        share_x_eq x;
        assert (s' == wstep p s w);
        xfer_mono p v s s' x x';
        preserve p v rts s s' w
      end
    end

/// ---------------------------------------------------------------------------
/// The busy worker's steps
/// ---------------------------------------------------------------------------

let xfer_or_marked (p: params) (v: view) (s s': mstate) (x x': wst)
  : Lemma (requires s'.bs == s.bs /\ s'.pool == s.pool /\
                    (forall (a y: nat). obl x a y ==> obl x' a y \/ marked s.bs (ybit y)))
          (ensures xfer p v s s' x x')
  = ()

/// A step of a busy worker that changes only its own state.
let run_local (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws}) (x': wst)
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Run /\ winv p v rts s.bs x' /\ busy x'.pc /\
                    ~(incs x'.pc) /\ x'.pc <> Cs2 /\
                    (forall (a y: nat). obl (Seq.index s.ws w) a y ==> obl x' a y \/ marked s.bs (ybit y)))
          (ensures inv p v rts (upd s w x'))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    xfer_or_marked p v s (upd s w x') x x';
    same_shared p v rts s w x'

let step_cload (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws}) (y: nat)
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CLoad y /\
                    Seq.length s.bs == bm_len)
          (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    if marked s.bs (ybit y) then run_local p v rts s w ({ x with vis = CNone })
    else begin
      if in_pages (ybit y) then marked_bword s.bs (ybit y);
      run_local p v rts s w ({ x with vis = CCas (y, bword s.bs (ybit y)) })
    end

[@@"opaque_to_smt"]
let vok (p: params) (v: view) (rts: list nat) : prop = view_ok p v rts

let vok_reveal (p: params) (v: view) (rts: list nat) : Lemma (vok p v rts <==> view_ok p v rts)
  = reveal_opaque (`%vok) (vok p v rts)

let ok_ge8 (p: params) (v: view) (rts: list nat) (y: nat)
  : Lemma (requires vok p v rts /\ v.ok y) (ensures y >= 8 /\ in_pages (y - 8))
  = vok_reveal p v rts

/// The claim succeeds: `y`'s bit is set and its fields are pending.
let claim_xfer_at (p: params) (v: view) (s s': mstate) (x x': wst) (y o a z: nat)
  : Lemma (requires v.ok y /\ y >= 8 /\ in_pages (ybit y) /\ (v.ok o ==> o >= 8) /\
                    s'.bs == set_bit s.bs (ybit y) /\ s'.pool == s.pool /\ Seq.length s.bs == bm_len /\
                    claims x y /\ x.pend == [] /\
                    x' == { x with vis = CNone; pend = obj_entries p y } /\
                    v.ok o /\ marked s'.bs (ybit o) /\ field_of p o a /\ p.tgt a == Some z /\
                    (marked s.bs (ybit o) ==> (marked s.bs (ybit z) \/ cp s.pool a \/ obl x a z)))
          (ensures marked s'.bs (ybit z) \/ cp s'.pool a \/ obl x' a z)
  = set_bit_marked s.bs (ybit y) (ybit o);
    set_bit_marked s.bs (ybit y) (ybit z);
    if marked s.bs (ybit o) then begin
      if marked s.bs (ybit z) || cp s.pool a then ()
      else if claims x z then assert (z == y)
      else begin
        cl_nil a;
        assert (cl x.inp a || cl x.out a || cl x.pub a || cl (gl x.got) a || covers x.scan a);
        assert (x'.inp == x.inp /\ x'.out == x.out /\ x'.pub == x.pub /\ x'.got == x.got /\ x'.scan == x.scan)
      end
    end else begin
      assert (ybit o == ybit y);
      assert (o == y);
      obj_entries_covers p y a;
      assert (cl x'.pend a)
    end

let claim_xfer (p: params) (v: view) (rts: list nat) (s s': mstate) (x x': wst) (y: nat)
  : Lemma (requires vok p v rts /\ v.ok y /\
                    s'.bs == set_bit s.bs (ybit y) /\ s'.pool == s.pool /\ Seq.length s.bs == bm_len /\
                    claims x y /\ x.pend == [] /\
                    x' == { x with vis = CNone; pend = obj_entries p y })
          (ensures xfer p v s s' x x')
  = vok_reveal p v rts;
    let aux (o a z: nat) : Lemma (xfer_at p v s s' x x' o a z)
      = FStar.Classical.move_requires (claim_xfer_at p v s s' x x' y o a) z
    in
    FStar.Classical.forall_intro_3 aux

let claim_winv (p: params) (v: view) (rts: list nat) (bs bs': Seq.seq U32.t) (x: wst) (y: nat)
  : Lemma (requires winv p v rts bs x /\ grows bs bs' /\ lok p v bs' (obj_entries p y) /\
                    x.pc == Run /\ x.pend == [])
          (ensures winv p v rts bs' ({ x with vis = CNone; pend = obj_entries p y }))
  = winv_grows p v rts bs bs' x

let step_ccas (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws}) (y: nat) (old: U32.t)
  : Lemma (requires vok p v rts /\ inv p v rts s /\ (Seq.index s.ws w).pc == Run /\
                    (Seq.index s.ws w).vis == CCas (y, old))
          (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    if in_pages (ybit y) && Seq.length s.bs = bm_len && bword s.bs (ybit y) = old then begin
      let bs' = set_bit s.bs (ybit y) in
      let x' = { x with vis = CNone; pend = obj_entries p y } in
      let s' = upd ({ s with bs = bs' }) w x' in
      assert (v.ok y /\ reach p rts y);
      ok_ge8 p v rts y;
      grows_set s.bs (ybit y);
      FStar.Classical.forall_intro (set_bit_marked s.bs (ybit y));
      assert (marked bs' (ybit y));
      assert (i1 p v rts bs');
      obj_entries_ok p v bs' y;
      claim_winv p v rts s.bs bs' x y;
      claim_xfer p v rts s s' x x' y;
      preserve p v rts s s' w
    end
    else run_local p v rts s w ({ x with vis = CLoad y })

let step_push (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Cons? (Seq.index s.ws w).pend)
          (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    if L.length x.out < p.pkt then begin
      let x' = { x with out = L.hd x.pend :: x.out; pend = L.tl x.pend } in
      FStar.Classical.forall_intro (cl_cons (L.hd x.pend) x.out);
      FStar.Classical.forall_intro (cl_cons (L.hd x.pend) (L.tl x.pend));
      assert (x.pend == L.hd x.pend :: L.tl x.pend);
      lok_cons p v s.bs (L.hd x.pend) x.out;
      lok_cons p v s.bs (L.hd x.pend) (L.tl x.pend);
      assert (winv p v rts s.bs x');
      run_local p v rts s w x'
    end else begin
      let x' = { x with pub = x.out; out = []; pc = Lk } in
      len_pos x.out;
      FStar.Classical.forall_intro cl_nil;
      run_local p v rts s w x'
    end

let step_swap_pop (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Nil? (Seq.index s.ws w).pend /\ (Seq.index s.ws w).scan.el == 0 /\
                    not (Seq.index s.ws w).chk /\
                    ~(Nil? (Seq.index s.ws w).inp /\ Nil? (Seq.index s.ws w).out))
          (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    FStar.Classical.forall_intro cl_nil;
    if Nil? x.inp then run_local p v rts s w ({ x with inp = x.out; out = x.inp })
    else begin
      let e = L.hd x.inp in
      let x1 = { x with inp = L.tl x.inp; tick = x.tick + 1; chk = ((x.tick + 1) % p.tickp = 0) } in
      FStar.Classical.forall_intro (cl_cons e (L.tl x.inp));
      assert (x.inp == e :: L.tl x.inp);
      lok_cons p v s.bs e (L.tl x.inp);
      assert (eok p v s.bs e /\ lok p v s.bs x1.inp);
      if e.el > p.chunk then begin
        let sc = { es = e.es; el = p.chunk } in
        let r = rest_of e p.chunk in
        eok_sub p v s.bs e sc;
        eok_sub p v s.bs e r;
        FStar.Classical.forall_intro (cl_cons r []);
        lok_cons p v s.bs r [];
        FStar.Classical.forall_intro (FStar.Classical.move_requires (covers_split e p.chunk));
        run_local p v rts s w ({ x1 with scan = sc; pend = [r] })
      end
      else run_local p v rts s w ({ x1 with scan = e })
    end

let step_idle (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Nil? (Seq.index s.ws w).pend /\ (Seq.index s.ws w).scan.el == 0 /\
                    not (Seq.index s.ws w).chk /\
                    Nil? (Seq.index s.ws w).inp /\ Nil? (Seq.index s.ws w).out)
          (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    FStar.Classical.forall_intro cl_nil;
    let x' = { x with active = false; pc = Id1 } in
    let s' = upd ({ s with cnt = (if s.cnt > 0 then s.cnt - 1 else 0) }) w x' in
    assert (units x == 1 /\ units x' == 0 /\ s.cnt >= 1);
    xfer_mono p v s s' x x';
    preserve p v rts s s' w

let field_of_b (p: params) (x a: nat) : bool =
  x <= a && a < x + 8 * p.nf x && (a - x) % 8 = 0

/// The worker after visiting the word at the start of its scan range.
let visit_x (p: params) (bs: Seq.seq U32.t) (x: wst{x.scan.el > 0}) : wst =
  let a0 = x.scan.es in
  let x0 = { x with scan = advance x.scan } in
  match p.tst a0 with
  | None -> x0
  | Some t -> if marked bs t then x0
             else (match p.tgt a0 with
                   | None -> x0
                   | Some y -> { x0 with vis = CLoad y })

let eok_advance (p: params) (v: view) (bs: Seq.seq U32.t) (e: entry)
  : Lemma (requires eok p v bs e /\ e.el > 0) (ensures eok p v bs (advance e))
  = eok_sub p v bs e (advance e)

/// The visited word's obligation is met: its target is marked, or claimed.
let visit_at (p: params) (v: view) (rts: list nat) (bs: Seq.seq U32.t) (x: wst) (o a z: nat)
  : Lemma (requires vok p v rts /\ i1 p v rts bs /\ eok p v bs x.scan /\ x.scan.el > 0 /\
                    x.vis == CNone /\ x.pend == [] /\
                    field_of p o a /\ p.tgt a == Some z /\ obl x a z)
          (ensures marked bs (ybit z) \/ obl (visit_x p bs x) a z)
  = let a0 = x.scan.es in
    vok_reveal p v rts;
    cl_nil a;
    if a <> a0 then begin
      if covers x.scan a then covers_advance x.scan a
    end else begin
      covers_field p v bs x.scan a0;
      eliminate exists (x0: nat). v.ok x0 /\ marked bs (ybit x0) /\ field_of p x0 a0
      with begin
        match p.tst a0 with
        | None -> ()
        | Some t ->
          if marked bs t then begin
            assert (v.ok (t + 8));
            assert (t + 8 >= 8 /\ (t + 8) - 8 == t);
            assert (p.tgt a0 == Some (t + 8));
            assert (ybit z == t)
          end
          else ()
      end
    end

/// A claim of the visited word's target is for a reachable object.
let visit_vis (p: params) (v: view) (rts: list nat) (bs: Seq.seq U32.t) (x: wst) (y: nat)
  : Lemma (requires vok p v rts /\ i1 p v rts bs /\ eok p v bs x.scan /\ x.scan.el > 0 /\
                    p.tgt x.scan.es == Some y)
          (ensures v.ok y /\ reach p rts y)
  = vok_reveal p v rts;
    covers_field p v bs x.scan x.scan.es;
    eliminate exists (x0: nat). v.ok x0 /\ marked bs (ybit x0) /\ field_of p x0 x.scan.es
    with begin
      vok_reveal p v rts;
      assert (x0 >= 8);
      marked_obj p v rts bs x0;
      reach_step p rts x0 x.scan.es y
    end

let visit_winv (p: params) (v: view) (rts: list nat) (bs: Seq.seq U32.t) (x: wst)
  : Lemma (requires vok p v rts /\ i1 p v rts bs /\ winv p v rts bs x /\ x.pc == Run /\ x.scan.el > 0 /\
                    x.vis == CNone /\ x.pend == [])
          (ensures winv p v rts bs (visit_x p bs x))
  = eok_advance p v bs x.scan;
    match (visit_x p bs x).vis with
    | CLoad y -> visit_vis p v rts bs x y
    | _ -> ()

let visit_xfer (p: params) (v: view) (rts: list nat) (s s': mstate) (x: wst)
  : Lemma (requires vok p v rts /\ i1 p v rts s.bs /\ eok p v s.bs x.scan /\ x.scan.el > 0 /\
                    x.vis == CNone /\ x.pend == [] /\ s'.bs == s.bs /\ s'.pool == s.pool)
          (ensures xfer p v s s' x (visit_x p s.bs x))
  = let aux (o a z: nat) : Lemma (xfer_at p v s s' x (visit_x p s.bs x) o a z)
      = if v.ok o && marked s.bs (ybit o) && field_of_b p o a && p.tgt a = Some z && obl x a z then
          visit_at p v rts s.bs x o a z
    in
    FStar.Classical.forall_intro_3 aux

let step_visit (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires vok p v rts /\ inv p v rts s /\ (Seq.index s.ws w).pc == Run /\
                    (Seq.index s.ws w).vis == CNone /\ Nil? (Seq.index s.ws w).pend /\
                    (Seq.index s.ws w).scan.el > 0)
          (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    get_shared p v rts s;
    let x' = visit_x p s.bs x in
    assert (wstep p s w == upd s w x');
    visit_winv p v rts s.bs x;
    visit_xfer p v rts s (upd s w x') x;
    same_shared p v rts s w x'

let step_chk (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires inv p v rts s /\ (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Nil? (Seq.index s.ws w).pend /\ (Seq.index s.ws w).scan.el == 0 /\ (Seq.index s.ws w).chk)
          (ensures inv p v rts (wstep p s w))
  = get_w p v rts s w;
    pc_step p v rts s w Sh1 false

let step_run (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires view_ok p v rts /\ inv p v rts s /\ (Seq.index s.ws w).pc == Run)
          (ensures inv p v rts (wstep p s w))
  = let x = Seq.index s.ws w in
    match x.vis with
    | CLoad y -> (get_shared p v rts s; step_cload p v rts s w y)
    | CCas (y, old) -> (vok_reveal p v rts; step_ccas p v rts s w y old)
    | CNone ->
      if Cons? x.pend then step_push p v rts s w
      else if x.scan.el > 0 then (vok_reveal p v rts; step_visit p v rts s w)
      else if x.chk then step_chk p v rts s w
      else if Nil? x.inp && Nil? x.out then step_idle p v rts s w
      else step_swap_pop p v rts s w

/// **No step breaks the invariant.**
let step_inv (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires view_ok p v rts /\ inv p v rts s) (ensures inv p v rts (wstep p s w))
  = match (Seq.index s.ws w).pc with
    | Run -> step_run p v rts s w
    | Sh1 -> step_sh1 p v rts s w
    | Sh2 -> step_sh2 p v rts s w
    | Sh3 -> step_sh3 p v rts s w
    | Lk -> step_lk p v rts s w
    | Cs1 -> step_cs1 p v rts s w
    | Cs2 -> step_cs2 p v rts s w
    | Cs3 -> step_cs3 p v rts s w
    | Id1 -> step_id1 p v rts s w
    | Id2 -> step_id2 p v rts s w
    | Tk1 -> step_tk1 p v rts s w
    | Tk2 -> step_tk2 p v rts s w
    | Id3 -> step_id3 p v rts s w
    | Id4 -> step_id4 p v rts s w
    | Id5 -> step_id5 p v rts s w
    | Done -> step_done p v rts s w

/// **The invariant holds after any interleaving.**
#push-options "--fuel 1"
let rec run_inv (p: params) (v: view) (rts: list nat) (s: mstate) (sched: list nat)
  : Lemma (requires view_ok p v rts /\ inv p v rts s) (ensures inv p v rts (run p s sched))
          (decreases sched)
  = match sched with
    | [] -> ()
    | w :: rest ->
      if w < Seq.length s.ws then begin
        step_inv p v rts s w;
        run_inv p v rts (wstep p s w) rest
      end
      else run_inv p v rts s rest
#pop-options
