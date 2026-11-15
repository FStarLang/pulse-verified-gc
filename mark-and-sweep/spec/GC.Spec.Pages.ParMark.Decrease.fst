/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Decrease - every step that does not wait decreases mu
/// ---------------------------------------------------------------------------
///
/// `step_mu`: under the invariant, a step of a worker that is not `waiting`
/// strictly decreases `Measure.mu`, and a waiting step changes no shared state
/// and keeps it.  The steps fall in three groups:
///   - most keep the bitmap and the pool, so only the stepping worker's
///     weight and the shared flags change (`mu_same`);
///   - publishing to the pool can only lower the other workers' weights
///     (`mu_push`);
///   - a successful claim CAS and a take from the pool can raise the other
///     workers' weights, by at most `kk p` in all, which the claim
///     (`w_u`) and the pool packet (`p_pool`) pay for (`mu_crude`).

module GC.Spec.Pages.ParMark.Decrease

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Bits
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach
open GC.Spec.Pages.ParMark.Inv
open GC.Spec.Pages.ParMark.Measure

module U32 = FStar.UInt32
module Seq = FStar.Seq
module L = FStar.List.Tot
module Sf = GC.Spec.Pages.ParMark.Safety

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Sums
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec sum_ext_f (f g: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws})
  : Lemma (requires forall (x: wst). f x == g x) (ensures sumw f ws n == sumw g ws n) (decreases n)
  = if n = 0 then () else sum_ext_f f g ws (n - 1)

let rec sum_le_f (f g: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws})
  : Lemma (requires forall (x: wst). f x <= g x) (ensures sumw f ws n <= sumw g ws n) (decreases n)
  = if n = 0 then () else sum_le_f f g ws (n - 1)

let rec sum_bound (f: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws}) (b: nat)
  : Lemma (requires forall (x: wst). f x <= b) (ensures sumw f ws n <= b * n) (decreases n)
  = if n = 0 then () else sum_bound f ws (n - 1) b

let rec sum_add (f g: wst -> nat) (ws: Seq.seq wst) (n: nat{n <= Seq.length ws})
  : Lemma (ensures sumw (fun x -> f x + g x) ws n == sumw f ws n + sumw g ws n) (decreases n)
  = if n = 0 then () else sum_add f g ws (n - 1)
#pop-options

let psi_le (s: mstate) (x: wst) : Lemma (psi s x <= 3) = ()

let phi_split (p: params) (v: view) (s: mstate)
  : Lemma (mu p v s == glob p v s + sumw (phi0 p) s.ws (Seq.length s.ws) + sumw (psi s) s.ws (Seq.length s.ws))
  = sum_ext_f (phi p s) (fun x -> phi0 p x + psi s x) s.ws (Seq.length s.ws);
    sum_add (phi0 p) (psi s) s.ws (Seq.length s.ws)

/// ---------------------------------------------------------------------------
/// The three groups
/// ---------------------------------------------------------------------------

let upd_facts (s s': mstate) (w: nat) : prop =
  w < Seq.length s.ws /\ Seq.length s'.ws == Seq.length s.ws /\ s'.ws == Seq.upd s.ws w (Seq.index s'.ws w)

/// The bitmap and the pool unchanged.
let mu_same (p: params) (v: view) (s s': mstate) (w: nat)
  : Lemma (requires upd_facts s s' w /\ s'.bs == s.bs /\ s'.pool == s.pool)
          (ensures mu p v s' + phi p s (Seq.index s.ws w) ==
                   mu p v s + phi p s (Seq.index s'.ws w) + glob p v s' - glob p v s)
  = sum_ext_f (phi p s') (phi p s) s'.ws (Seq.length s'.ws);
    sum_upd (phi p s) s.ws (Seq.length s.ws) w (Seq.index s'.ws w)

let psi_push (s s': mstate) (x: wst)
  : Lemma (requires s'.bs == s.bs /\ Cons? s'.pool) (ensures psi s' x <= psi s x)
  = ()

/// A packet pushed to the pool.
let mu_push (p: params) (v: view) (s s': mstate) (w: nat)
  : Lemma (requires upd_facts s s' w /\ s'.bs == s.bs /\ Cons? s'.pool)
          (ensures mu p v s' + phi p s (Seq.index s.ws w) <=
                   mu p v s + phi p s (Seq.index s'.ws w) + glob p v s' - glob p v s)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (psi_push s s'));
    sum_le_f (phi p s') (phi p s) s'.ws (Seq.length s'.ws);
    sum_upd (phi p s) s.ws (Seq.length s.ws) w (Seq.index s'.ws w)

/// Anything: the other workers' `psi` can grow by at most `kk p`.
let mu_crude (p: params) (v: view) (s s': mstate) (w: nat)
  : Lemma (requires upd_facts s s' w /\ Seq.length s.ws == p.k)
          (ensures mu p v s' + phi0 p (Seq.index s.ws w) <=
                   mu p v s + phi0 p (Seq.index s'.ws w) + glob p v s' - glob p v s + kk p)
  = phi_split p v s;
    phi_split p v s';
    sum_upd (phi0 p) s.ws (Seq.length s.ws) w (Seq.index s'.ws w);
    FStar.Classical.forall_intro (psi_le s');
    sum_bound (psi s') s'.ws (Seq.length s'.ws) 3

/// ---------------------------------------------------------------------------
/// Lists
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let lsum_nil (wt c: nat) : Lemma (lsum wt c [] == 0) = ()
let lsum_cons (wt c: nat) (e: entry) (l: list entry) : Lemma (lsum wt c (e :: l) == entw wt c e + lsum wt c l) = ()
let psum_cons (p: params) (l: list entry) (q: list (list entry))
  : Lemma (psum p (l :: q) == p_pool p + lsum (e_in p) (ce p) l + psum p q) = ()

/// Moving entries to a lighter place.
let rec lsum_weights (w1 w2 c: nat) (l: list entry)
  : Lemma (requires w1 <= w2) (ensures lsum w1 c l + (w2 - w1) * L.length l == lsum w2 c l) (decreases l)
  = match l with
    | [] -> ()
    | _ :: r -> lsum_weights w1 w2 c r

let rec lsum_split (wt c: nat) (n: nat) (l: list entry)
  : Lemma (ensures lsum wt c l == lsum wt c (fst (L.splitAt n l)) + lsum wt c (snd (L.splitAt n l)))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: r -> if n = 0 then () else lsum_split wt c (n - 1) r

/// An object's entries weigh at most (weight + field weight) per field.
let rec lsum_push_obj (wt c: nat) (ml: pos) (a n: nat)
  : Lemma (ensures lsum wt c (push_obj ml a n) <= (wt + c) * n) (decreases n)
  = if n = 0 then ()
    else if n <= ml then begin
      assert (push_obj ml a n == [{ es = a; el = n }]);
      lsum_cons wt c ({ es = a; el = n }) [];
      FStar.Math.Lemmas.distributivity_add_left wt c n;
      FStar.Math.Lemmas.lemma_mult_le_right wt 1 n
    end
    else begin
      lsum_push_obj wt c ml (a + 8 * ml) (n - ml);
      lsum_cons wt c ({ es = a; el = ml }) (push_obj ml (a + 8 * ml) (n - ml));
      FStar.Math.Lemmas.distributivity_add_right (wt + c) ml (n - ml);
      FStar.Math.Lemmas.distributivity_add_left wt c ml;
      FStar.Math.Lemmas.lemma_mult_le_right wt 1 ml
    end
#pop-options

let len_pos (#a: Type) (l: list a) : Lemma (Cons? l <==> L.length l >= 1) = Sf.len_pos l

/// ---------------------------------------------------------------------------
/// Steps that keep the bitmap and the pool
/// ---------------------------------------------------------------------------

let dec_same (p: params) (v: view) (s s': mstate) (w: nat)
  : Lemma (requires upd_facts s s' w /\ s'.bs == s.bs /\ s'.pool == s.pool /\
                    phi p s (Seq.index s'.ws w) + glob p v s' < phi p s (Seq.index s.ws w) + glob p v s)
          (ensures mu p v s' < mu p v s)
  = mu_same p v s s' w

let eq_same (p: params) (v: view) (s s': mstate) (w: nat)
  : Lemma (requires upd_facts s s' w /\ shared_eq s s' /\
                    phi p s (Seq.index s'.ws w) == phi p s (Seq.index s.ws w))
          (ensures mu p v s' == mu p v s)
  = mu_same p v s s' w

let get_w (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat)
  : Lemma (requires inv p v rts s /\ w < Seq.length s.ws)
          (ensures winv p v rts s.bs (Seq.index s.ws w) /\ i1 p v rts s.bs /\ s.nfull == L.length s.pool /\
                   Seq.length s.ws == p.k /\ lock_ok s /\ pool_ok p v s.bs s.pool)
  = inv_reveal p v rts s

/// A step that changes the phase only (and the share check), with the
/// flags as given.
let pc_dec (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws}) (c: pc) (ck: bool) (s0: mstate)
  : Lemma (requires s0.bs == s.bs /\ s0.pool == s.pool /\ s0.ws == s.ws /\
                    (let x = Seq.index s.ws w in
                     let x' = { x with pc = c; chk = ck } in
                     phi p s x' + glob p v s0 < phi p s x + glob p v s))
          (ensures mu p v (upd s0 w ({ Seq.index s.ws w with pc = c; chk = ck })) < mu p v s)
  = let x = Seq.index s.ws w in
    let s' = upd s0 w ({ x with pc = c; chk = ck }) in
    assert (Seq.index s'.ws w == { x with pc = c; chk = ck });
    dec_same p v s s' w

let pc_eq (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws}) (c: pc)
  : Lemma (requires (let x = Seq.index s.ws w in phi p s ({ x with pc = c }) == phi p s x))
          (ensures (let s' = upd s w ({ Seq.index s.ws w with pc = c }) in
                    shared_eq s s' /\ mu p v s' == mu p v s))
  = let x = Seq.index s.ws w in
    let s' = upd s w ({ x with pc = c }) in
    assert (Seq.index s'.ws w == { x with pc = c });
    eq_same p v s s' w

/// The weight of a worker that holds nothing.
let nb (x: wst) : prop =
  x.inp == [] /\ x.out == [] /\ x.pend == [] /\ x.pub == [] /\ x.scan.el == 0 /\ x.vis == CNone /\
  ~x.active /\ x.got == None

let phi_nb (p: params) (s: mstate) (x: wst)
  : Lemma (requires nb x)
          (ensures phi p s x == ph p x + (if x.chk then c_chk p else 0) + psi s x)
  = lsum_nil (e_in p) (ce p);
    lsum_nil (e_out p) (ce p);
    lsum_nil (e_p p) (ce p)

let nb_pc (x: wst) (c: pc) : Lemma (requires nb x) (ensures nb ({ x with pc = c })) = ()

/// The facts the idle phases use.
let idle_facts (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat)
  : Lemma (requires inv p v rts s /\ w < Seq.length s.ws /\ ~(busy (Seq.index s.ws w).pc) /\
                    (Seq.index s.ws w).pc <> Tk2)
          (ensures nb (Seq.index s.ws w) /\ s.nfull == L.length s.pool)
  = get_w p v rts s w

let go (p: params) (s: mstate) (x: wst) (c: pc)
  : Lemma (requires nb x)
          (ensures phi p s ({ x with pc = c }) == ph p ({ x with pc = c }) + (if x.chk then c_chk p else 0) +
                                                psi s ({ x with pc = c }) /\
                   phi p s x == ph p x + (if x.chk then c_chk p else 0) + psi s x)
  = nb_pc x c; phi_nb p s ({ x with pc = c }); phi_nb p s x

let mu_id1 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires nb (Seq.index s.ws w) /\ (Seq.index s.ws w).pc == Id1 /\ s.nfull == L.length s.pool)
          (ensures shared_eq s (wstep p s w) /\ mu p v (wstep p s w) == mu p v s)
  = let x = Seq.index s.ws w in
    if s.nfull > 0 then (len_pos s.pool; go p s x Id2; pc_eq p v s w Id2)
    else (go p s x Id3; pc_eq p v s w Id3)

let mu_id2 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires nb (Seq.index s.ws w) /\ (Seq.index s.ws w).pc == Id2)
          (ensures (if waiting s (Seq.index s.ws w)
                    then shared_eq s (wstep p s w) /\ mu p v (wstep p s w) == mu p v s
                    else mu p v (wstep p s w) < mu p v s))
  = let x = Seq.index s.ws w in
    if s.lk then begin
      go p s x Id5;
      if Cons? s.pool then pc_eq p v s w Id5 else pc_dec p v s w Id5 x.chk s
    end
    else (go p s x Tk1; pc_dec p v s w Tk1 x.chk ({ s with lk = true }))

let mu_id3 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires nb (Seq.index s.ws w) /\ (Seq.index s.ws w).pc == Id3)
          (ensures shared_eq s (wstep p s w) /\ mu p v (wstep p s w) == mu p v s)
  = let x = Seq.index s.ws w in
    if s.flag then (go p s x Id5; pc_eq p v s w Id5) else (go p s x Id4; pc_eq p v s w Id4)

let mu_id4 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires nb (Seq.index s.ws w) /\ (Seq.index s.ws w).pc == Id4)
          (ensures (if waiting s (Seq.index s.ws w)
                    then shared_eq s (wstep p s w) /\ mu p v (wstep p s w) == mu p v s
                    else mu p v (wstep p s w) < mu p v s))
  = let x = Seq.index s.ws w in
    go p s x Id5;
    if s.flag then begin
      let s' = wstep p s w in
      assert (Seq.index s'.ws w == { x with pc = Id5 });
      eq_same p v s s' w
    end else pc_dec p v s w Id5 x.chk ({ s with flag = true })

let mu_id5 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires nb (Seq.index s.ws w) /\ (Seq.index s.ws w).pc == Id5)
          (ensures (if waiting s (Seq.index s.ws w)
                    then shared_eq s (wstep p s w) /\ mu p v (wstep p s w) == mu p v s
                    else mu p v (wstep p s w) < mu p v s))
  = let x = Seq.index s.ws w in
    go p s x Done; go p s x Id1;
    if s.cnt = 0 then pc_dec p v s w Done x.chk s else pc_eq p v s w Id1

/// ---------------------------------------------------------------------------
/// Lock, publish, share check, take
/// ---------------------------------------------------------------------------

let not_ph (c: pc) : bool = c <> Id2 && c <> Tk1

/// Changing only the phase and the share check.
let phi_pc (p: params) (s: mstate) (x: wst) (c: pc) (ck: bool)
  : Lemma (requires not_ph x.pc /\ not_ph c /\ x.pc <> Tk2 /\ c <> Tk2)
          (ensures phi p s ({ x with pc = c; chk = ck }) + ph p x + (if x.chk then c_chk p else 0) ==
                   phi p s x + ph p ({ x with pc = c; chk = ck }) + (if ck then c_chk p else 0))
  = ()

let mu_lk (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Lk)
          (ensures (if waiting s (Seq.index s.ws w)
                    then shared_eq s (wstep p s w) /\ mu p v (wstep p s w) == mu p v s
                    else mu p v (wstep p s w) < mu p v s))
  = let x = Seq.index s.ws w in
    if s.lk then ()
    else (phi_pc p s x Cs1 x.chk; pc_dec p v s w Cs1 x.chk ({ s with lk = true }))

let mu_cs1 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Cs1) (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    phi_pc p s x Cs2 x.chk; pc_dec p v s w Cs2 x.chk ({ s with cnt = s.cnt + 1 })

let mu_cs3 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Cs3 /\ s.lk) (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    phi_pc p s x Run x.chk; pc_dec p v s w Run x.chk ({ s with lk = false })

let mu_cs2 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Cs2) (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    let x' = { x with pub = []; pc = Cs3 } in
    let s' = upd ({ s with pool = x.pub :: s.pool; nfull = s.nfull + 1 }) w x' in
    assert (Seq.index s'.ws w == x');
    psum_cons p x.pub s.pool;
    lsum_nil (e_in p) (ce p);
    assert (phi p s x' + lsum (e_in p) (ce p) x.pub + ph_cs2 p == phi p s x + ph_cs3);
    mu_push p v s s' w

let mu_sh12 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Sh1 \/ (Seq.index s.ws w).pc == Sh2)
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    phi_pc p s x Run x.chk;
    phi_pc p s x Sh2 x.chk;
    phi_pc p s x Sh3 x.chk;
    if x.pc = Sh1 then (if s.nfull <> 0 then pc_dec p v s w Run x.chk s else pc_dec p v s w Sh2 x.chk s)
    else (if not s.flag || L.length (share_src x) < p.smin then pc_dec p v s w Run x.chk s
          else pc_dec p v s w Sh3 x.chk s)

/// The share: the given half weighs as the input packet, never more.
let share_phi (p: params) (s: mstate) (x: wst)
  : Lemma (requires x.pc == Sh3 /\ x.pub == [] /\ L.length (share_src x) / 2 > 0)
          (ensures phi p s (Sf.share_x x) + ph_sh3 p <= phi p s x + ph_lk p)
  = let src = share_src x in
    let h = L.length src / 2 in
    let n = L.length src - h in
    lsum_split (e_in p) (ce p) n src;
    lsum_split (e_out p) (ce p) n src;
    lsum_weights (e_in p) (e_out p) (ce p) (snd (L.splitAt n src));
    lsum_nil (e_in p) (ce p)

let mu_sh3 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Sh3 /\ (Seq.index s.ws w).pub == [])
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    if not s.flag then (phi_pc p s x Run x.chk; pc_dec p v s w Run x.chk s)
    else begin
      let h = L.length (share_src x) / 2 in
      if h = 0 then (phi_pc p s x Run x.chk; pc_dec p v s w Run x.chk ({ s with flag = false }))
      else begin
        Sf.half_pos (L.length (share_src x));
        Sf.share_x_eq x;
        let s' = upd ({ s with flag = false }) w (Sf.share_x x) in
        assert (s' == wstep p s w);
        assert (Seq.index s'.ws w == Sf.share_x x);
        share_phi p s x;
        dec_same p v s s' w
      end
    end

let mu_tk1 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires nb (Seq.index s.ws w) /\ (Seq.index s.ws w).pc == Tk1 /\ Seq.length s.ws == p.k)
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    lsum_nil (e_in p) (ce p);
    lsum_nil (e_out p) (ce p);
    lsum_nil (e_p p) (ce p);
    match s.pool with
    | [] ->
      let x' = { x with got = None; pc = Tk2 } in
      let s' = upd s w x' in
      assert (Seq.index s'.ws w == x');
      dec_same p v s s' w
    | q :: rest ->
      let x' = { x with got = Some q; pc = Tk2 } in
      let s' = upd ({ s with pool = rest; nfull = (if s.nfull > 0 then s.nfull - 1 else 0) }) w x' in
      assert (Seq.index s'.ws w == x');
      psum_cons p q rest;
      assert (phi0 p x' == phi0 p x + lsum (e_in p) (ce p) q + 3);
      mu_crude p v s s' w;
      assert (psi s x >= 0)

let mu_tk2 (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Tk2 /\ s.lk /\ (Seq.index s.ws w).inp == [] /\
                    ~(Seq.index s.ws w).active)
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    lsum_nil (e_in p) (ce p);
    match x.got with
    | Some q ->
      let x' = { x with inp = q; got = None; active = true; chk = false; pc = Run } in
      let s' = upd ({ s with lk = false }) w x' in
      assert (Seq.index s'.ws w == x');
      dec_same p v s s' w
    | None ->
      let x' = { x with pc = Id5 } in
      let s' = upd ({ s with lk = false }) w x' in
      assert (Seq.index s'.ws w == x');
      dec_same p v s s' w

/// ---------------------------------------------------------------------------
/// The busy worker
/// ---------------------------------------------------------------------------

let mu_cload (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws}) (y: nat)
  : Lemma (requires (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CLoad y /\
                    in_pages (ybit y) /\ Seq.length s.bs == bm_len)
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    let x' = if marked s.bs (ybit y) then { x with vis = CNone } else { x with vis = CCas (y, bword s.bs (ybit y)) } in
    let s' = upd s w x' in
    assert (s' == wstep p s w);
    assert (Seq.index s'.ws w == x');
    dec_same p v s s' w

#push-options "--fuel 1"
/// Marking a claimable object lowers the count of unmarked ones.
let rec unmarked_dec (bs bs': Seq.seq U32.t) (u: list nat) (y: nat)
  : Lemma (requires grows bs bs')
          (ensures unmarked bs' u <= unmarked bs u /\
                   (L.mem y u /\ ~(marked bs (ybit y)) /\ marked bs' (ybit y) ==> unmarked bs' u < unmarked bs u))
          (decreases u)
  = match u with
    | [] -> ()
    | _ :: r -> unmarked_dec bs bs' r y
#pop-options

let wu_dec (a b c: nat) : Lemma (requires b < c) (ensures a * b + a <= a * c)
  = FStar.Math.Lemmas.lemma_mult_le_left a (b + 1) c;
    FStar.Math.Lemmas.distributivity_add_right a b 1

let nf_bound (e c n m: nat) : Lemma (requires n <= m) (ensures (e + c) * n <= (e + c) * m)
  = FStar.Math.Lemmas.lemma_mult_le_left (e + c) n m

/// The claim CAS: it fails only on a stale read, and a success marks a
/// claimable object, which pays for its entries and the others' stale reads.
let mu_ccas (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws}) (y: nat) (old: U32.t)
  : Lemma (requires (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CCas (y, old) /\
                    (Seq.index s.ws w).pend == [] /\ Seq.length s.ws == p.k /\
                    ~(in_pages (ybit y) /\ bit_of old (widx (ybit y) % 32)) /\
                    L.mem y v.univ /\ p.nf y <= v.maxnf)
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    if fresh s.bs y old then begin
      let bs' = set_bit s.bs (ybit y) in
      let x' = { x with vis = CNone; pend = obj_entries p y } in
      let s' = upd ({ s with bs = bs' }) w x' in
      assert (s' == wstep p s w);
      assert (Seq.index s'.ws w == x');
      marked_bword s.bs (ybit y);
      set_bit_marked s.bs (ybit y) (ybit y);
      grows_set s.bs (ybit y);
      unmarked_dec s.bs bs' v.univ y;
      wu_dec (w_u p v) (unmarked bs' v.univ) (unmarked s.bs v.univ);
      lsum_nil (e_p p) (ce p);
      lsum_push_obj (e_p p) (ce p) p.maxlen y (p.nf y);
      nf_bound (e_p p) (ce p) (p.nf y) v.maxnf;
      assert (phi0 p x' + 2 == phi0 p x + lsum (e_p p) (ce p) (obj_entries p y));
      mu_crude p v s s' w
    end else begin
      let x' = { x with vis = CLoad y } in
      let s' = upd s w x' in
      assert (s' == wstep p s w);
      assert (Seq.index s'.ws w == x');
      dec_same p v s s' w
    end

let mu_pushe (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Cons? (Seq.index s.ws w).pend /\ (Seq.index s.ws w).pub == [])
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    if L.length x.out < p.pkt then begin
      let x' = { x with out = L.hd x.pend :: x.out; pend = L.tl x.pend } in
      let s' = upd s w x' in
      assert (Seq.index s'.ws w == x');
      lsum_cons (e_out p) (ce p) (L.hd x.pend) x.out;
      lsum_cons (e_p p) (ce p) (L.hd x.pend) (L.tl x.pend);
      assert (x.pend == L.hd x.pend :: L.tl x.pend);
      dec_same p v s s' w
    end else begin
      let x' = { x with pub = x.out; out = []; pc = Lk } in
      let s' = upd s w x' in
      assert (Seq.index s'.ws w == x');
      len_pos x.out;
      lsum_nil (e_in p) (ce p);
      lsum_nil (e_out p) (ce p);
      lsum_weights (e_in p) (e_out p) (ce p) x.out;
      FStar.Math.Lemmas.lemma_mult_le_left (e_out p - e_in p) 1 (L.length x.out);
      dec_same p v s s' w
    end

let mu_visit (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Nil? (Seq.index s.ws w).pend /\ (Seq.index s.ws w).scan.el > 0)
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    let x' = Sf.visit_x p s.bs x in
    let s' = upd s w x' in
    assert (s' == wstep p s w);
    assert (Seq.index s'.ws w == x');
    dec_same p v s s' w

let mu_chk (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Nil? (Seq.index s.ws w).pend /\ (Seq.index s.ws w).scan.el == 0 /\ (Seq.index s.ws w).chk)
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    phi_pc p s x Sh1 false;
    pc_dec p v s w Sh1 false s

let mu_go_idle (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Nil? (Seq.index s.ws w).pend /\ (Seq.index s.ws w).scan.el == 0 /\
                    not (Seq.index s.ws w).chk /\ (Seq.index s.ws w).active /\
                    Nil? (Seq.index s.ws w).inp /\ Nil? (Seq.index s.ws w).out)
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    let x' = { x with active = false; pc = Id1 } in
    let s' = upd ({ s with cnt = (if s.cnt > 0 then s.cnt - 1 else 0) }) w x' in
    assert (Seq.index s'.ws w == x');
    dec_same p v s s' w

let pop_arith (ein ep cchk cs c chunk el: nat)
  : Lemma (requires el > chunk /\ chunk >= 1 /\ c >= cs /\ ep >= ein /\ (c - cs) >= ep - ein + cchk + 1)
          (ensures cs * chunk + ep + c * (el - chunk) + cchk < ein + c * el)
  = FStar.Math.Lemmas.distributivity_sub_right c el chunk;
    FStar.Math.Lemmas.distributivity_sub_left c cs chunk;
    FStar.Math.Lemmas.lemma_mult_le_right chunk 1 (c - cs);
    assert ((c - cs) * chunk >= (c - cs))

let pop_arith1 (ein cchk cs c el: nat)
  : Lemma (requires c >= cs /\ ein > cchk) (ensures cs * el + cchk < ein + c * el)
  = FStar.Math.Lemmas.lemma_mult_le_right el cs c

let mu_swap_pop (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires (Seq.index s.ws w).pc == Run /\ (Seq.index s.ws w).vis == CNone /\
                    Nil? (Seq.index s.ws w).pend /\ (Seq.index s.ws w).scan.el == 0 /\
                    not (Seq.index s.ws w).chk /\
                    ~(Nil? (Seq.index s.ws w).inp /\ Nil? (Seq.index s.ws w).out))
          (ensures mu p v (wstep p s w) < mu p v s)
  = let x = Seq.index s.ws w in
    lsum_nil (e_in p) (ce p);
    lsum_nil (e_out p) (ce p);
    lsum_nil (e_p p) (ce p);
    if Nil? x.inp then begin
      let x' = { x with inp = x.out; out = x.inp } in
      let s' = upd s w x' in
      assert (Seq.index s'.ws w == x');
      len_pos x.out;
      lsum_weights (e_in p) (e_out p) (ce p) x.out;
      FStar.Math.Lemmas.lemma_mult_le_left (e_out p - e_in p) 1 (L.length x.out);
      dec_same p v s s' w
    end else begin
      let e = L.hd x.inp in
      assert (x.inp == e :: L.tl x.inp);
      lsum_cons (e_in p) (ce p) e (L.tl x.inp);
      let x1 = { x with inp = L.tl x.inp; tick = x.tick + 1; chk = ((x.tick + 1) % p.tickp = 0) } in
      if e.el > p.chunk then begin
        let r = rest_of e p.chunk in
        let x' = { x1 with scan = { es = e.es; el = p.chunk }; pend = [r] } in
        let s' = upd s w x' in
        assert (s' == wstep p s w);
        assert (Seq.index s'.ws w == x');
        lsum_cons (e_p p) (ce p) r [];
        pop_arith (e_in p) (e_p p) (c_chk p) c_s (ce p) p.chunk e.el;
        dec_same p v s s' w
      end else begin
        let x' = { x1 with scan = e } in
        let s' = upd s w x' in
        assert (s' == wstep p s w);
        assert (Seq.index s'.ws w == x');
        pop_arith1 (e_in p) (c_chk p) c_s (ce p) e.el;
        dec_same p v s s' w
      end
    end

/// ---------------------------------------------------------------------------
/// Every step
/// ---------------------------------------------------------------------------

let step_ok (p: params) (v: view) (s: mstate) (w: nat{w < Seq.length s.ws}) : prop =
  if waiting s (Seq.index s.ws w)
  then shared_eq s (wstep p s w) /\ mu p v (wstep p s w) == mu p v s
  else mu p v (wstep p s w) < mu p v s

let run_mu (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires view_ok p v rts /\ inv p v rts s /\ (Seq.index s.ws w).pc == Run)
          (ensures step_ok p v s w)
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    match x.vis with
    | CLoad y -> mu_cload p v s w y
    | CCas (y, old) -> mu_ccas p v s w y old
    | CNone ->
      if Cons? x.pend then mu_pushe p v s w
      else if x.scan.el > 0 then mu_visit p v s w
      else if x.chk then mu_chk p v s w
      else if Nil? x.inp && Nil? x.out then mu_go_idle p v s w
      else mu_swap_pop p v s w

/// **Every step that does not wait decreases the measure; a waiting step
/// keeps it and the shared state.**
let step_mu (p: params) (v: view) (rts: list nat) (s: mstate) (w: nat{w < Seq.length s.ws})
  : Lemma (requires view_ok p v rts /\ inv p v rts s) (ensures step_ok p v s w)
  = let x = Seq.index s.ws w in
    get_w p v rts s w;
    match x.pc with
    | Run -> run_mu p v rts s w
    | Sh1 | Sh2 -> mu_sh12 p v s w
    | Sh3 -> mu_sh3 p v s w
    | Lk -> mu_lk p v s w
    | Cs1 -> mu_cs1 p v s w
    | Cs2 -> mu_cs2 p v s w
    | Cs3 -> Sf.lock_mine s w; mu_cs3 p v s w
    | Tk2 -> Sf.lock_mine s w; mu_tk2 p v s w
    | Tk1 -> idle_facts p v rts s w; mu_tk1 p v s w
    | Id1 -> idle_facts p v rts s w; mu_id1 p v s w
    | Id2 -> idle_facts p v rts s w; mu_id2 p v s w
    | Id3 -> idle_facts p v rts s w; mu_id3 p v s w
    | Id4 -> idle_facts p v rts s w; mu_id4 p v s w
    | Id5 -> idle_facts p v rts s w; mu_id5 p v s w
    | Done -> ()
