/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFRepeat - a repeated root changes nothing in the first-fit
/// promotion
/// ---------------------------------------------------------------------------
///
/// Design doc §18, U3 (the table's repeats).  In the promotion's root loop
/// (`Pages.Promote.forward_roots` over first-fit, `FFPromote.fftal`), once an
/// address has been forwarded it is `inert`: forwarded already, or nothing
/// to promote, or its block refused -- and a refusal stays one, since a
/// promotion never makes a blue block of the refused size
/// (`FFNoGrow.nofit`, `step_nofit`).  So forwarding it again is a no-op
/// (`one_noop`), and every root sequence `s` that is `t` with some repeats
/// of earlier roots inserted (`rep s t`) gives the same loop state
/// (`rep_run`) and the same promotion (`promote_rep`).

module GC.Spec.Top.FFRepeat

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
module U64 = FStar.UInt64
module Seq = FStar.Seq
module T = GC.Spec.Top.Iface
module P = GC.Spec.Pages.Promote
module PL = GC.Spec.Pages.Promote.Loop
module GP = GC.Gen.Promote
module NG = GC.Spec.Top.FFNoGrow
module FFP = GC.Spec.Top.FFPromote
module FW = GC.Spec.Top.FFWrite

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let tl (ph: T.phase U64.t) : P.tal U64.t = FFP.fftal ph

/// What the loop runs in: the promotion's context and its invariant.
let rctx (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) : prop =
  PL.ctx (tl ph) ms g0 /\ PL.linv (tl ph) ms g0 cs

/// Forwarding a block that is not infix does nothing.
let ninert (ms: minor_state) (cs: P.gstate U64.t) (y: U64.t) : prop =
  ~(Seq.mem y (minor_objects ms)) \/ cs.P.fwd y <> 0UL \/ minor_wosize ms y == 0 \/
  NG.nofit cs.P.major (minor_wosize ms y)

/// **Forwarding an address does nothing.**
let inert (ms: minor_state) (cs: P.gstate U64.t) (x: U64.t) : prop =
  cs.P.fwd x <> 0UL \/
  (~(is_infix_in_minor ms x) /\ ninert ms cs x) \/
  (is_infix_in_minor ms x /\
   (let p = infix_parent ms x in
    (cs.P.fwd p == 0UL /\ ninert ms cs p) \/
    (cs.P.fwd p <> 0UL /\ ~(U64.v x >= U64.v p /\ U64.v (cs.P.fwd p) + (U64.v x - U64.v p) < heap_size))))

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

/// The allocator's invariant at a loop state.
let inv_of (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t)
  : Lemma (requires rctx ph ms g0 cs) (ensures FW.fshape ph cs.P.major cs.P.st)
  = ()

/// Forwarding a block: it is forwarded after, or nothing happened and it
/// is `ninert`.
#push-options "--z3rlimit 40"
let normal_cases (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y: U64.t)
  : Lemma (requires rctx ph ms g0 cs)
          (ensures (let cs' = P.forward_normal (tl ph) ms cs y in
                    cs'.P.fwd y <> 0UL \/ (cs' == cs /\ ninert ms cs y)))
  = if not (Seq.mem y (minor_objects ms)) || cs.P.fwd y <> 0UL then ()
    else begin
      let wz = minor_wosize ms y in
      if wz = 0 then ()
      else begin
        inv_of ph ms g0 cs;
        NG.promote_fail_nofit ph ms cs.P.major cs.P.st y wz
      end
    end
#pop-options

/// A `ninert` block's forwarding does nothing.
#push-options "--z3rlimit 40"
let normal_noop (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y: U64.t)
  : Lemma (requires rctx ph ms g0 cs /\ ninert ms cs y)
          (ensures P.forward_normal (tl ph) ms cs y == cs)
  = if not (Seq.mem y (minor_objects ms)) || cs.P.fwd y <> 0UL then ()
    else begin
      let wz = minor_wosize ms y in
      if wz = 0 then ()
      else begin
        inv_of ph ms g0 cs;
        NG.promote_fail_nofit ph ms cs.P.major cs.P.st y wz
      end
    end
#pop-options

/// **An inert address's forwarding does nothing.**
#push-options "--z3rlimit 40"
let one_noop (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (x: U64.t)
  : Lemma (requires rctx ph ms g0 cs /\ inert ms cs x)
          (ensures P.forward_one (tl ph) ms cs x == cs)
  = if cs.P.fwd x <> 0UL then ()
    else if is_infix_in_minor ms x then begin
      let p = infix_parent ms x in
      if cs.P.fwd p = 0UL then normal_noop ph ms g0 cs p
    end
    else normal_noop ph ms g0 cs x
#pop-options

/// **After forwarding an address, it is inert.**
#push-options "--z3rlimit 40"
let one_after (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (x: U64.t)
  : Lemma (requires rctx ph ms g0 cs)
          (ensures inert ms (P.forward_one (tl ph) ms cs x) x)
  = if cs.P.fwd x <> 0UL then ()
    else if is_infix_in_minor ms x then begin
      let p = infix_parent ms x in
      normal_cases ph ms g0 cs p
    end
    else normal_cases ph ms g0 cs x
#pop-options

/// A forwarding entry stays.
#push-options "--z3rlimit 40"
let fwd_keep (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y m: U64.t)
  : Lemma (requires rctx ph ms g0 cs /\ cs.P.fwd m <> 0UL)
          (ensures (P.forward_one (tl ph) ms cs y).P.fwd m == cs.P.fwd m)
  = if cs.P.fwd y <> 0UL then ()
    else if is_infix_in_minor ms y then begin
      let q = infix_parent ms y in
      PL.forward_normal_keeps (tl ph) ms g0 cs q
    end
    else PL.forward_normal_keeps (tl ph) ms g0 cs y
#pop-options

/// `nofit` stays.
#push-options "--z3rlimit 40"
let normal_nofit (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y: U64.t) (w: nat)
  : Lemma (requires rctx ph ms g0 cs /\ NG.nofit cs.P.major w)
          (ensures NG.nofit (P.forward_normal (tl ph) ms cs y).P.major w)
  = if not (Seq.mem y (minor_objects ms)) || cs.P.fwd y <> 0UL then ()
    else begin
      let wz = minor_wosize ms y in
      if wz = 0 then ()
      else begin
        inv_of ph ms g0 cs;
        NG.step_nofit ph ms cs.P.major cs.P.st y wz w
      end
    end
#pop-options

let nofit_keep (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y: U64.t) (w: nat)
  : Lemma (requires rctx ph ms g0 cs /\ NG.nofit cs.P.major w)
          (ensures NG.nofit (P.forward_one (tl ph) ms cs y).P.major w)
  = if cs.P.fwd y <> 0UL then ()
    else if is_infix_in_minor ms y then normal_nofit ph ms g0 cs (infix_parent ms y) w
    else normal_nofit ph ms g0 cs y w

/// A block not forwarded and `ninert` stays not forwarded.
#push-options "--z3rlimit 40"
let fwd0_keep (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y p: U64.t)
  : Lemma (requires rctx ph ms g0 cs /\ ninert ms cs p /\ cs.P.fwd p == 0UL /\ ~(is_infix_in_minor ms p))
          (ensures (P.forward_one (tl ph) ms cs y).P.fwd p == 0UL)
  = if cs.P.fwd y <> 0UL then ()
    else if is_infix_in_minor ms y then begin
      let q = infix_parent ms y in
      if q = p then normal_noop ph ms g0 cs p
      else PL.forward_normal_keeps (tl ph) ms g0 cs q
    end
    else if y = p then normal_noop ph ms g0 cs p
    else PL.forward_normal_keeps (tl ph) ms g0 cs y
#pop-options

/// `ninert` stays.
let ninert_keep (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y z: U64.t)
  : Lemma (requires rctx ph ms g0 cs /\ ninert ms cs z)
          (ensures ninert ms (P.forward_one (tl ph) ms cs y) z)
  = if cs.P.fwd z <> 0UL then fwd_keep ph ms g0 cs y z
    else if Seq.mem z (minor_objects ms) && minor_wosize ms z <> 0 then
      nofit_keep ph ms g0 cs y (minor_wosize ms z)

/// **An inert address stays inert.**
#push-options "--z3rlimit 40"
let persist (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y x: U64.t)
  : Lemma (requires rctx ph ms g0 cs /\ inert ms cs x)
          (ensures inert ms (P.forward_one (tl ph) ms cs y) x)
  = if cs.P.fwd x <> 0UL then fwd_keep ph ms g0 cs y x
    else if is_infix_in_minor ms x then begin
      let p = infix_parent ms x in
      PL.parent_facts ms x;
      if cs.P.fwd p = 0UL then begin
        fwd0_keep ph ms g0 cs y p;
        ninert_keep ph ms g0 cs y p
      end
      else fwd_keep ph ms g0 cs y p
    end
    else ninert_keep ph ms g0 cs y x
#pop-options

/// The step keeps the context.
let ctx_step (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs: P.gstate U64.t) (y: U64.t)
  : Lemma (requires rctx ph ms g0 cs) (ensures rctx ph ms g0 (P.forward_one (tl ph) ms cs y))
  = PL.forward_one_keeps (tl ph) ms g0 cs y

/// ---------------------------------------------------------------------------
/// The roots loop
/// ---------------------------------------------------------------------------

/// The loop over `s`, from the start.
let frs (ph: T.phase U64.t) (ms: minor_state) (cs0: P.gstate U64.t) (s: Seq.seq U64.t) : GTot (P.gstate U64.t) =
  P.forward_roots (tl ph) ms cs0 s 0

/// One more root.
#push-options "--fuel 2 --z3rlimit 40"
let rec fr_snoc (ph: T.phase U64.t) (ms: minor_state) (cs: P.gstate U64.t) (s: Seq.seq U64.t) (x: U64.t) (i: nat)
  : Lemma (requires i <= Seq.length s)
          (ensures P.forward_roots (tl ph) ms cs (Seq.snoc s x) i ==
                   P.forward_one (tl ph) ms (P.forward_roots (tl ph) ms cs s i) x)
          (decreases (Seq.length s - i))
  = if i = Seq.length s then ()
    else begin
      assert (Seq.index (Seq.snoc s x) i == Seq.index s i);
      fr_snoc ph ms (P.forward_one (tl ph) ms cs (Seq.index s i)) s x (i + 1)
    end

let fr_nil (ph: T.phase U64.t) (ms: minor_state) (cs: P.gstate U64.t)
  : Lemma (frs ph ms cs Seq.empty == cs)
  = ()
#pop-options

/// `s` is `t` with repeats of earlier roots inserted.  (The sequences are
/// given as refinements, so a derivation can be built for any sequence equal
/// to the one constructed.)
noeq type rep : Seq.seq U64.t -> Seq.seq U64.t -> Type =
  | RNil : s: Seq.seq U64.t{Seq.length s == 0} -> t: Seq.seq U64.t{Seq.length t == 0} -> rep s t
  | RKeep : #s: Seq.seq U64.t -> #t: Seq.seq U64.t -> r: rep s t -> x: U64.t ->
            s': Seq.seq U64.t{s' == Seq.snoc s x} -> t': Seq.seq U64.t{t' == Seq.snoc t x} -> rep s' t'
  | RDrop : #s: Seq.seq U64.t -> #t: Seq.seq U64.t -> r: rep s t -> x: U64.t{Seq.mem x s} ->
            s': Seq.seq U64.t{s' == Seq.snoc s x} -> rep s' t

let mem_snoc (s: Seq.seq U64.t) (x z: U64.t) : Lemma (Seq.mem z (Seq.snoc s x) <==> Seq.mem z s \/ z == x)
  = Seq.lemma_mem_append s (Seq.create 1 x);
    GC.Spec.Top.PagesLive.mem_one z x

/// **The loop over `s` is the loop over `t`**, and every root of `s` is
/// inert at its end.
#push-options "--z3rlimit 40"
let rec rep_run (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (cs0: P.gstate U64.t)
                (s t: Seq.seq U64.t) (r: rep s t)
  : Lemma (requires rctx ph ms g0 cs0)
          (ensures frs ph ms cs0 s == frs ph ms cs0 t /\ rctx ph ms g0 (frs ph ms cs0 s) /\
                   (forall (z: U64.t). Seq.mem z s ==> inert ms (frs ph ms cs0 s) z))
          (decreases r)
  = match r with
    | RNil _ _ ->
      Seq.lemma_empty s; Seq.lemma_empty t;
      fr_nil ph ms cs0;
      FStar.Classical.forall_intro GC.Spec.Top.PagesLive.mem_empty
    | RKeep #s1 #t1 r' x _ _ ->
      rep_run ph ms g0 cs0 s1 t1 r';
      let c = frs ph ms cs0 s1 in
      fr_snoc ph ms cs0 s1 x 0;
      fr_snoc ph ms cs0 t1 x 0;
      ctx_step ph ms g0 c x;
      let one (z: U64.t) : Lemma (requires Seq.mem z (Seq.snoc s1 x)) (ensures inert ms (P.forward_one (tl ph) ms c x) z)
        = mem_snoc s1 x z;
          if z = x then one_after ph ms g0 c x else persist ph ms g0 c x z in
      FStar.Classical.forall_intro (FStar.Classical.move_requires one)
    | RDrop #s1 #t1 r' x _ ->
      rep_run ph ms g0 cs0 s1 t1 r';
      let c = frs ph ms cs0 s1 in
      fr_snoc ph ms cs0 s1 x 0;
      one_noop ph ms g0 c x;
      let one (z: U64.t) : Lemma (requires Seq.mem z (Seq.snoc s1 x)) (ensures inert ms c z)
        = mem_snoc s1 x z in
      FStar.Classical.forall_intro (FStar.Classical.move_requires one)
#pop-options

/// The members of `t` are members of `s`.
let rec rep_mem (s t: Seq.seq U64.t) (r: rep s t) (z: U64.t)
  : Lemma (requires Seq.mem z t) (ensures Seq.mem z s) (decreases r)
  = match r with
    | RNil _ _ -> Seq.lemma_empty t; GC.Spec.Top.PagesLive.mem_empty z
    | RKeep #s1 #t1 r' x _ _ -> mem_snoc s1 x z; mem_snoc t1 x z; if z <> x then rep_mem s1 t1 r' z
    | RDrop #s1 #t1 r' x _ -> mem_snoc s1 x z; rep_mem s1 t1 r' z

/// The loop's start.
let start_ctx (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (fp: U64.t)
  : Lemma (requires PL.ctx (tl ph) ms g0 /\ FW.fshape ph g0 fp)
          (ensures rctx ph ms g0 ({ P.major = g0; P.st = fp; P.fwd = GP.empty_forwarding; P.queue = Seq.empty }))
  = assert (PL.olds (tl ph) g0 g0)

/// **The promotion on `s` is the promotion on `t`.**
let promote_rep (ph: T.phase U64.t) (ms: minor_state) (g0: heap) (fp: U64.t) (s t: Seq.seq U64.t) (r: rep s t)
  : Lemma (requires PL.ctx (tl ph) ms g0 /\ FW.fshape ph g0 fp)
          (ensures P.promote (tl ph) ms g0 fp s == P.promote (tl ph) ms g0 fp t)
  = let cs0 : P.gstate U64.t = { P.major = g0; P.st = fp; P.fwd = GP.empty_forwarding; P.queue = Seq.empty } in
    start_ctx ph ms g0 fp;
    rep_run ph ms g0 cs0 s t r

/// A sequence is itself with no repeat inserted.
let rec rep_refl (s: Seq.seq U64.t) : GTot (rep s s) (decreases Seq.length s) =
  if Seq.length s = 0 then RNil s s
  else begin
    let n = Seq.length s - 1 in
    let s1 = Seq.slice s 0 n in
    Seq.lemma_eq_elim s (Seq.snoc s1 (Seq.index s n));
    RKeep (rep_refl s1) (Seq.index s n) s s
  end
