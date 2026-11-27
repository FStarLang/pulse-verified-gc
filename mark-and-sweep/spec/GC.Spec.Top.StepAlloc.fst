/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StepAlloc - allocation and its Fill
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 7): `EAlloc`, clause (2).  The allocator hands
/// out a block `o` on free words, coloured by `colour_at`, and keeps every
/// block in use; the barrier's Fill writes `o`'s fields and nothing else
/// (`fill_other`); allocation status is read from the headers (G48), so it
/// is the allocator's after the Fill.  Then:
///   - only `o` is new: a reachable object is reachable before, or `o`
///     (every value of the Fill is one the program may hold);
///   - `o` is kept: in use, and allocated in the cycle;
///   - the colours: `o` is black while marking, and black or white by the
///     sweep's progress while sweeping, so the invariant of each phase holds
///     with `o` in `allocd`;
///   - the allocator's invariant after the Fill, from the post, with values
///     the program may store (`sound_value`: their targets are kept).

module GC.Spec.Top.StepAlloc

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.StepFacts
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator's guarantee, sealed
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let apost (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (h': c.t) (st': c.a.state) (o: nat) (m': mheap)
  : prop =
  alloc_post c.r c.a x.ph x.w.cmaj x.ast sz tag h' st' (Ok o) (mj x) m'

let al_basic (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (h': c.t) (st': c.a.state) (o: nat) (m': mheap)
  : Lemma (requires apost x sz tag h' st' o m' /\ well_formed (mj x))
          (ensures m'.size == (mj x).size /\ is_block m' o /\
                   m'.hd o == Some ({ wz = sz; tag = tag; col = colour_at c.k x.ph o }) /\
                   well_formed m' /\ c.a.room x.ph x.ast x.w.cmaj sz == true /\ in_use_c x o == false)
  = reveal_opaque (`%apost) (apost #c);
    assert (covers m' o o);
    assert (free_word c.a x.ast x.w.cmaj (mj x) o);
    if in_use_c x o then begin
      assert (covers (mj x) o o);
      C.forall_intro (C.move_requires (cover_unique (mj x) o o))
    end

let al_iu (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (h': c.t) (st': c.a.state) (o: nat) (m': mheap)
    (y: nat)
  : Lemma (requires apost x sz tag h' st' o m')
          (ensures in_use c.a st' h' m' y == (in_use_c x y || y = o))
  = reveal_opaque (`%apost) (apost #c)

let al_same (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (h': c.t) (st': c.a.state) (o: nat) (m': mheap)
    (y: nat)
  : Lemma (requires apost x sz tag h' st' o m' /\ in_use_c x y) (ensures same_block (mj x) m' y)
  = reveal_opaque (`%apost) (apost #c)

let al_inv (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (h': c.t) (st': c.a.state) (o: nat) (m': mheap)
    (vs: list value) (h'': c.t)
  : Lemma (requires apost x sz tag h' st' o m' /\ L.length vs == sz /\
                    (scannable tag ==> (forall (v: value). L.memP v vs ==> sound_value c.a x.ph x.ast x.w.cmaj (mj x) v)) /\
                    c.r.repr (fill m' o vs) h'')
          (ensures c.a.inv x.ph h'' st')
  = reveal_opaque (`%apost) (apost #c)

/// ---------------------------------------------------------------------------
/// The step's context
/// ---------------------------------------------------------------------------

let anext (#c: comps) (x x': config c) (h'': c.t) (st': c.a.state) (o: nat) (rem': list slot) : prop =
  x'.ph == x.ph /\ x'.ast == st' /\ x'.w.cmaj == h'' /\ x'.w.crem == rem' /\ x'.w.cyng == x.w.cyng /\
  x'.w.croots == VPtr (Major o) :: x.w.croots /\ x'.snap == x.snap /\ x'.ms == x.ms /\
  (forall (p: nat). x'.allocd p <==> x.allocd p \/ p == o)

/// Everything the step lemma knows.
let aok (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) : prop =
  rinv x /\ mutator_ok x (EAlloc sz tag vs) /\ apost x sz tag h' st' o m' /\ anext x x' h'' st' o rem' /\
  (forall (y: nat). c.a.free st' h'' y == c.a.free st' h' y) /\
  (forall (sl: slot). L.memP sl (vw x).rem ==> L.memP sl rem') /\
  (forall (i: nat). i < L.length vs /\ young_slot m' o i (L.index vs i) ==> L.memP (o, i) rem')

let wnext (#c: comps) (x: config c) (vs: list value) (o: nat) (m': mheap) (rem': list slot) : GTot world =
  { maj = fill m' o vs; yng = (vw x).yng; roots = VPtr (Major o) :: (vw x).roots; rem = rem' }

let a_basic (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem')
          (ensures (let m2 = fill m' o vs in
                    L.length vs == sz /\ tag <> infix_tag /\ fill_ok (vw x) tag vs /\
                    well_formed (mj x) /\ m2.size == (mj x).size /\ is_block m2 o /\
                    m2.hd o == Some ({ wz = sz; tag = tag; col = colour_at c.k x.ph o }) /\
                    well_formed m2 /\ unique_cover m2 /\ unique_cover m' /\
                    c.a.room x.ph x.ast x.w.cmaj sz == true /\ in_use_c x o == false))
  = reveal_opaque (`%r_heap) (r_heap #c);
    assert (well_formed (mj x));
    assert (L.length vs == sz /\ tag <> infix_tag /\ fill_ok (vw x) tag vs);
    al_basic x sz tag h' st' o m';
    fill_blocks m' o vs o;
    fill_wf m' o vs;
    unique_wf m'

/// In use after: in use before, or `o`.
let a_iu (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (y: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem')
          (ensures iu x' (fill m' o vs) y == (in_use_c x y || y = o))
  = fill_hd m' o vs;
    al_iu x sz tag h' st' o m' y

/// A block in use before is kept, header included.
let a_keep (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (y: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ in_use_c x y)
          (ensures y <> o /\ iu x' (fill m' o vs) y /\ keeps (mj x) (fill m' o vs) y /\
                   (fill m' o vs).hd y == (mj x).hd y /\ keepsy (mj x) (fill m' o vs) y)
  = a_basic x x' sz tag vs h' st' o m' h'' rem';
    a_iu x x' sz tag vs h' st' o m' h'' rem' y;
    al_same x sz tag h' st' o m' y;
    fill_hd m' o vs;
    let f (i: nat) : Lemma (i < wz_of (mj x) y ==> field (fill m' o vs) y i == field (mj x) y i)
      = if i < wz_of (mj x) y then fill_other m' o vs y i in
    C.forall_intro f

/// The new block's fields are the Fill's values, ones the program may hold.
let a_new_field (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (i: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ ptr_field (fill m' o vs) o i)
          (ensures i < sz /\ field (fill m' o vs) o i == L.index vs i /\ value_ok (vw x) (L.index vs i) /\
                   scannable tag)
  = a_basic x x' sz tag vs h' st' o m' h'' rem';
    fill_field m' o vs i

/// ---------------------------------------------------------------------------
/// Reachability
/// ---------------------------------------------------------------------------

let s_new (w: world) (o: nat) (z: nat) : prop = reachable w z \/ z == o

/// A reachable target in the old world resolves to it after.
let a_target (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (a t: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ resolve (mj x) a == Some t /\ reachable (vw x) t)
          (ensures resolve (fill m' o vs) a == Some t)
  = reach_kept x (vw x) t;
    a_keep x x' sz tag vs h' st' o m' h'' rem' t;
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    resolve_keepy (mj x) (fill m' o vs) a t

/// A value the program may hold resolves after to its target.
let a_value (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (a z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ value_ok (vw x) (VPtr (Major a)) /\
                    resolve (fill m' o vs) a == Some z)
          (ensures reachable (vw x) z)
  = eliminate exists (t: nat). resolve (mj x) a == Some t /\ reachable (vw x) t
    with a_target x x' sz tag vs h' st' o m' h'' rem' a t

/// A major pointer that resolves to a reachable block in the old world.
let a_held (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (a z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ Some? (resolve (mj x) a) /\
                    reachable (vw x) (Some?.v (resolve (mj x) a)) /\ resolve (fill m' o vs) a == Some z)
          (ensures reachable (vw x) z)
  = a_target x x' sz tag vs h' st' o m' h'' rem' a (Some?.v (resolve (mj x) a))

let a_outside (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ outside_ref (wnext x vs o m' rem') z)
          (ensures s_new (vw x) o z)
  = let w = vw x in
    let w' = wnext x vs o m' rem' in
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    if FStar.IndefiniteDescription.strong_excluded_middle (root_ref w' z) then begin
      eliminate exists (a: nat). L.memP (VPtr (Major a)) w'.roots /\ resolve w'.maj a == Some z
      with begin
        if a = o then ()
        else begin
          res_root w (VPtr (Major a));
          reach_root w a (Some?.v (resolve w.maj a));
          a_held x x' sz tag vs h' st' o m' h'' rem' a z
        end
      end
    end else begin
      eliminate exists (y i a: nat). ptr_field w'.yng y i /\ field w'.yng y i == VPtr (Major a) /\
                                     resolve w'.maj a == Some z
      with begin
        res_yng w y i;
        reach_young w y i a (Some?.v (resolve w.maj a));
        a_held x x' sz tag vs h' st' o m' h'' rem' a z
      end
    end

let a_edge (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (y z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ s_new (vw x) o y /\ major_edge (fill m' o vs) y z)
          (ensures s_new (vw x) o z)
  = let w = vw x in
    let m2 = fill m' o vs in
    eliminate exists (i a: nat). ptr_field m2 y i /\ field m2 y i == VPtr (Major a) /\ resolve m2 a == Some z
    with begin
      if y = o then begin
        a_new_field x x' sz tag vs h' st' o m' h'' rem' i;
        a_value x x' sz tag vs h' st' o m' h'' rem' a z
      end else begin
        reach_kept x w y;
        a_keep x x' sz tag vs h' st' o m' h'' rem' y;
        assert (ptr_field w.maj y i /\ field w.maj y i == VPtr (Major a));
        res_maj w y i;
        reach_field w y i a (Some?.v (resolve w.maj a));
        a_held x x' sz tag vs h' st' o m' h'' rem' a z
      end
    end

let a_reach (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ reachable (wnext x vs o m' rem') z)
          (ensures s_new (vw x) o z)
  = C.forall_intro (C.move_requires (a_outside x x' sz tag vs h' st' o m' h'' rem'));
    C.forall_intro_2 (fun y z -> C.move_requires (a_edge x x' sz tag vs h' st' o m' h'' rem' y) z);
    reachable_within (wnext x vs o m' rem') (s_new (vw x) o) z

/// ---------------------------------------------------------------------------
/// The invariant after the step
/// ---------------------------------------------------------------------------

let a_kept_new (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ s_new (vw x) o z)
          (ensures kept_w x' (wnext x vs o m' rem') z)
  = a_iu x x' sz tag vs h' st' o m' h'' rem' z;
    if FStar.IndefiniteDescription.strong_excluded_middle (reachable (vw x) z) then reach_kept x (vw x) z

let a_r_reach (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t) (st': c.a.state)
    (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem')
          (ensures r_reach x' (wnext x vs o m' rem') /\ rback_w x (wnext x vs o m' rem'))
  = C.forall_intro (C.move_requires (a_reach x x' sz tag vs h' st' o m' h'' rem'));
    C.forall_intro (C.move_requires (a_kept_new x x' sz tag vs h' st' o m' h'' rem'));
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    reveal_opaque (`%r_reach) (r_reach #c);
    reveal_opaque (`%rback_w) (rback_w #c)

/// A value of the old world that resolves (to a reachable block, if major).
let a_resolves (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (v: value)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ resolves (vw x) v /\
                    (match v with VPtr (Major a) -> reachable (vw x) (Some?.v (resolve (mj x) a)) | _ -> True))
          (ensures resolves (wnext x vs o m' rem') v)
  = match v with
    | VPtr (Major a) -> a_target x x' sz tag vs h' st' o m' h'' rem' a (Some?.v (resolve (mj x) a))
    | _ -> ()

let a_res_root (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (v: value)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ L.memP v (wnext x vs o m' rem').roots)
          (ensures resolves (wnext x vs o m' rem') v)
  = let w = vw x in
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    if v = VPtr (Major o) then ()
    else begin
      res_root w v;
      (match v with VPtr (Major a) -> reach_root w a (Some?.v (resolve w.maj a)) | _ -> ());
      a_resolves x x' sz tag vs h' st' o m' h'' rem' v
    end

let a_res_value (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (v: value)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ value_ok (vw x) v)
          (ensures resolves (wnext x vs o m' rem') v)
  = match v with
    | VPtr (Major a) ->
      eliminate exists (t: nat). resolve (mj x) a == Some t /\ reachable (vw x) t
      with a_target x x' sz tag vs h' st' o m' h'' rem' a t
    | _ -> ()

let a_res_maj (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z i: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ reachable (wnext x vs o m' rem') z /\
                    ptr_field (fill m' o vs) z i)
          (ensures resolves (wnext x vs o m' rem') (field (fill m' o vs) z i))
  = let w = vw x in
    a_reach x x' sz tag vs h' st' o m' h'' rem' z;
    if z = o then begin
      a_new_field x x' sz tag vs h' st' o m' h'' rem' i;
      a_res_value x x' sz tag vs h' st' o m' h'' rem' (L.index vs i)
    end else begin
      reach_kept x w z;
      a_keep x x' sz tag vs h' st' o m' h'' rem' z;
      assert (ptr_field w.maj z i /\ field (fill m' o vs) z i == field w.maj z i);
      res_maj w z i;
      (match field w.maj z i with VPtr (Major a) -> reach_field w z i a (Some?.v (resolve w.maj a)) | _ -> ());
      a_resolves x x' sz tag vs h' st' o m' h'' rem' (field w.maj z i)
    end

let a_res_yng (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (y i: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ ptr_field (vw x).yng y i)
          (ensures resolves (wnext x vs o m' rem') (field (vw x).yng y i))
  = let w = vw x in
    res_yng w y i;
    (match field w.yng y i with VPtr (Major a) -> reach_young w y i a (Some?.v (resolve w.maj a)) | _ -> ());
    a_resolves x x' sz tag vs h' st' o m' h'' rem' (field w.yng y i)

let a_r_res (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem') (ensures r_res (wnext x vs o m' rem'))
  = C.forall_intro (C.move_requires (a_res_root x x' sz tag vs h' st' o m' h'' rem'));
    C.forall_intro_2 (fun z i -> C.move_requires (a_res_maj x x' sz tag vs h' st' o m' h'' rem' z) i);
    C.forall_intro_2 (fun y i -> C.move_requires (a_res_yng x x' sz tag vs h' st' o m' h'' rem' y) i);
    reveal_opaque (`%r_res) r_res

let a_young1 (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z i b: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\
                    live_target c.a x'.ph x'.ast x'.w.cmaj (fill m' o vs) z /\
                    ptr_field (fill m' o vs) z i /\ field (fill m' o vs) z i == VPtr (Young b))
          (ensures Some? (resolve (vw x).yng b) /\ L.memP (z, i) rem')
  = let w = vw x in
    a_iu x x' sz tag vs h' st' o m' h'' rem' z;
    if z = o then begin
      a_new_field x x' sz tag vs h' st' o m' h'' rem' i;
      a_basic x x' sz tag vs h' st' o m' h'' rem';
      assert (young_slot m' o i (L.index vs i))
    end else begin
      a_keep x x' sz tag vs h' st' o m' h'' rem' z;
      reveal_opaque (`%r_young) (r_young #c);
      assert (live_target c.a x.ph x.ast x.w.cmaj w.maj z);
      assert (ptr_field w.maj z i /\ field w.maj z i == VPtr (Young b))
    end

let a_r_young (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem') (ensures r_young x' (wnext x vs o m' rem'))
  = C.forall_intro_3 (fun z i b -> C.move_requires (a_young1 x x' sz tag vs h' st' o m' h'' rem' z i) b);
    reveal_opaque (`%r_young) (r_young #c)

/// The allocator's invariant after the Fill.
let a_sound (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (v: value)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ scannable tag /\ L.memP v vs)
          (ensures sound_value c.a x.ph x.ast x.w.cmaj (mj x) v)
  = let w = vw x in
    mem_index v vs;
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    assert (value_ok w v);
    match v with
    | VPtr (Major a) ->
      eliminate exists (t: nat). resolve w.maj a == Some t /\ reachable w t
      with begin reach_kept x w t; kept_live_target x w t end
    | _ -> ()

let a_r_heap (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ c.r.repr (fill m' o vs) h'')
          (ensures r_heap x' (wnext x vs o m' rem'))
  = a_basic x x' sz tag vs h' st' o m' h'' rem';
    C.forall_intro (C.move_requires (a_sound x x' sz tag vs h' st' o m' h'' rem'));
    al_inv x sz tag h' st' o m' vs h'';
    reveal_opaque (`%r_heap) (r_heap #c)

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

let a_col_idle (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ Idle? x.ph /\ iu x' (fill m' o vs) z)
          (ensures not (dark (col_of (fill m' o vs) z)))
  = a_iu x x' sz tag vs h' st' o m' h'' rem' z;
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    if z <> o then begin
      a_keep x x' sz tag vs h' st' o m' h'' rem' z;
      reveal_opaque (`%r_col) (r_col #c)
    end

let a_col_sweep (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (p: c.k.progress) (z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ x.ph == Sweeping p /\ iu x' (fill m' o vs) z)
          (ensures col_sweep x' p (fill m' o vs) z /\ (c.k.unswept p z == false ==> live x' z) /\ iu x' (fill m' o vs) z)
  = a_iu x x' sz tag vs h' st' o m' h'' rem' z;
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    if z <> o then begin
      a_keep x x' sz tag vs h' st' o m' h'' rem' z;
      reveal_opaque (`%r_col) (r_col #c);
      reveal_opaque (`%r_live) (r_live #c);
      assert (col_sweep x p (mj x) z)
    end

let a_live (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ ~(Idle? x.ph) /\ live x' z)
          (ensures iu x' (fill m' o vs) z /\ (z <> o ==> live x z /\ in_use_c x z))
  = a_iu x x' sz tag vs h' st' o m' h'' rem' z;
    if z <> o then reveal_opaque (`%r_live) (r_live #c)

/// While marking: the tricolour invariant over blocks in use, and closed.
let a_tri (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ Marking? x.ph)
          (ensures tri_iu x' (fill m' o vs) /\ scan_ok x' (fill m' o vs))
  = let m = mj x in
    let m2 = fill m' o vs in
    reveal_opaque (`%r_col) (r_col #c);
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    C.forall_intro (C.move_requires (a_live x x' sz tag vs h' st' o m' h'' rem'));
    let c2 (z: nat) : Lemma (iu x' m2 z /\ dark (col_of m2 z) ==> live x' z)
      = a_iu x x' sz tag vs h' st' o m' h'' rem' z;
        if z <> o && in_use_c x z then a_keep x x' sz tag vs h' st' o m' h'' rem' z in
    C.forall_intro c2;
    let c3 (z: nat) : Lemma (x'.allocd z ==> col_of m2 z == Black)
      = if z <> o && x.allocd z then a_live x x' sz tag vs h' st' o m' h'' rem' z;
        if z <> o && x.allocd z then a_keep x x' sz tag vs h' st' o m' h'' rem' z in
    C.forall_intro c3;
    let lv (y: nat) : Lemma (union x.snap x.allocd y ==> keepsy m m2 y /\ union x'.snap x'.allocd y)
      = if FStar.IndefiniteDescription.strong_excluded_middle (union x.snap x.allocd y) then begin
          reveal_opaque (`%r_live) (r_live #c);
          a_keep x x' sz tag vs h' st' o m' h'' rem' y
        end in
    C.forall_intro lv;
    scan_keepy x x' m m2;
    let c4 (z: nat) : Lemma (x'.snap z /\ col_of m2 z == White ==> live_reached m2 (scan_of x') (union x'.snap x'.allocd) z)
      = if FStar.IndefiniteDescription.strong_excluded_middle (x'.snap z /\ col_of m2 z == White) then begin
          reveal_opaque (`%r_live) (r_live #c);
          a_keep x x' sz tag vs h' st' o m' h'' rem' z;
          lpath_keepy m m2 (scan_of x) (union x.snap x.allocd) (union x'.snap x'.allocd) z
        end in
    C.forall_intro c4

let a_closed1 (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z i a: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ Marking? x.ph /\ union x'.snap x'.allocd z /\
                    ptr_field (fill m' o vs) z i /\ field (fill m' o vs) z i == VPtr (Major a))
          (ensures exists (t: nat). resolve (fill m' o vs) a == Some t /\ union x'.snap x'.allocd t)
  = let w = vw x in
    let m = mj x in
    if z = o then begin
      a_new_field x x' sz tag vs h' st' o m' h'' rem' i;
      eliminate exists (t: nat). resolve m a == Some t /\ reachable w t
      with begin
        a_target x x' sz tag vs h' st' o m' h'' rem' a t;
        reach_kept x w t
      end
    end else begin
      assert (union x.snap x.allocd z);
      live_iu x z;
      a_keep x x' sz tag vs h' st' o m' h'' rem' z;
      assert (ptr_field m z i /\ field m z i == VPtr (Major a));
      closed_step x z i a;
      eliminate exists (t: nat). resolve m a == Some t /\ union x.snap x.allocd t /\ in_use_c x t
      with begin
        a_keep x x' sz tag vs h' st' o m' h'' rem' t;
        a_basic x x' sz tag vs h' st' o m' h'' rem';
        resolve_keepy m (fill m' o vs) a t
      end
    end

let a_r_col (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem')
          (ensures r_col x' (wnext x vs o m' rem') /\ r_live x' (wnext x vs o m' rem'))
  = reveal_opaque (`%r_col) (r_col #c);
    reveal_opaque (`%r_live) (r_live #c);
    match x.ph with
    | Idle -> C.forall_intro (C.move_requires (a_col_idle x x' sz tag vs h' st' o m' h'' rem'))
    | Marking ->
      a_tri x x' sz tag vs h' st' o m' h'' rem';
      C.forall_intro_3 (fun z i a -> C.move_requires (a_closed1 x x' sz tag vs h' st' o m' h'' rem' z i) a);
      C.forall_intro (C.move_requires (a_live x x' sz tag vs h' st' o m' h'' rem'))
    | Sweeping p ->
      C.forall_intro (C.move_requires (a_col_sweep x x' sz tag vs h' st' o m' h'' rem' p));
      C.forall_intro (C.move_requires (a_live x x' sz tag vs h' st' o m' h'' rem'))

/// ---------------------------------------------------------------------------
/// The conclusions
/// ---------------------------------------------------------------------------

let a_kept (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ kept x z)
          (ensures iu x' (fill m' o vs) z == true /\ contents_w x (EAlloc sz tag vs) (wnext x vs o m' rem') z)
  = a_keep x x' sz tag vs h' st' o m' h'' rem' z

let a_cs_keep (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem')
          (ensures cs_keep x (EAlloc sz tag vs) x' (wnext x vs o m' rem'))
  = C.forall_intro (C.move_requires (a_kept x x' sz tag vs h' st' o m' h'' rem'));
    reveal_opaque (`%cs_keep) (cs_keep #c)

let a_word (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (n: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ n < (mj x).size /\ in_use_word_c x n)
          (ensures ~(free_w x' (wnext x vs o m' rem') n))
  = a_basic x x' sz tag vs h' st' o m' h'' rem';
    eliminate exists (z: nat). covers (mj x) z n /\ in_use_c x z
    with begin
      a_keep x x' sz tag vs h' st' o m' h'' rem' z;
      in_use_not_free c.a x'.ast x'.w.cmaj (fill m' o vs) z n
    end

let a_cs_words (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem')
          (ensures cs_words x (EAlloc sz tag vs) x' (wnext x vs o m' rem'))
  = C.forall_intro (C.move_requires (a_word x x' sz tag vs h' st' o m' h'' rem'));
    reveal_opaque (`%cs_words) (cs_words #c)

let a_measure1 (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (z: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ Marking? x.ph)
          (ensures (white_live (fill m' o vs) (live x') z ==> white_live (mj x) (live x') z) /\
                   (grey_live (fill m' o vs) (live x') z ==> grey_live (mj x) (live x') z))
  = a_basic x x' sz tag vs h' st' o m' h'' rem';
    if z <> o && FStar.IndefiniteDescription.strong_excluded_middle (live x' z) then begin
      a_live x x' sz tag vs h' st' o m' h'' rem' z;
      a_keep x x' sz tag vs h' st' o m' h'' rem' z
    end

let a_cs_mark (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem')
          (ensures cs_mark x (EAlloc sz tag vs) x' (wnext x vs o m' rem'))
  = if Marking? x.ph then begin
      C.forall_intro (C.move_requires (a_measure1 x x' sz tag vs h' st' o m' h'' rem'));
      a_basic x x' sz tag vs h' st' o m' h'' rem';
      reveal_opaque (`%r_col) (r_col #c);
      reveal_opaque (`%r_live) (r_live #c);
      (match scan_of x with Some (s, _) -> a_keep x x' sz tag vs h' st' o m' h'' rem' s | None -> ());
      fleft_keepy x (mj x) (fill m' o vs)
    end;
    reveal_opaque (`%cs_mark) (cs_mark #c)

let a_cs_alloc (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem' /\ c.a.alloc x.ph x.w.cmaj x.ast sz tag == (h', st', Ok o))
          (ensures cs_alloc x (EAlloc sz tag vs) x' (wnext x vs o m' rem'))
  = let w' = wnext x vs o m' rem' in
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    C.forall_intro (a_iu x x' sz tag vs h' st' o m' h'' rem');
    let fi (i: nat) : Lemma (i < sz /\ i < L.length vs ==> field w'.maj o i == L.index vs i)
      = if i < L.length vs then fill_field m' o vs i in
    C.forall_intro fi;
    a_kept_new x x' sz tag vs h' st' o m' h'' rem' o;
    fill_hd m' o vs;
    assert (in_use_c x o == false /\ iu x' w'.maj o == true /\ kept_w x' w' o);
    assert (w'.maj.hd o == Some ({ wz = sz; tag = tag; col = colour_at c.k x.ph o }));
    assert (forall (y: nat). y <> o ==> (iu x' w'.maj y == in_use_c x y));
    assert (alloc_w x sz tag vs x' w');
    reveal_opaque (`%cs_alloc) (cs_alloc #c)

let a_cyc1 (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot) (y: nat)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem')
          (ensures (x'.allocd y ==> x.allocd y \/ in_use_c x y == false) /\
                   (iu x' (fill m' o vs) y == true /\ in_use_c x y == false ==> x'.allocd y) /\
                   (in_use_c x y == true ==> iu x' (fill m' o vs) y == true /\ wz_of (fill m' o vs) y == wz_of (mj x) y))
  = a_basic x x' sz tag vs h' st' o m' h'' rem';
    a_iu x x' sz tag vs h' st' o m' h'' rem' y;
    if in_use_c x y then a_keep x x' sz tag vs h' st' o m' h'' rem' y

let a_cyc (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires aok x x' sz tag vs h' st' o m' h'' rem') (ensures cs_cyc x x' (wnext x vs o m' rem'))
  = C.forall_intro (a_cyc1 x x' sz tag vs h' st' o m' h'' rem');
    a_basic x x' sz tag vs h' st' o m' h'' rem';
    reveal_opaque (`%cs_cyc) (cs_cyc #c)

/// **A successful allocation.**
let a_finish (#c: comps) (x x': config c) (sz: size_t) (tag: tag_t) (vs: list value) (h': c.t)
    (st': c.a.state) (o: nat) (m': mheap) (h'': c.t) (rem': list slot)
  : Lemma (requires faithful c.r /\ aok x x' sz tag vs h' st' o m' h'' rem' /\
                    c.a.alloc x.ph x.w.cmaj x.ast sz tag == (h', st', Ok o) /\
                    c.r.repr (fill m' o vs) h'' /\ views x' (wnext x vs o m' rem'))
          (ensures rinv x' /\ concl_step x (EAlloc sz tag vs) x' /\ rback x x' /\ cyc x x')
  = let e = EAlloc sz tag vs in
    let w' = wnext x vs o m' rem' in
    a_r_heap x x' sz tag vs h' st' o m' h'' rem';
    a_r_reach x x' sz tag vs h' st' o m' h'' rem';
    a_r_res x x' sz tag vs h' st' o m' h'' rem';
    a_r_young x x' sz tag vs h' st' o m' h'' rem';
    a_r_col x x' sz tag vs h' st' o m' h'' rem';
    a_cs_keep x x' sz tag vs h' st' o m' h'' rem';
    a_cs_alloc x x' sz tag vs h' st' o m' h'' rem';
    a_cs_words x x' sz tag vs h' st' o m' h'' rem';
    a_cs_mark x x' sz tag vs h' st' o m' h'' rem';
    assert (cs_old x e x');
    a_cyc x x' sz tag vs h' st' o m' h'' rem';
    step_out_intro x e x' w'

/// ---------------------------------------------------------------------------
/// EAlloc
/// ---------------------------------------------------------------------------

/// No room: nothing changes.
let noroom_step (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires faithful c.r /\ rinv x /\
                    (let (h', st', res) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
                     res == NoRoom /\ c.a.room x.ph x.ast x.w.cmaj sz == false))
          (ensures (let e = EAlloc sz tag vs in let x' = step c x e in
                    rinv x' /\ concl_step x e x' /\ rback x x' /\ cyc x x'))
  = let e = EAlloc sz tag vs in
    let x' = step c x e in
    assert (x' == x);
    let w = vw x in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    agree_refl w.maj;
    C.forall_intro (C.move_requires (same_keep1 x e x w));
    reveal_opaque (`%cs_keep) (cs_keep #c);
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    same_words x e x w;
    C.forall_intro (fun (o: nat) -> ag_white_live w.maj w.maj (live x) o);
    reveal_opaque (`%cs_mark) (cs_mark #c);
    reveal_opaque (`%rback_w) (rback_w #c);
    cyc_agree x x w;
    step_out_intro x e x w

#push-options "--z3rlimit 40"
let alloc_step (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x (EAlloc sz tag vs) /\ mutator_ok x (EAlloc sz tag vs))
          (ensures (let e = EAlloc sz tag vs in let x' = step c x e in
                    rinv x' /\ concl_step x e x' /\ rback x x' /\ cyc x x'))
  = let e = EAlloc sz tag vs in
    let x' = step c x e in
    let w = vw x in
    let m = w.maj in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    let (h', st', res) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
    assert (alloc_pre c.a x.ph x.w.cmaj x.ast tag m);
    let m' = FStar.IndefiniteDescription.indefinite_description_ghost mheap
               (fun m' -> c.r.repr m' h' /\ alloc_post c.r c.a x.ph x.w.cmaj x.ast sz tag h' st' res m m') in
    match res with
    | NoRoom -> noroom_step x sz tag vs
    | Ok o ->
      reveal_opaque (`%apost) (apost #c);
      assert (apost x sz tag h' st' o m');
      let (h'', rem') = c.b.binit h' x.w.crem o vs in
      assert (binit_m c.r c.b h' x.w.crem o vs m');
      assert (is_block m' o /\ L.length vs == wz_of m' o);
      assert (c.r.repr (fill m' o vs) h'');
      assert (free_hd_m c.a st' h' h'' m' (fill m' o vs));
      assert (forall (y: nat). c.a.free st' h'' y == c.a.free st' h' y);
      assert (anext x x' h'' st' o rem');
      assert (aok x x' sz tag vs h' st' o m' h'' rem');
      assert (views x' (wnext x vs o m' rem'));
      a_finish x x' sz tag vs h' st' o m' h'' rem'
#pop-options
