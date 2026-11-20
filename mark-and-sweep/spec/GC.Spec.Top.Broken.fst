/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Broken - broken components the specification rejects
/// ---------------------------------------------------------------------------
///
/// Strength of the specification: each component below is deliberately
/// wrong, and each lemma proves that it violates its contract (or, for the
/// mutator, its obligations), on a concrete heap.
///
///   | component                                          | rejected by                         |
///   |----------------------------------------------------|-------------------------------------|
///   | allocator handing out an object in use (`bad_inuse`) | `alloc_ok`: o's words were free   |
///   | allocator whose room is always false (`bad_noroom`)  | `nontrivial` (it meets `allocator_ok`) |
///   | sweep freeing a black object (`bad_black`)           | `sweep_ok`: black stays in use     |
///   | sweep re-sweeping swept memory (`bad_resweep`)       | `sweep_ok`: outside the region unchanged |
///   | mutator setting a root to a garbage object           | `mutator_ok` (`value_ok`); the     |
///   |                                                      | snapshot-based reading accepts it  |
///   | minor collection skipping a remembered slot          | `minor_ok`: exactly the live young |
///   | mark not greying old objects held by young ones      | `mark_ok`: outside_refs greyed     |
///   | minor collection always out of room (`bad_oor`)      | `minor_ok`: OutOfRoom justified    |
///   | barrier not remembering a Fill's young pointers      | `barrier_ok`                       |

module GC.Spec.Top.Broken

open GC.Spec.Top.Heap
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Toy
open GC.Spec.Top.ToyMark
open GC.Spec.Top.ToyMinor
open GC.Spec.Top.ToyComps
module L = FStar.List.Tot
module Seq = FStar.Seq

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Concrete heaps
/// ---------------------------------------------------------------------------

let hdr (w: nat) (c: colour) : header = { wz = w; tag = 0; col = c }

/// Two blocks: at 0 (wosize `w0`) and at `w0 + 1` (wosize `w1`).
let heap2 (w0: nat) (c0: colour) (w1: nat) (c1: colour) (body: nat -> value) : mheap =
  { size = w0 + w1 + 2;
    hd = (fun (x: nat) -> if x = 0 then Some (hdr w0 c0) else if x = w0 + 1 then Some (hdr w1 c1) else None);
    body = body }

/// Three blocks: at 0, `w0 + 1` and `w0 + w1 + 2`.
let heap3 (w0: nat) (c0: colour) (w1: nat) (c1: colour) (w2: nat) (c2: colour) (body: nat -> value) : mheap =
  { size = w0 + w1 + w2 + 3;
    hd = (fun (x: nat) ->
      if x = 0 then Some (hdr w0 c0)
      else if x = w0 + 1 then Some (hdr w1 c1)
      else if x = w0 + w1 + 2 then Some (hdr w2 c2)
      else None);
    body = body }

let heap2_wf (w0: nat) (c0: colour) (w1: nat) (c1: colour) (body: nat -> value)
  : Lemma (well_formed (heap2 w0 c0 w1 c1 body))
  = let h = heap2 w0 c0 w1 c1 body in
    let cov (w: nat) : Lemma (w < h.size ==> (exists (o: nat). covers h o w))
      = if w <= w0 then assert (covers h 0 w) else if w < h.size then assert (covers h (w0 + 1) w) in
    FStar.Classical.forall_intro cov;
    tiled_intro h

let heap3_wf (w0: nat) (c0: colour) (w1: nat) (c1: colour) (w2: nat) (c2: colour) (body: nat -> value)
  : Lemma (well_formed (heap3 w0 c0 w1 c1 w2 c2 body))
  = let h = heap3 w0 c0 w1 c1 w2 c2 body in
    let cov (w: nat) : Lemma (w < h.size ==> (exists (o: nat). covers h o w))
      = if w <= w0 then assert (covers h 0 w)
        else if w <= w0 + w1 + 1 then assert (covers h (w0 + 1) w)
        else if w < h.size then assert (covers h (w0 + w1 + 2) w) in
    FStar.Classical.forall_intro cov;
    tiled_intro h

let zero_body : nat -> value = fun _ -> VInt 0

let st_at (c: nat) : tstate = { cur = c; dead = (fun _ -> false) }

/// ---------------------------------------------------------------------------
/// 1. An allocator that hands out an object in use
/// ---------------------------------------------------------------------------

let bad_inuse_alloc (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
  : GTot (mheap & tstate & result) =
  if st.cur > 0 then (h, st, Ok 0) else talloc ph h st sz tag

let bad_inuse : allocator tk = { toy with alloc = bad_inuse_alloc }

/// One white object at 0, the tail at 2.
let h_one : mheap = heap2 1 White 1 White zero_body

let one_local (o: nat) : Lemma (tlocal Idle h_one (st_at 2) o) = ()

let h_one_inv () : Lemma (tinv Idle h_one (st_at 2) /\ well_formed h_one)
  = FStar.Classical.forall_intro one_local;
    assert_norm (is_block h_one 2 /\ wz_of h_one 2 == 1 /\ h_one.size == 4);
    assert (tail_ok h_one 2);
    heap2_wf 1 White 1 White zero_body;
    tinv_intro Idle h_one (st_at 2)

let bad_inuse_rejected () : Lemma (~(alloc_ok bad_inuse))
  = let aux () : Lemma (requires alloc_ok bad_inuse) (ensures False)
      = h_one_inv ();
        assert (alloc_at bad_inuse Idle h_one (st_at 2) 1 0);
        assert (covers h_one 0 0);
        assert (free_word bad_inuse (st_at 2) h_one 0);
        let b = FStar.IndefiniteDescription.indefinite_description_ghost nat
                  (fun b -> covers h_one b 0 /\ bad_inuse.free (st_at 2) h_one b == true) in
        assert (b == 0)
    in
    FStar.Classical.move_requires aux ()

/// ---------------------------------------------------------------------------
/// 2. An allocator whose room is always false: it meets allocator_ok, and
///    only `nontrivial` rejects it
/// ---------------------------------------------------------------------------

let bad_noroom : allocator tk =
  { toy with room = (fun _ _ _ _ -> false); alloc = (fun _ h st _ _ -> (h, st, NoRoom)) }

let bad_noroom_meets_allocator_ok () : Lemma (allocator_ok bad_noroom)
  = toy_allocator_ok ();
    let i (n: nat) : Lemma (init_at bad_noroom n) = assert (init_at toy n) in
    FStar.Classical.forall_intro i;
    let f (ph: phase tprog) (h: mheap) (st: tstate) (h': mheap) : Lemma (inv_frame_at bad_noroom ph h st h')
      = assert (inv_frame_at toy ph h st h') in
    let f3 (ph: phase tprog) (h: mheap) (st: tstate) : Lemma (forall h'. inv_frame_at bad_noroom ph h st h')
      = FStar.Classical.forall_intro (f ph h st) in
    FStar.Classical.forall_intro_3 f3;
    let w (ph: phase tprog) (h: mheap) (st: tstate) : Lemma (free_white_at bad_noroom ph h st)
      = assert (free_white_at toy ph h st) in
    FStar.Classical.forall_intro_3 w;
    let s (h: mheap) (st: tstate) : Lemma (inv_start_at bad_noroom h st)
      = assert (inv_start_at toy h st) in
    FStar.Classical.forall_intro_2 s;
    let fh (st: tstate) (h h': mheap) : Lemma (free_hd_at bad_noroom st h h') = () in
    FStar.Classical.forall_intro_3 fh;
    let a (ph: phase tprog) (h: mheap) (st: tstate) : Lemma (forall sz tag. alloc_at bad_noroom ph h st sz tag)
      = let a1 (sz: size_t) (tag: tag_t) : Lemma (alloc_at bad_noroom ph h st sz tag) = () in
        FStar.Classical.forall_intro_2 a1 in
    FStar.Classical.forall_intro_3 a

/// The same allocator plugged into a collector, with the toy's capacity
/// condition (the free tail).
let c_noroom : comps =
  { k = tk; a = bad_noroom; s = { start = tstart; step = tstep; done = tdone }; m = tmark;
    n = { collect = (fun _ _ _ -> OutOfRoom) }; b = tbarrier; fits = toy_fits }

/// Rejected at the initial state of the empty run: the tail has room, the
/// allocator says no.
let bad_noroom_rejected () : Lemma (~(nontrivial c_noroom))
  = let aux () : Lemma (requires nontrivial c_noroom) (ensures False)
      = assert (run_ok c_noroom Sequential 2 2 []);
        assert_nbe (c_noroom.fits (at c_noroom 2 2 [] 0).ph (at c_noroom 2 2 [] 0).ast (at c_noroom 2 2 [] 0).w.maj 1);
        assert_nbe (c_noroom.a.room (at c_noroom 2 2 [] 0).ph (at c_noroom 2 2 [] 0).ast (at c_noroom 2 2 [] 0).w.maj 1 == false)
    in
    FStar.Classical.move_requires aux ()

/// ---------------------------------------------------------------------------
/// 2b. An allocator with room only on the initial heap (G18): it meets
///     allocator_ok and the old, initial-heap-only non-triviality; the
///     run-reachable `nontrivial` rejects it
/// ---------------------------------------------------------------------------

let once_alloc (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
  : GTot (mheap & tstate & result) =
  if st.cur = 0 then talloc ph h st sz tag else (h, st, NoRoom)

/// alloc_post reads only `room`, `free` and `inv`: an allocator updated in
/// `room` and `alloc` keeps the post of an allocation where the rooms agree.
let alloc_post_with_room (#k: sweep_kind) (a: allocator k)
    (room2: phase k.progress -> a.state -> mheap -> size_t -> GTot bool)
    (alloc2: phase k.progress -> mheap -> a.state -> size_t -> tag_t -> GTot (mheap & a.state & result))
    (ph: phase k.progress) (h: mheap) (st: a.state) (sz: size_t) (tag: tag_t) (h': mheap) (st': a.state) (r: result)
  : Lemma (requires alloc_post a ph h st sz tag h' st' r /\ room2 ph st h sz == a.room ph st h sz)
          (ensures alloc_post ({ a with room = room2; alloc = alloc2 }) ph h st sz tag h' st' r)
  = ()

let bad_once : allocator tk =
  { toy with room = (fun ph st h sz -> st.cur = 0 && troom ph st h sz); alloc = once_alloc }

let bad_once_meets_allocator_ok () : Lemma (allocator_ok bad_once)
  = toy_allocator_ok ();
    let i (n: nat) : Lemma (init_at bad_once n) = assert (init_at toy n) in
    FStar.Classical.forall_intro i;
    let f (ph: phase tprog) (h: mheap) (st: tstate) (h': mheap) : Lemma (inv_frame_at bad_once ph h st h')
      = assert (inv_frame_at toy ph h st h') in
    let f3 (ph: phase tprog) (h: mheap) (st: tstate) : Lemma (forall h'. inv_frame_at bad_once ph h st h')
      = FStar.Classical.forall_intro (f ph h st) in
    FStar.Classical.forall_intro_3 f3;
    let w (ph: phase tprog) (h: mheap) (st: tstate) : Lemma (free_white_at bad_once ph h st)
      = assert (free_white_at toy ph h st) in
    FStar.Classical.forall_intro_3 w;
    let s (h: mheap) (st: tstate) : Lemma (inv_start_at bad_once h st)
      = assert (inv_start_at toy h st) in
    FStar.Classical.forall_intro_2 s;
    let fh (st: tstate) (h h': mheap) : Lemma (free_hd_at bad_once st h h') = () in
    FStar.Classical.forall_intro_3 fh;
    let a (ph: phase tprog) (h: mheap) (st: tstate) : Lemma (forall sz tag. alloc_at bad_once ph h st sz tag)
      = let a1 (sz: size_t) (tag: tag_t) : Lemma (alloc_at bad_once ph h st sz tag)
          = if st.cur = 0 then begin
              talloc_ok ph h st sz tag;
              let pre () : Lemma (requires bad_once.inv ph h st /\ well_formed h /\ tag <> infix_tag)
                                 (ensures (let (h', st', r) = bad_once.alloc ph h st sz tag in
                                           alloc_post bad_once ph h st sz tag h' st' r))
                = let (h', st', r) = toy.alloc ph h st sz tag in
                  assert (alloc_post toy ph h st sz tag h' st' r);
                  alloc_post_with_room toy (fun ph st h sz -> st.cur = 0 && troom ph st h sz) once_alloc
                    ph h st sz tag h' st' r in
              FStar.Classical.move_requires pre ()
            end in
        FStar.Classical.forall_intro_2 a1 in
    FStar.Classical.forall_intro_3 a

/// The old non-triviality (room on some initial heap) accepts it.
let bad_once_initial_room () : Lemma (exists (n: nat) (sz: size_t). (let (h, st) = bad_once.init n in bad_once.room Idle st h sz == true))
  = assert_nbe (let (h, st) = bad_once.init 2 in bad_once.room Idle st h 1 == true)

let c_once : comps =
  { k = tk; a = bad_once; s = { start = tstart; step = tstep; done = tdone }; m = tmark;
    n = { collect = (fun _ _ _ -> OutOfRoom) }; b = tbarrier; fits = toy_fits }

let es_once : list event = [EAlloc 1 0 [VInt 0]]

#push-options "--fuel 2"
let once_run_ok () : Lemma (run_ok c_once Sequential 4 4 es_once)
  = let f (i: nat) : Lemma (i < L.length es_once ==>
                            (let x = at c_once 4 4 es_once i in
                             let e = ev es_once i in
                             enabled c_once x e /\ style_ok Sequential x e /\ mutator_ok x e))
      = if i = 0 then begin
          assert_nbe ((at c_once 4 4 es_once 0).stopped == false /\ Idle? (at c_once 4 4 es_once 0).ph /\
                      ev es_once 0 == EAlloc 1 0 [VInt 0])
        end in
    FStar.Classical.forall_intro f
#pop-options

/// After one allocation the tail still has room for a one-field object; the
/// allocator refuses.
let bad_once_rejected () : Lemma (~(nontrivial c_once))
  = once_run_ok ();
    let aux () : Lemma (requires nontrivial c_once) (ensures False)
      = assert_nbe (c_once.fits (at c_once 4 4 es_once 1).ph (at c_once 4 4 es_once 1).ast (at c_once 4 4 es_once 1).w.maj 1);
        assert_nbe (c_once.a.room (at c_once 4 4 es_once 1).ph (at c_once 4 4 es_once 1).ast (at c_once 4 4 es_once 1).w.maj 1 == false);
        assert (1 <= L.length es_once)
    in
    FStar.Classical.move_requires aux ()

/// ---------------------------------------------------------------------------
/// 3. A sweep that frees a black object
/// ---------------------------------------------------------------------------

let bad_black_step (pe: tprog) (h: mheap) (st: tstate) : GTot (tprog & mheap & tstate & step_result) =
  let p = fst pe in
  let e = snd pe in
  if p < e then
    ((p + wz_of h p + 1, e), h, { st with dead = (fun (x: nat) -> x = p || st.dead x) },
     { units = 1; freed_words = wz_of h p + 1 })
  else (pe, h, st, { units = 0; freed_words = 0 })

let bad_black : sweep tk toy = { tsweep with step = bad_black_step }

/// One black object at 0, the tail at 2; sweeping, nothing swept yet.
let h_black : mheap = heap2 1 Black 1 White zero_body

let black_local (o: nat)
  : Lemma (tlocal (Sweeping (0, 2)) h_black (st_at 2) o /\ (is_block h_black o ==> col_of h_black o <> Grey))
  = ()

let black_facts () : Lemma (tinv (Sweeping (0, 2)) h_black (st_at 2) /\ well_formed h_black /\ no_grey h_black)
  = FStar.Classical.forall_intro black_local;
    assert_norm (is_block h_black 2 /\ wz_of h_black 2 == 1 /\ is_block h_black 0 /\ h_black.size == 4);
    assert (tail_ok h_black 2);
    assert (tglob (Sweeping (0, 2)) h_black (st_at 2));
    heap2_wf 1 Black 1 White zero_body;
    tinv_intro (Sweeping (0, 2)) h_black (st_at 2)

let bad_black_fails () : Lemma (~(sweep_step_at bad_black (0, 2) h_black (st_at 2)))
  = black_facts ();
    let aux () : Lemma (requires sweep_step_at bad_black (0, 2) h_black (st_at 2)) (ensures False)
      = assert (in_use toy (st_at 2) h_black 0 /\ region tk (0, 2) (2, 2) 0 /\ col_of h_black 0 == Black) in
    FStar.Classical.move_requires aux ()

let bad_black_rejected () : Lemma (~(sweep_ok bad_black)) = bad_black_fails ()

/// ---------------------------------------------------------------------------
/// 4. A sweep that re-sweeps swept memory
/// ---------------------------------------------------------------------------

/// The toy step, then every white block in use below the start of the
/// step's region is freed again.
let bad_resweep_step (pe: tprog) (h: mheap) (st: tstate) : GTot (tprog & mheap & tstate & step_result) =
  let (pe', h', st', r) = tstep pe h st in
  (pe', h',
   { st' with dead = (fun (x: nat) ->
       st'.dead x || (x < fst pe && is_block h x && col_of h x = White && not (tfree st h x))) },
   r)

let bad_resweep : sweep tk toy = { tsweep with step = bad_resweep_step }

/// A swept survivor (white) at 0, a black object at 2, the tail at 4;
/// sweeping, progress at 2.
let h_resweep : mheap = heap3 1 White 1 Black 1 White zero_body

let resweep_local (o: nat)
  : Lemma (tlocal (Sweeping (2, 4)) h_resweep (st_at 4) o /\ (is_block h_resweep o ==> col_of h_resweep o <> Grey))
  = ()

let resweep_facts () : Lemma (tinv (Sweeping (2, 4)) h_resweep (st_at 4) /\ well_formed h_resweep /\ no_grey h_resweep)
  = FStar.Classical.forall_intro resweep_local;
    assert_norm (is_block h_resweep 4 /\ wz_of h_resweep 4 == 1 /\ is_block h_resweep 2 /\ h_resweep.size == 6);
    assert (tail_ok h_resweep 4);
    assert (tglob (Sweeping (2, 4)) h_resweep (st_at 4));
    heap3_wf 1 White 1 Black 1 White zero_body;
    tinv_intro (Sweeping (2, 4)) h_resweep (st_at 4)

let bad_resweep_fails () : Lemma (~(sweep_step_at bad_resweep (2, 4) h_resweep (st_at 4)))
  = resweep_facts ();
    let aux () : Lemma (requires sweep_step_at bad_resweep (2, 4) h_resweep (st_at 4)) (ensures False)
      = assert (in_use toy (st_at 4) h_resweep 0 /\ not (region tk (2, 4) (4, 4) 0)) in
    FStar.Classical.move_requires aux ()

let bad_resweep_rejected () : Lemma (~(sweep_ok bad_resweep)) = bad_resweep_fails ()

/// ---------------------------------------------------------------------------
/// Unreachability
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// 5. A mutator that sets a root to a garbage object
/// ---------------------------------------------------------------------------

/// A at 0 (the root's target), C at 2 (in the snapshot, since dropped), the
/// tail at 4; marking.
let w_garbage : world =
  { maj = heap3 1 Black 1 White 1 White zero_body; yng = empty_heap 4;
    roots = [VPtr (Major 0)]; rem = [] }

let x_garbage : config tc =
  { w = w_garbage; ph = Marking; ast = st_at 4; hs = w_garbage.maj;
    snap = (fun o -> o == 0 \/ o == 2); allocd = (fun _ -> False); stopped = false }

let garbage_unreachable () : Lemma (~(reachable w_garbage 2))
  = let s (o: nat) : prop = o == 0 in
    assert_norm (resolve w_garbage.maj 0 == Some 0);
    let out (x: nat) : Lemma (outside_ref w_garbage x ==> s x)
      = root_b_iff w_garbage.maj w_garbage.roots x;
        young_b_iff w_garbage x;
        assert_norm (root_b w_garbage.maj w_garbage.roots x == (Some 0 = Some x || false)) in
    FStar.Classical.forall_intro out;
    not_reachable w_garbage s 2

let bad_root_rejected () : Lemma (~(mutator_ok x_garbage (ERoots [VPtr (Major 2)])))
  = garbage_unreachable ()

/// The snapshot-based reading of mutator_ok: roots, stored values and write
/// targets resolve to snapshot_k U allocated_k U reachable young objects.
let value_ok_snapshot (#c: comps) (x: config c) (v: value) : prop =
  match v with
  | VInt _ -> True
  | VInfix _ -> False
  | VPtr (Major a) -> exists (o: nat). resolve x.w.maj a == Some o /\ (x.snap o \/ x.allocd o)
  | VPtr (Young a) -> exists (o: nat). resolve x.w.yng a == Some o /\ yreachable x.w o

/// It accepts the event: the gap behind (3c).
#push-options "--fuel 2"
let bad_root_accepted_by_snapshot_reading ()
  : Lemma (forall (v: value). L.memP v [VPtr (Major 2)] ==> value_ok_snapshot x_garbage v)
  = assert_norm (resolve w_garbage.maj 2 == Some 2);
    assert (x_garbage.snap 2);
    assert (value_ok_snapshot x_garbage (VPtr (Major 2)));
    let m (v: value) : Lemma (L.memP v [VPtr (Major 2)] ==> v == VPtr (Major 2)) = () in
    FStar.Classical.forall_intro m
#pop-options

/// ---------------------------------------------------------------------------
/// 6. A minor collection that skips the remembered slots
/// ---------------------------------------------------------------------------

let bad_norem : minor tk toy = { collect = (fun ph st w -> tcollect ph st ({ w with rem = [] })) }

/// A at 0 holds the only pointer to young Y; the slot (0, 0) is remembered.
let w_rem : world =
  { maj = heap2 1 White 3 White (fun (x: nat) -> if x = 1 then VPtr (Young 0) else VInt 0);
    yng = { size = 4; hd = (fun (x: nat) -> if x = 0 then Some (hdr 1 White) else None); body = zero_body };
    roots = [VPtr (Major 0)]; rem = [(0, 0)] }

let rec mlive_none (w: world) (y: nat) (l: mlive w y)
  : Lemma (requires (forall (v: value). L.memP v w.roots ==> ~(VPtr? v /\ Young? (VPtr?._0 v))) /\ w.rem == [])
          (ensures False)
          (decreases l)
  = match l with
    | LRoot _ a _ -> assert (L.memP (VPtr (Young a)) w.roots)
    | LRem _ _ _ _ _ -> ()
    | LStep y0 _ l' _ -> mlive_none w y0 l'

let list_empty (l: list nat) : Lemma (requires forall (o: nat). ~(L.memP o l)) (ensures l == [])
  = match l with
    | [] -> ()
    | h :: _ -> assert (L.memP h l)

let rem_local (o: nat) : Lemma (tlocal Idle w_rem.maj (st_at 2) o) = ()

let rem_young_ok () : Lemma (young_ok w_rem.yng) = ()

let rem_cov () : Lemma (rem_covers toy (st_at 2) w_rem)
  = let c (o i b: nat) : Lemma (in_use toy (st_at 2) w_rem.maj o /\ ptr_field w_rem.maj o i /\
                                field w_rem.maj o i == VPtr (Young b) ==> L.memP (o, i) w_rem.rem)
      = if in_use toy (st_at 2) w_rem.maj o && ptr_field w_rem.maj o i then assert (o == 0 /\ i == 0) in
    FStar.Classical.forall_intro_3 c

let norem_facts () : Lemma (minor_pre toy Idle (st_at 2) w_rem /\ minor_live w_rem 0 /\ is_block w_rem.yng 0)
  = FStar.Classical.forall_intro rem_local;
    assert_norm (is_block w_rem.maj 2 /\ wz_of w_rem.maj 2 == 3 /\ w_rem.maj.size == 6);
    assert (tail_ok w_rem.maj 2);
    heap2_wf 1 White 3 White (fun (x: nat) -> if x = 1 then VPtr (Young 0) else VInt 0);
    tinv_intro Idle w_rem.maj (st_at 2);
    rem_young_ok ();
    rem_cov ();
    let l : mlive w_rem 0 = LRem 0 0 0 0 () in
    ()

#push-options "--fuel 2"
let rem_roots_major ()
  : Lemma (forall (v: value). L.memP v w_rem.roots ==> ~(VPtr? v /\ Young? (VPtr?._0 v)))
  = let m (v: value) : Lemma (L.memP v w_rem.roots ==> v == VPtr (Major 0)) = () in
    FStar.Classical.forall_intro m
#pop-options

/// Without the slot nothing is live, so nothing is promoted.
let norem_result () : Lemma (Done? (bad_norem.collect Idle (st_at 2) w_rem) /\
                             Done?.fwd (bad_norem.collect Idle (st_at 2) w_rem) 0 == None)
  = let st = st_at 2 in
    let w' = { w_rem with rem = [] } in
    rem_roots_major ();
    let nl (y: nat) : Lemma (live_g w' y == false)
      = let f (l: mlive w' y) : Lemma False = mlive_none w' y l in
        FStar.Classical.forall_intro f in
    FStar.Classical.forall_intro nl;
    live_list_spec w' 4;
    list_empty (live_list w' 4)

let bad_norem_fails () : Lemma (~(minor_at bad_norem Idle (st_at 2) w_rem))
  = norem_facts (); norem_result ();
    let aux () : Lemma (requires minor_at bad_norem Idle (st_at 2) w_rem) (ensures False)
      = assert (minor_post toy Idle (st_at 2) w_rem (bad_norem.collect Idle (st_at 2) w_rem)) in
    FStar.Classical.move_requires aux ()

let bad_norem_rejected () : Lemma (~(minor_ok bad_norem)) = bad_norem_fails ()

/// ---------------------------------------------------------------------------
/// 7. A mark that does not grey old objects held only by young objects
/// ---------------------------------------------------------------------------

let bad_roots_only_start (w: world) : GTot mheap =
  { w.maj with hd = (fun (x: nat) ->
      match w.maj.hd x with
      | Some hx -> if root_b w.maj w.roots x && hx.col = White then Some ({ hx with col = Grey }) else Some hx
      | None -> None) }

let bad_roots_only : mark = { tmark with mstart = bad_roots_only_start }

/// A at 0 is held only by the young Y; no roots.
let w_young_held : world =
  { maj = heap2 1 White 1 White zero_body;
    yng = { size = 4; hd = (fun (x: nat) -> if x = 0 then Some (hdr 1 White) else None);
            body = (fun (x: nat) -> if x = 1 then VPtr (Major 0) else VInt 0) };
    roots = []; rem = [] }

let young_held_facts ()
  : Lemma (well_formed w_young_held.maj /\ no_dark w_young_held.maj /\
           (forall (o: nat). reachable w_young_held o ==> is_block w_young_held.maj o /\ col_of w_young_held.maj o == White) /\
           outside_ref w_young_held 0)
  = let w = w_young_held in
    heap2_wf 1 White 1 White zero_body;
    let s (o: nat) : prop = o == 0 in
    let out (x: nat) : Lemma (outside_ref w x ==> s x)
      = root_b_iff w.maj w.roots x; young_b_iff w x in
    FStar.Classical.forall_intro out;
    let r (o: nat) : Lemma (reachable w o ==> is_block w.maj o /\ col_of w.maj o == White)
      = if FStar.IndefiniteDescription.strong_excluded_middle (reachable w o) then begin
          let rr = FStar.IndefiniteDescription.indefinite_description_ghost (reach w o) (fun _ -> True) in
          reach_within w s o rr
        end in
    FStar.Classical.forall_intro r;
    assert_norm (ptr_field w_young_held.yng 0 0 == true /\ field w_young_held.yng 0 0 == VPtr (Major 0) /\ resolve w_young_held.maj 0 == Some 0);
    assert (young_ref w 0)

let bad_roots_only_fails () : Lemma (~(mark_start_at bad_roots_only w_young_held))
  = young_held_facts ();
    assert (col_of (bad_roots_only_start w_young_held) 0 == White);
    assert (~(dark (col_of (bad_roots_only_start w_young_held) 0)))

let bad_roots_only_rejected () : Lemma (~(mark_ok bad_roots_only)) = bad_roots_only_fails ()

/// ---------------------------------------------------------------------------
/// 8. A minor collection that always reports OutOfRoom
/// ---------------------------------------------------------------------------

let bad_oor : minor tk toy = { collect = (fun _ _ _ -> OutOfRoom) }

let w_empty : world = { maj = tinit_heap 4; yng = empty_heap 4; roots = []; rem = [] }
let st_empty : tstate = { cur = 0; dead = (fun _ -> false) }

let bad_oor_fails () : Lemma (~(minor_at bad_oor Idle st_empty w_empty))
  = tinit_ok 4;
    assert (minor_pre toy Idle st_empty w_empty);
    let aux () : Lemma (requires minor_at bad_oor Idle st_empty w_empty) (ensures False)
      = let ys = FStar.IndefiniteDescription.indefinite_description_ghost (list nat)
                   (fun ys -> L.noRepeats ys /\
                              (forall (o: nat). L.memP o ys ==> is_block w_empty.yng o /\ minor_live w_empty o) /\
                              alloc_fold toy Idle w_empty.maj st_empty w_empty.yng ys == None) in
        list_empty ys in
    FStar.Classical.move_requires aux ()

let bad_oor_rejected () : Lemma (~(minor_ok bad_oor)) = bad_oor_fails ()

/// ---------------------------------------------------------------------------
/// 9. A barrier that does not remember a Fill's young pointers
/// ---------------------------------------------------------------------------

let bad_init : barrier = { tbarrier with binit = (fun h rem o vs -> (fill h o vs, rem)) }

let bad_init_fails () : Lemma (~(barrier_init_at bad_init h_one [] 0 [VPtr (Young 0)]))
  = assert_norm (is_block h_one 0 == true /\ wz_of h_one 0 == 1 /\
                 young_slot h_one 0 0 (VPtr (Young 0)) == true);
    assert_norm (L.length [VPtr (Young 0)] == 1 /\ L.index [VPtr (Young 0)] 0 == VPtr (Young 0));
    assert (snd (bad_init.binit h_one [] 0 [VPtr (Young 0)]) == [])

let bad_init_rejected () : Lemma (~(barrier_ok bad_init)) = bad_init_fails ()
