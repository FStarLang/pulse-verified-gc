/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Vacuity - constructive runs satisfying every hypothesis
/// ---------------------------------------------------------------------------
///
/// Non-vacuity of `gc_correct` and `gc_correct_local`
/// (GC.Spec.Top.Run), for the toy collector `tc`: one run per style, each
/// exercising every event, each satisfying every hypothesis:
///   - the components' contracts (`toy_components_ok`);
///   - the run is allowed: every event enabled, in its style, meeting the
///     mutator's obligations (`run_ok`), checked event by event on the
///     concrete configurations;
///   - the contracts at every step (`run_hyps`), from the contracts.
///
/// The toy works on model heaps, its representation equality
/// (GC.Spec.Top.ToyRep); a configuration's one model world is `wo x`.
///
/// The runs (heap of 12 words, nursery of 4):
///   - A at 0 (root), B at 2 (A.0 = B), C at 4 (dropped: unreachable),
///     young Y (Y.0 = B, then dropped), then a full cycle, a read of A.0
///     into a root, then a minor collection;
///   - incremental: the same start, then during marking an allocation (D,
///     black) and an overwrite of A.0 (the barrier), during sweeping an
///     allocation (E, white), a write and a root change; then the read and
///     the minor collection.
/// At the cycle's start, A and B are reachable and C is not
/// (`c_unreachable_at_start`).

module GC.Spec.Top.Vacuity

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.IdRep
open GC.Spec.Top.ToyRep
open GC.Spec.Top.Toy
open GC.Spec.Top.ToyMark
open GC.Spec.Top.ToyMinor
open GC.Spec.Top.ToyComps
module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// The world of a toy configuration (the one model world representing it).
let wo (x: config tc) : world = tview x.w


/// ---------------------------------------------------------------------------
/// Decidable sufficient conditions
/// ---------------------------------------------------------------------------

let reach_by_root (w: world) (o: nat)
  : Lemma (requires root_b w.maj w.roots o == true) (ensures reachable w o)
  = root_b_iff w.maj w.roots o;
    let r : reach w o = RBase o () in ()

let reach_by_young (w: world) (o: nat)
  : Lemma (requires young_b w o == true) (ensures reachable w o)
  = young_b_iff w o;
    let r : reach w o = RBase o () in ()

let rec yroot_b (y: mheap) (rs: list value) (o: nat) : bool =
  match rs with
  | [] -> false
  | v :: tl -> (match v with VPtr (Young a) -> resolve y a = Some o | _ -> false) || yroot_b y tl o

let rec yroot_b_mem (y: mheap) (rs: list value) (o: nat)
  : Lemma (requires yroot_b y rs o == true)
          (ensures exists (a: nat). L.memP (VPtr (Young a)) rs /\ resolve y a == Some o)
  = match rs with
    | v :: tl ->
      match v with
      | VPtr (Young a) -> if resolve y a = Some o then () else yroot_b_mem y tl o
      | _ -> yroot_b_mem y tl o

let yreach_by_root (w: world) (o: nat)
  : Lemma (requires yroot_b w.yng w.roots o == true) (ensures yreachable w o)
  = yroot_b_mem w.yng w.roots o;
    let a = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun a -> L.memP (VPtr (Young a)) w.roots /\ resolve w.yng a == Some o) in
    let r : yreach w o = YRoot o a () in ()

/// A major pointer the program may hold: to an object it reaches through a
/// root or a young object.
let major_ok_b (w: world) (a: nat) : bool =
  resolve w.maj a = Some a && (root_b w.maj w.roots a || young_b w a)

let major_ok (w: world) (a: nat)
  : Lemma (requires major_ok_b w a == true) (ensures value_ok w (VPtr (Major a)))
  = if root_b w.maj w.roots a then reach_by_root w a else reach_by_young w a

let young_ok_b (w: world) (a: nat) : bool =
  resolve w.yng a = Some a && yroot_b w.yng w.roots a

let young_vok (w: world) (a: nat)
  : Lemma (requires young_ok_b w a == true) (ensures value_ok w (VPtr (Young a)))
  = yreach_by_root w a

let grey_at (h: mheap) (o: nat) : bool = is_block h o && col_of h o = Grey

let no_grey_b (h: mheap) : bool =
  not (exists_below h.size (grey_at h))

let no_grey_of_b (h: mheap) : Lemma (requires no_grey_b h == true) (ensures no_grey h)
  = exists_below_iff h.size (grey_at h)

let overlaps (y: mheap) (o: nat) (sz: nat) (x: nat) : bool = is_block y x && x <= o + sz && o <= x + wz_of y x

let young_free_b (y: mheap) (o: nat) (sz: nat) : bool =
  o + sz < y.size && not (exists_below y.size (overlaps y o sz))

let young_free_of_b (y: mheap) (o: nat) (sz: size_t)
  : Lemma (requires young_free_b y o sz == true) (ensures young_free y o sz)
  = exists_below_iff y.size (overlaps y o sz)

/// ---------------------------------------------------------------------------
/// The runs
/// ---------------------------------------------------------------------------

let n_heap : nat = 12
let n_young : nat = 4

let prefix : list event = [
  EAlloc 1 0 [VInt 0];                    (* 0: A at 0 *)
  EAlloc 1 0 [VInt 0];                    (* 1: B at 2 *)
  EWrite (Major 0) 0 (VPtr (Major 2));    (* 2: A.0 := B *)
  EAlloc 1 0 [VInt 1];                    (* 3: C at 4 *)
  EYoungAlloc 1 0 [VPtr (Major 0)];     (* 4: young Y, Y.0 = A *)
  EWrite (Young 0) 0 (VPtr (Major 2));    (* 5: Y.0 := B *)
  ERoots [VPtr (Major 0)]                 (* 6: only A is a root *)
]

let es_seq : list event = L.append prefix [
  EStart;                                 (* 7: snapshot {A, B}; C unreachable *)
  ESlice;                                 (* 8: scan A *)
  ESlice;                                 (* 9: scan B *)
  EHandover;                              (* 10: progress (0, 6) *)
  ESweep;                                 (* 11: A black -> white *)
  ESweep;                                 (* 12: B black -> white *)
  ESweep;                                 (* 13: C white -> free *)
  EEnd;                                   (* 14 *)
  ERead (Major 0) 0;                      (* 15: read A.0 into a root *)
  EMinor                                  (* 16 *)
]

let es_inc : list event = L.append prefix [
  EStart;                                 (* 7 *)
  EAlloc 1 0 [VPtr (Major 2)];            (* 8: D at 6, black, D.0 = B *)
  EWrite (Major 0) 0 (VInt 5);            (* 9: A.0 := 5, the barrier greys B *)
  ESlice;                                 (* 10: scan A *)
  ESlice;                                 (* 11: scan B *)
  EHandover;                              (* 12: progress (0, 8) *)
  EAlloc 1 0 [VPtr (Major 6)];            (* 13: E at 8, white, E.0 = D *)
  EWrite (Major 6) 0 (VPtr (Major 0));    (* 14: D.0 := A *)
  ERoots [VPtr (Major 8); VPtr (Major 0)];(* 15: drop D *)
  ESweep;                                 (* 16: A *)
  ESweep;                                 (* 17: B *)
  ESweep;                                 (* 18: C freed *)
  ESweep;                                 (* 19: D *)
  EEnd;                                   (* 20 *)
  ERead (Major 0) 0;                      (* 21: read A.0 into a root *)
  EMinor                                  (* 22 *)
]

let cs (i: nat) : GTot (config tc) = at tc n_heap n_young es_seq i
let ci (i: nat) : GTot (config tc) = at tc n_heap n_young es_inc i

let step_ok (es: list event) (sty: style) (i: nat) : prop =
  i < L.length es /\
  (let x = at tc n_heap n_young es i in
   let e = ev es i in
   enabled tc x e /\ style_ok sty x e /\ mutator_ok x e)

/// ---------------------------------------------------------------------------
/// The checks, event by event
/// ---------------------------------------------------------------------------

/// A collector event, or a mutator event whose values are bytes.
let simple_b (sty: style) (x: config tc) (e: event) : GTot bool =
  not x.stopped &&
  (match e with
   | EAlloc sz tag vs -> tag <> infix_tag && L.length vs = sz && L.for_all VInt? vs &&
                         (not (Sequential? sty) || Idle? x.ph)
   | EStart -> Idle? x.ph
   | ESlice -> Marking? x.ph && not (no_grey_b (wo x).maj)
   | EHandover -> Marking? x.ph && no_grey_b (wo x).maj
   | ESweep -> Sweeping? x.ph && not (tsweep.done (Sweeping?._0 x.ph))
   | EEnd -> Sweeping? x.ph && tsweep.done (Sweeping?._0 x.ph)
   | EMinor -> true
   | _ -> false)

let rec for_all_vint (vs: list value) (i: nat)
  : Lemma (requires L.for_all VInt? vs == true /\ i < L.length vs) (ensures VInt? (L.index vs i))
  = match vs with
    | _ :: tl -> if i = 0 then () else for_all_vint tl (i - 1)

let simple_ok (sty: style) (x: config tc) (e: event)
  : Lemma (requires simple_b sty x e == true) (ensures enabled tc x e /\ style_ok sty x e /\ mutator_ok x e)
  = tc_vw x;
    match e with
    | EAlloc sz tag vs ->
      let f (i: nat) : Lemma (i < L.length vs ==> value_ok (wo x) (L.index vs i))
        = if i < L.length vs then for_all_vint vs i in
      FStar.Classical.forall_intro f;
      tc_storable vs; mutator_of x e
    | ESlice ->
      exists_below_iff (wo x).maj.size (grey_at (wo x).maj);
      let g = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun o -> o < (wo x).maj.size /\ is_block (wo x).maj o /\ col_of (wo x).maj o == Grey) in
      assert (~(no_grey (wo x).maj))
    | EHandover -> no_grey_of_b (wo x).maj
    | _ -> ()

let simple_step (es: list event) (sty: style) (i: nat{i < L.length es})
  : Lemma (requires simple_b sty (at tc n_heap n_young es i) (ev es i) == true)
          (ensures step_ok es sty i)
  = simple_ok sty (at tc n_heap n_young es i) (ev es i)

/// ESlice: something is grey.
let slice_enabled (x: config tc)
  : Lemma (requires Marking? x.ph /\ x.stopped == false /\ no_grey_b (wo x).maj == false)
          (ensures enabled tc x ESlice)
  = tc_vw x;
    exists_below_iff (wo x).maj.size (grey_at (wo x).maj)

#push-options "--fuel 2"
let single_fill (w: world) (v: value)
  : Lemma (requires value_ok w v) (ensures L.length [v] == 1 /\ fill_ok w 0 [v])
  = let f (i: nat) : Lemma (i < L.length [v] ==> value_ok w (L.index [v] i)) = () in
    FStar.Classical.forall_intro f
#pop-options

/// An allocation filled with one pointer the program holds.
let alloc_ptr_ok (sty: style) (x: config tc) (a: nat)
  : Lemma (requires x.stopped == false /\ major_ok_b (wo x) a == true /\ (Sequential? sty ==> Idle? x.ph))
          (ensures (let e = EAlloc 1 0 [VPtr (Major a)] in enabled tc x e /\ style_ok sty x e /\ mutator_ok x e))
  = major_ok (wo x) a; single_fill (wo x) (VPtr (Major a));
    tc_storable [VPtr (Major a)]; mutator_of x (EAlloc 1 0 [VPtr (Major a)])

let young_alloc_ok (sty: style) (x: config tc) (a: nat)
  : Lemma (requires x.stopped == false /\ Some? (tyalloc x.w.cyng 1 0 [VPtr (Major a)]) /\ major_ok_b (wo x) a == true /\
                    (Sequential? sty ==> Idle? x.ph))
          (ensures (let e = EYoungAlloc 1 0 [VPtr (Major a)] in enabled tc x e /\ style_ok sty x e /\ mutator_ok x e))
  = major_ok (wo x) a; single_fill (wo x) (VPtr (Major a));
    tc_storable [VPtr (Major a)]; mutator_of x (EYoungAlloc 1 0 [VPtr (Major a)])

/// A write to a major block through a root.
let write_major_ok (sty: style) (x: config tc) (o i: nat) (v: value)
  : Lemma (requires x.stopped == false /\ (Sequential? sty ==> Idle? x.ph) /\
                    is_block (wo x).maj o /\ root_b (wo x).maj (wo x).roots o == true /\ i < wz_of (wo x).maj o /\
                    tag_of (wo x).maj o <> closure_tag /\
                    (match v with VInt _ -> True | VPtr (Major a) -> major_ok_b (wo x) a == true | _ -> False))
          (ensures (let e = EWrite (Major o) i v in enabled tc x e /\ style_ok sty x e /\ mutator_ok x e))
  = reach_by_root (wo x) o;
    (match v with
     | VPtr (Major a) -> major_ok (wo x) a
     | _ -> ());
    tc_store v; mutator_of x (EWrite (Major o) i v)

let write_young_ok (sty: style) (x: config tc) (o i: nat) (a: nat)
  : Lemma (requires x.stopped == false /\ (Sequential? sty ==> Idle? x.ph) /\
                    is_block (wo x).yng o /\ yroot_b (wo x).yng (wo x).roots o == true /\ i < wz_of (wo x).yng o /\
                    tag_of (wo x).yng o <> closure_tag /\ major_ok_b (wo x) a == true)
          (ensures (let e = EWrite (Young o) i (VPtr (Major a)) in enabled tc x e /\ style_ok sty x e /\ mutator_ok x e))
  = yreach_by_root (wo x) o; major_ok (wo x) a;
    tc_store (VPtr (Major a)); mutator_of x (EWrite (Young o) i (VPtr (Major a)))

let rec roots_ok_b (w: world) (rs: list value) : bool =
  match rs with
  | [] -> true
  | VPtr (Major a) :: tl -> major_ok_b w a && roots_ok_b w tl
  | VInt _ :: tl -> roots_ok_b w tl
  | _ -> false

let rec roots_ok (w: world) (rs: list value)
  : Lemma (requires roots_ok_b w rs == true) (ensures forall (v: value). L.memP v rs ==> value_ok w v)
  = match rs with
    | [] -> ()
    | VPtr (Major a) :: tl -> major_ok w a; roots_ok w tl
    | VInt _ :: tl -> roots_ok w tl

let roots_step_ok (sty: style) (x: config tc) (rs: list value)
  : Lemma (requires x.stopped == false /\ (Sequential? sty ==> Idle? x.ph) /\ roots_ok_b (wo x) rs == true)
          (ensures (let e = ERoots rs in enabled tc x e /\ style_ok sty x e /\ mutator_ok x e))
  = roots_ok (wo x) rs; tc_storable rs; mutator_of x (ERoots rs)

/// A read of a field of a major block through a root.
let read_major_ok (sty: style) (x: config tc) (o i: nat)
  : Lemma (requires x.stopped == false /\ (Sequential? sty ==> Idle? x.ph) /\
                    is_block (wo x).maj o /\ root_b (wo x).maj (wo x).roots o == true /\ i < wz_of (wo x).maj o /\
                    scannable (tag_of (wo x).maj o))
          (ensures (let e = ERead (Major o) i in enabled tc x e /\ style_ok sty x e /\ mutator_ok x e))
  = reach_by_root (wo x) o; mutator_of x (ERead (Major o) i)

/// ---------------------------------------------------------------------------
/// The sequential run
/// ---------------------------------------------------------------------------

let len_seq () : Lemma (L.length es_seq == 17) = assert_nbe (L.length es_seq == 17)

#push-options "--z3rlimit 40"

let seq_step_2 () : Lemma (step_ok es_seq Sequential 2)
  = len_seq ();
    assert_nbe (ev es_seq 2 == EWrite (Major 0) 0 (VPtr (Major 2)));
    assert_nbe ((cs 2).stopped == false /\ Idle? (cs 2).ph /\ is_block (wo (cs 2)).maj 0 /\
                 root_b (wo (cs 2)).maj (wo (cs 2)).roots 0 == true /\ 0 < wz_of (wo (cs 2)).maj 0 /\
                 tag_of (wo (cs 2)).maj 0 <> closure_tag /\ major_ok_b (wo (cs 2)) 2 == true);
    write_major_ok Sequential (cs 2) 0 0 (VPtr (Major 2))

let seq_step_4 () : Lemma (step_ok es_seq Sequential 4)
  = len_seq ();
    assert_nbe (ev es_seq 4 == EYoungAlloc 1 0 [VPtr (Major 0)]);
    assert_nbe ((cs 4).stopped == false /\ Idle? (cs 4).ph /\ Some? (tyalloc (cs 4).w.cyng 1 0 [VPtr (Major 0)]) /\
                 major_ok_b (wo (cs 4)) 0 == true);
    young_alloc_ok Sequential (cs 4) 0

let seq_step_5 () : Lemma (step_ok es_seq Sequential 5)
  = len_seq ();
    assert_nbe (ev es_seq 5 == EWrite (Young 0) 0 (VPtr (Major 2)));
    assert_nbe ((cs 5).stopped == false /\ Idle? (cs 5).ph /\ is_block (wo (cs 5)).yng 0 /\
                 yroot_b (wo (cs 5)).yng (wo (cs 5)).roots 0 == true /\ 0 < wz_of (wo (cs 5)).yng 0 /\
                 tag_of (wo (cs 5)).yng 0 <> closure_tag /\ major_ok_b (wo (cs 5)) 2 == true);
    write_young_ok Sequential (cs 5) 0 0 2

let seq_step_6 () : Lemma (step_ok es_seq Sequential 6)
  = len_seq ();
    assert_nbe (ev es_seq 6 == ERoots [VPtr (Major 0)]);
    assert_nbe ((cs 6).stopped == false /\ Idle? (cs 6).ph /\ roots_ok_b (wo (cs 6)) [VPtr (Major 0)] == true);
    roots_step_ok Sequential (cs 6) [VPtr (Major 0)]

let seq_step_0 () : Lemma (step_ok es_seq Sequential 0)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 0) (ev es_seq 0) == true);
    simple_step es_seq Sequential 0

let seq_step_1 () : Lemma (step_ok es_seq Sequential 1)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 1) (ev es_seq 1) == true);
    simple_step es_seq Sequential 1

let seq_step_3 () : Lemma (step_ok es_seq Sequential 3)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 3) (ev es_seq 3) == true);
    simple_step es_seq Sequential 3

let seq_step_7 () : Lemma (step_ok es_seq Sequential 7)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 7) (ev es_seq 7) == true);
    simple_step es_seq Sequential 7

let seq_step_8 () : Lemma (step_ok es_seq Sequential 8)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 8) (ev es_seq 8) == true);
    simple_step es_seq Sequential 8

let seq_step_9 () : Lemma (step_ok es_seq Sequential 9)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 9) (ev es_seq 9) == true);
    simple_step es_seq Sequential 9

let seq_step_10 () : Lemma (step_ok es_seq Sequential 10)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 10) (ev es_seq 10) == true);
    simple_step es_seq Sequential 10

let seq_step_11 () : Lemma (step_ok es_seq Sequential 11)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 11) (ev es_seq 11) == true);
    simple_step es_seq Sequential 11

let seq_step_12 () : Lemma (step_ok es_seq Sequential 12)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 12) (ev es_seq 12) == true);
    simple_step es_seq Sequential 12

let seq_step_13 () : Lemma (step_ok es_seq Sequential 13)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 13) (ev es_seq 13) == true);
    simple_step es_seq Sequential 13

let seq_step_14 () : Lemma (step_ok es_seq Sequential 14)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 14) (ev es_seq 14) == true);
    simple_step es_seq Sequential 14

let seq_step_15 () : Lemma (step_ok es_seq Sequential 15)
  = len_seq ();
    assert_nbe (ev es_seq 15 == ERead (Major 0) 0);
    assert_nbe ((cs 15).stopped == false /\ Idle? (cs 15).ph /\ is_block (wo (cs 15)).maj 0 /\
                 root_b (wo (cs 15)).maj (wo (cs 15)).roots 0 == true /\ 0 < wz_of (wo (cs 15)).maj 0 /\
                 scannable (tag_of (wo (cs 15)).maj 0));
    read_major_ok Sequential (cs 15) 0 0

#pop-options

let seq_step_16 () : Lemma (step_ok es_seq Sequential 16)
  = len_seq ();
    assert_nbe (simple_b Sequential (cs 16) (ev es_seq 16) == true);
    simple_step es_seq Sequential 16

let seq_step (i: nat{i < 17}) : Lemma (step_ok es_seq Sequential i)
  = match i with
    | 2 -> seq_step_2 ()
    | 4 -> seq_step_4 ()
    | 5 -> seq_step_5 ()
    | 6 -> seq_step_6 ()
    | 0 -> seq_step_0 ()
    | 1 -> seq_step_1 ()
    | 3 -> seq_step_3 ()
    | 7 -> seq_step_7 ()
    | 8 -> seq_step_8 ()
    | 9 -> seq_step_9 ()
    | 10 -> seq_step_10 ()
    | 11 -> seq_step_11 ()
    | 12 -> seq_step_12 ()
    | 13 -> seq_step_13 ()
    | 14 -> seq_step_14 ()
    | 15 -> seq_step_15 ()
    | 16 -> seq_step_16 ()

let seq_run_ok () : Lemma (run_ok tc Sequential n_heap n_young es_seq)
  = len_seq ();
    let f (i: nat) : Lemma (i < L.length es_seq ==> step_ok es_seq Sequential i)
      = if i < 17 then seq_step i in
    FStar.Classical.forall_intro f;
    tc_sizes n_heap n_young

/// ---------------------------------------------------------------------------
/// The incremental run
/// ---------------------------------------------------------------------------

let len_inc () : Lemma (L.length es_inc == 23) = assert_nbe (L.length es_inc == 23)

#push-options "--z3rlimit 40"

let inc_step_2 () : Lemma (step_ok es_inc Incremental 2)
  = len_inc ();
    assert_nbe (ev es_inc 2 == EWrite (Major 0) 0 (VPtr (Major 2)));
    assert_nbe ((ci 2).stopped == false /\ is_block (wo (ci 2)).maj 0 /\
                 root_b (wo (ci 2)).maj (wo (ci 2)).roots 0 == true /\ 0 < wz_of (wo (ci 2)).maj 0 /\
                 tag_of (wo (ci 2)).maj 0 <> closure_tag /\ major_ok_b (wo (ci 2)) 2 == true);
    write_major_ok Incremental (ci 2) 0 0 (VPtr (Major 2))

let inc_step_4 () : Lemma (step_ok es_inc Incremental 4)
  = len_inc ();
    assert_nbe (ev es_inc 4 == EYoungAlloc 1 0 [VPtr (Major 0)]);
    assert_nbe ((ci 4).stopped == false /\ Some? (tyalloc (ci 4).w.cyng 1 0 [VPtr (Major 0)]) /\
                 major_ok_b (wo (ci 4)) 0 == true);
    young_alloc_ok Incremental (ci 4) 0

let inc_step_5 () : Lemma (step_ok es_inc Incremental 5)
  = len_inc ();
    assert_nbe (ev es_inc 5 == EWrite (Young 0) 0 (VPtr (Major 2)));
    assert_nbe ((ci 5).stopped == false /\ is_block (wo (ci 5)).yng 0 /\
                 yroot_b (wo (ci 5)).yng (wo (ci 5)).roots 0 == true /\ 0 < wz_of (wo (ci 5)).yng 0 /\
                 tag_of (wo (ci 5)).yng 0 <> closure_tag /\ major_ok_b (wo (ci 5)) 2 == true);
    write_young_ok Incremental (ci 5) 0 0 2

let inc_step_6 () : Lemma (step_ok es_inc Incremental 6)
  = len_inc ();
    assert_nbe (ev es_inc 6 == ERoots [VPtr (Major 0)]);
    assert_nbe ((ci 6).stopped == false /\ roots_ok_b (wo (ci 6)) [VPtr (Major 0)] == true);
    roots_step_ok Incremental (ci 6) [VPtr (Major 0)]

let inc_step_8 () : Lemma (step_ok es_inc Incremental 8)
  = len_inc ();
    assert_nbe (ev es_inc 8 == EAlloc 1 0 [VPtr (Major 2)]);
    assert_nbe ((ci 8).stopped == false /\ major_ok_b (wo (ci 8)) 2 == true);
    alloc_ptr_ok Incremental (ci 8) 2

let inc_step_9 () : Lemma (step_ok es_inc Incremental 9)
  = len_inc ();
    assert_nbe (ev es_inc 9 == EWrite (Major 0) 0 (VInt 5));
    assert_nbe ((ci 9).stopped == false /\ is_block (wo (ci 9)).maj 0 /\
                 root_b (wo (ci 9)).maj (wo (ci 9)).roots 0 == true /\ 0 < wz_of (wo (ci 9)).maj 0 /\
                 tag_of (wo (ci 9)).maj 0 <> closure_tag);
    write_major_ok Incremental (ci 9) 0 0 (VInt 5)

let inc_step_13 () : Lemma (step_ok es_inc Incremental 13)
  = len_inc ();
    assert_nbe (ev es_inc 13 == EAlloc 1 0 [VPtr (Major 6)]);
    assert_nbe ((ci 13).stopped == false /\ major_ok_b (wo (ci 13)) 6 == true);
    alloc_ptr_ok Incremental (ci 13) 6

let inc_step_14 () : Lemma (step_ok es_inc Incremental 14)
  = len_inc ();
    assert_nbe (ev es_inc 14 == EWrite (Major 6) 0 (VPtr (Major 0)));
    assert_nbe ((ci 14).stopped == false /\ is_block (wo (ci 14)).maj 6 /\
                 root_b (wo (ci 14)).maj (wo (ci 14)).roots 6 == true /\ 0 < wz_of (wo (ci 14)).maj 6 /\
                 tag_of (wo (ci 14)).maj 6 <> closure_tag /\ major_ok_b (wo (ci 14)) 0 == true);
    write_major_ok Incremental (ci 14) 6 0 (VPtr (Major 0))

let inc_step_15 () : Lemma (step_ok es_inc Incremental 15)
  = len_inc ();
    assert_nbe (ev es_inc 15 == ERoots [VPtr (Major 8); VPtr (Major 0)]);
    assert_nbe ((ci 15).stopped == false /\ roots_ok_b (wo (ci 15)) [VPtr (Major 8); VPtr (Major 0)] == true);
    roots_step_ok Incremental (ci 15) [VPtr (Major 8); VPtr (Major 0)]

let inc_step_0 () : Lemma (step_ok es_inc Incremental 0)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 0) (ev es_inc 0) == true);
    simple_step es_inc Incremental 0

let inc_step_1 () : Lemma (step_ok es_inc Incremental 1)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 1) (ev es_inc 1) == true);
    simple_step es_inc Incremental 1

let inc_step_3 () : Lemma (step_ok es_inc Incremental 3)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 3) (ev es_inc 3) == true);
    simple_step es_inc Incremental 3

let inc_step_7 () : Lemma (step_ok es_inc Incremental 7)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 7) (ev es_inc 7) == true);
    simple_step es_inc Incremental 7

let inc_step_10 () : Lemma (step_ok es_inc Incremental 10)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 10) (ev es_inc 10) == true);
    simple_step es_inc Incremental 10

let inc_step_11 () : Lemma (step_ok es_inc Incremental 11)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 11) (ev es_inc 11) == true);
    simple_step es_inc Incremental 11

let inc_step_12 () : Lemma (step_ok es_inc Incremental 12)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 12) (ev es_inc 12) == true);
    simple_step es_inc Incremental 12

let inc_step_16 () : Lemma (step_ok es_inc Incremental 16)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 16) (ev es_inc 16) == true);
    simple_step es_inc Incremental 16

let inc_step_17 () : Lemma (step_ok es_inc Incremental 17)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 17) (ev es_inc 17) == true);
    simple_step es_inc Incremental 17

let inc_step_18 () : Lemma (step_ok es_inc Incremental 18)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 18) (ev es_inc 18) == true);
    simple_step es_inc Incremental 18

let inc_step_19 () : Lemma (step_ok es_inc Incremental 19)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 19) (ev es_inc 19) == true);
    simple_step es_inc Incremental 19

let inc_step_20 () : Lemma (step_ok es_inc Incremental 20)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 20) (ev es_inc 20) == true);
    simple_step es_inc Incremental 20

let inc_step_21 () : Lemma (step_ok es_inc Incremental 21)
  = len_inc ();
    assert_nbe (ev es_inc 21 == ERead (Major 0) 0);
    assert_nbe ((ci 21).stopped == false /\ is_block (wo (ci 21)).maj 0 /\
                 root_b (wo (ci 21)).maj (wo (ci 21)).roots 0 == true /\ 0 < wz_of (wo (ci 21)).maj 0 /\
                 scannable (tag_of (wo (ci 21)).maj 0));
    read_major_ok Incremental (ci 21) 0 0

let inc_step_22 () : Lemma (step_ok es_inc Incremental 22)
  = len_inc ();
    assert_nbe (simple_b Incremental (ci 22) (ev es_inc 22) == true);
    simple_step es_inc Incremental 22

#pop-options

let inc_step (i: nat{i < 23}) : Lemma (step_ok es_inc Incremental i)
  = match i with
    | 2 -> inc_step_2 ()
    | 4 -> inc_step_4 ()
    | 5 -> inc_step_5 ()
    | 6 -> inc_step_6 ()
    | 8 -> inc_step_8 ()
    | 9 -> inc_step_9 ()
    | 13 -> inc_step_13 ()
    | 14 -> inc_step_14 ()
    | 15 -> inc_step_15 ()
    | 0 -> inc_step_0 ()
    | 1 -> inc_step_1 ()
    | 3 -> inc_step_3 ()
    | 7 -> inc_step_7 ()
    | 10 -> inc_step_10 ()
    | 11 -> inc_step_11 ()
    | 12 -> inc_step_12 ()
    | 16 -> inc_step_16 ()
    | 17 -> inc_step_17 ()
    | 18 -> inc_step_18 ()
    | 19 -> inc_step_19 ()
    | 20 -> inc_step_20 ()
    | 21 -> inc_step_21 ()
    | 22 -> inc_step_22 ()

let inc_run_ok () : Lemma (run_ok tc Incremental n_heap n_young es_inc)
  = len_inc ();
    let f (i: nat) : Lemma (i < L.length es_inc ==> step_ok es_inc Incremental i)
      = if i < 23 then inc_step i in
    FStar.Classical.forall_intro f;
    tc_sizes n_heap n_young

/// ---------------------------------------------------------------------------
/// Every hypothesis holds
/// ---------------------------------------------------------------------------

let run_hyps_of_ok (n ny: nat) (es: list event)
  : Lemma (requires components_ok tc) (ensures run_hyps tc n ny es)
  = let f (i: nat) : Lemma (i < L.length es ==> hyps_at tc (at tc n ny es i) (ev es i))
      = if i < L.length es then hyps_of_ok tc (at tc n ny es i) (ev es i) in
    FStar.Classical.forall_intro f;
    assert (init_at tc.r tc.a n);
    assert (yinit_ok tc.r ny)

/// The hypotheses of gc_correct and gc_correct_local, for both styles.
let vacuity_sequential ()
  : Lemma (components_ok tc /\ run_ok tc Sequential n_heap n_young es_seq /\
           run_hyps tc n_heap n_young es_seq)
  = toy_components_ok (); seq_run_ok (); run_hyps_of_ok n_heap n_young es_seq

let vacuity_incremental ()
  : Lemma (components_ok tc /\ run_ok tc Incremental n_heap n_young es_inc /\
           run_hyps tc n_heap n_young es_inc)
  = toy_components_ok (); inc_run_ok (); run_hyps_of_ok n_heap n_young es_inc

/// Every event occurs in each run.
let every_event (es: list event) : bool =
  L.existsb EAlloc? es && L.existsb EYoungAlloc? es && L.existsb EWrite? es && L.existsb ERead? es &&
  L.existsb ERoots? es &&
  L.existsb EMinor? es && L.existsb EStart? es && L.existsb ESlice? es && L.existsb EHandover? es &&
  L.existsb ESweep? es && L.existsb EEnd? es

let every_event_occurs () : Lemma (every_event es_seq /\ every_event es_inc)
  = assert_nbe (every_event es_seq /\ every_event es_inc)

/// Mutator events while marking and while sweeping, in the incremental run.
let ev_is (es: list event) (k: nat) (f: event -> bool) : bool =
  match L.nth es k with Some e -> f e | None -> false

let incremental_interleaves ()
  : Lemma (Marking? (ci 8).ph /\ ev_is es_inc 8 EAlloc? /\ Marking? (ci 9).ph /\ ev_is es_inc 9 EWrite? /\
           Sweeping? (ci 13).ph /\ ev_is es_inc 13 EAlloc? /\ Sweeping? (ci 14).ph /\ ev_is es_inc 14 EWrite?)
  = assert_nbe (Marking? (ci 8).ph /\ ev_is es_inc 8 EAlloc? /\ Marking? (ci 9).ph /\ ev_is es_inc 9 EWrite? /\
                Sweeping? (ci 13).ph /\ ev_is es_inc 13 EAlloc? /\ Sweeping? (ci 14).ph /\ ev_is es_inc 14 EWrite?)

/// ---------------------------------------------------------------------------
/// Non-triviality: at the cycle's start, a root, reachable objects (A, and B
/// only through a field), and an object in use that is unreachable (C)
/// ---------------------------------------------------------------------------

let all_below (n: nat) (f: nat -> bool) : bool = not (exists_below n (fun i -> not (f i)))

let all_below_elim (n: nat) (f: nat -> bool)
  : Lemma (requires all_below n f == true) (ensures forall (i: nat). i < n ==> f i == true)
  = exists_below_iff n (fun i -> not (f i))

let resolve_block (h: mheap) (a o: nat) : Lemma (resolve h a == Some o ==> o < h.size) = ()

let in02 (b: nat -> bool) (x: nat) : bool = not (b x) || x = 0 || x = 2

let c_unreachable_at_start ()
  : Lemma (let w = (wo (cs 7)) in
           L.memP (VPtr (Major 0)) w.roots /\ reachable w 0 /\ reachable w 2 /\
           in_use toy (cs 7).ast w.maj w.maj 4 == true /\ ~(reachable w 4))
  = let w = (wo (cs 7)) in
    assert_nbe (root_b (wo (cs 7)).maj (wo (cs 7)).roots 0 == true /\ young_b (wo (cs 7)) 2 == true /\ L.memP (VPtr (Major 0)) (wo (cs 7)).roots /\
                 in_use toy (cs 7).ast (wo (cs 7)).maj (wo (cs 7)).maj 4 == true);
    reach_by_root w 0;
    reach_by_young w 2;
    (* reachable is within {0, 2}: outside_refs are, and so are their fields *)
    let s (o: nat) : prop = o == 0 \/ o == 2 in
    assert_nbe (all_below 12 (in02 (outside_b (wo (cs 7)))) == true);
    assert_nbe (all_below 12 (in02 (edge_b (wo (cs 7)).maj 0)) == true);
    assert_nbe (all_below 12 (in02 (edge_b (wo (cs 7)).maj 2)) == true);
    assert_nbe ((wo (cs 7)).maj.size == 12);
    all_below_elim 12 (in02 (outside_b (wo (cs 7))));
    all_below_elim 12 (in02 (edge_b (wo (cs 7)).maj 0));
    all_below_elim 12 (in02 (edge_b (wo (cs 7)).maj 2));
    let out (x: nat) : Lemma (outside_ref w x ==> s x)
      = outside_b_iff w x;
        if FStar.IndefiniteDescription.strong_excluded_middle (outside_ref w x) then begin
          let a = FStar.IndefiniteDescription.indefinite_description_ghost nat
                    (fun a -> resolve w.maj a == Some x) in
          resolve_block w.maj a x
        end in
    FStar.Classical.forall_intro out;
    let edg (x x': nat) : Lemma (s x /\ major_edge w.maj x x' ==> s x')
      = edge_b_iff w.maj x x';
        if FStar.IndefiniteDescription.strong_excluded_middle (s x /\ major_edge w.maj x x') then begin
          let a = FStar.IndefiniteDescription.indefinite_description_ghost nat
                    (fun a -> resolve w.maj a == Some x') in
          resolve_block w.maj a x'
        end in
    FStar.Classical.forall_intro_2 edg;
    let aux (r: reach w 4) : Lemma False = reach_within w s 4 r in
    FStar.Classical.forall_intro aux
