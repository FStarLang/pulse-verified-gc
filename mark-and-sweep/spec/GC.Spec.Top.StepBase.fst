/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StepBase - what a step lemma proves, on a world of its choice
/// ---------------------------------------------------------------------------
///
/// Design doc §16.1.  A step lemma proves, for one event from `x` to
/// `x' = step c x e`, the invariant at `x'`, the clauses of `concl_step` and
/// `rback` (no object in use before becomes reachable: what (3c) needs).  The
/// contract of the event hands back some model `m'` of the new heap; the
/// lemma works on a world `w'` built from it, which views `x'`, and
/// `step_out_intro` moves everything to `vw x'` (GC.Spec.Top.Views).  The old
/// side is always `vw x` itself.

module GC.Spec.Top.StepBase

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// `concl_step`, with `vw x'` replaced by a world `w'`
/// ---------------------------------------------------------------------------

/// (1a) for a kept block.
let contents_w (#c: comps) (x: config c) (e: event) (w': world) (o: nat) : prop =
  let h = mj x in
  let h' = w'.maj in
  wz_of h' o == wz_of h o /\ tag_of h' o == tag_of h o /\
  (match e with
   | EWrite (Major t) i v ->
     (forall (j: nat). j < wz_of h o ==> field h' o j == (if o = t && j = i then v else field h o j))
   | EMinor ->
     (match c.n.collect x.ph x.ast x.w with
      | Done _ _ _ fwd -> (forall (j: nat). j < wz_of h o ==> field h' o j == fwd_field h o j (wv x).yng fwd)
      | OutOfRoom -> (forall (j: nat). j < wz_of h o ==> field h' o j == field h o j))
   | _ -> (forall (j: nat). j < wz_of h o ==> field h' o j == field h o j))

[@@"opaque_to_smt"]
let cs_keep (#c: comps) (x: config c) (e: event) (x': config c) (w': world) : prop =
  forall (o: nat). kept x o ==> iu x' w'.maj o == true /\ contents_w x e w' o

let alloc_w (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (x': config c) (w': world)
  : prop =
  let (_, _, r) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
  (Ok? r <==> c.a.room x.ph x.ast x.w.cmaj sz == true) /\
  (match r with
   | NoRoom -> x' == x
   | Ok o ->
     in_use_c x o == false /\ iu x' w'.maj o == true /\ kept_w x' w' o /\
     w'.maj.hd o == Some ({ wz = sz; tag = tag; col = colour_at c.k x.ph o }) /\
     (forall (i: nat). i < sz /\ i < L.length vs ==> field w'.maj o i == L.index vs i) /\
     (forall (y: nat). y <> o ==> (iu x' w'.maj y == in_use_c x y)))

[@@"opaque_to_smt"]
let cs_alloc (#c: comps) (x: config c) (e: event) (x': config c) (w': world) : prop =
  match e with EAlloc sz tag vs -> alloc_w x sz tag vs x' w' | _ -> True

/// The read clause and (3d) read only `x`.
let cs_old (#c: comps) (x: config c) (e: event) (x': config c) : prop =
  (match e with
   | ERead (Major o) i -> x'.w.croots == field (mj x) o i :: x.w.croots
   | ERead (Young o) i -> x'.w.croots == field (wv x).yng o i :: x.w.croots
   | _ -> True) /\
  (match e with
   | EMinor -> (match c.n.collect x.ph x.ast x.w with
               | Done _ _ _ fwd -> (forall (o: nat). Some? (fwd o) ==> minor_live (wv x) o)
               | OutOfRoom -> True)
   | _ -> True) /\
  (match x.ph, x'.ph with
   | Sweeping p, Sweeping p' ->
     (ESweep? e ==> (forall (o: nat). c.k.unswept p' o ==> c.k.unswept p o) /\
                    (exists (o: nat). o < (mj x).size /\ region c.k p p' o)) /\
     (~(ESweep? e) ==> p' == p)
   | _ -> True)

let free_w (#c: comps) (x: config c) (w: world) (n: nat) : prop = free_word c.a x.ast x.w.cmaj w.maj n
let used_w (#c: comps) (x: config c) (w: world) (n: nat) : prop = in_use_word c.a x.ast x.w.cmaj w.maj n

/// (5) the moves of words.
[@@"opaque_to_smt"]
let cs_words (#c: comps) (x: config c) (e: event) (x': config c) (w': world) : prop =
  forall (n: nat). n < (mj x).size ==>
    (in_use_word_c x n /\ free_w x' w' n ==> ESweep? e) /\
    (free_word_c x n /\ used_w x' w' n ==> EAlloc? e \/ EMinor? e)

/// (6) the mark's measure.
[@@"opaque_to_smt"]
let cs_mark (#c: comps) (x: config c) (e: event) (x': config c) (w': world) : prop =
  Marking? x.ph /\ Marking? x'.ph ==>
    (ESlice? e ==> mark_dec (mj x) (scan_of x) w'.maj (scan_of x') (live x')) /\
    (~(ESlice? e) ==> mark_noinc (mj x) (scan_of x) w'.maj (scan_of x') (live x'))

/// No object in use before the step becomes reachable (what (3c) needs).
[@@"opaque_to_smt"]
let rback_w (#c: comps) (x: config c) (w': world) : prop =
  forall (o: nat). reachable w' o /\ in_use_c x o == true ==> reachable (vw x) o

let rback (#c: comps) (x x': config c) : prop =
  forall (o: nat). reachable (vw x') o /\ in_use_c x o == true ==> reachable (vw x) o

/// What the cycle clauses (3a), (3b), (4) need of one step: an allocated
/// block was not in use, a block that comes into use is allocated, a block
/// that stays in use keeps its size, and a block that leaves use leaves its
/// words free.
[@@"opaque_to_smt"]
let cs_cyc (#c: comps) (x x': config c) (w': world) : prop =
  w'.maj.size == (mj x).size /\
  (forall (p: nat). x'.allocd p ==> x.allocd p \/ in_use_c x p == false) /\
  (forall (y: nat). iu x' w'.maj y == true /\ in_use_c x y == false ==> x'.allocd y) /\
  (forall (o: nat). in_use_c x o == true /\ iu x' w'.maj o == true ==> wz_of w'.maj o == wz_of (mj x) o) /\
  (forall (o n: nat). in_use_c x o == true /\ iu x' w'.maj o == false /\ covers (mj x) o n ==> free_w x' w' n)

let cyc (#c: comps) (x x': config c) : prop =
  (mj x').size == (mj x).size /\
  (forall (p: nat). x'.allocd p ==> x.allocd p \/ in_use_c x p == false) /\
  (forall (y: nat). in_use_c x' y == true /\ in_use_c x y == false ==> x'.allocd y) /\
  (forall (o: nat). in_use_c x o == true /\ in_use_c x' o == true ==> wz_of (mj x') o == wz_of (mj x) o) /\
  (forall (o n: nat). in_use_c x o == true /\ in_use_c x' o == false /\ covers (mj x) o n ==> free_word_c x' n)

/// Everything a step lemma proves.
let step_out (#c: comps) (x: config c) (e: event) (x': config c) (w': world) : prop =
  views x' w' /\ rinv_w x' w' /\
  cs_keep x e x' w' /\ cs_alloc x e x' w' /\ cs_old x e x' /\ cs_words x e x' w' /\ cs_mark x e x' w' /\
  rback_w x w' /\ cs_cyc x x' w'

/// ---------------------------------------------------------------------------
/// To `vw x'`
/// ---------------------------------------------------------------------------

let ag_contents (#c: comps) (x: config c) (e: event) (w1 w2: world) (o: nat)
  : Lemma (requires agree w1.maj w2.maj /\ is_block w1.maj o /\ contents_w x e w1 o)
          (ensures contents_w x e w2 o)
  = ag_hd w1.maj w2.maj o;
    C.forall_intro (C.move_requires (ag_field w1.maj w2.maj o))

let ag_cs_keep1 (#c: comps) (x: config c) (e: event) (x': config c) (w1 w2: world) (o: nat)
  : Lemma (requires agree w1.maj w2.maj /\ cs_keep x e x' w1 /\ kept x o)
          (ensures iu x' w2.maj o == true /\ contents_w x e w2 o)
  = reveal_opaque (`%cs_keep) (cs_keep #c);
    ag_iu x' w1.maj w2.maj o;
    ag_contents x e w1 w2 o

let ag_cs_keep (#c: comps) (x: config c) (e: event) (x': config c) (w1 w2: world)
  : Lemma (requires agree w1.maj w2.maj /\ cs_keep x e x' w1) (ensures cs_keep x e x' w2)
  = C.forall_intro (C.move_requires (ag_cs_keep1 x e x' w1 w2));
    reveal_opaque (`%cs_keep) (cs_keep #c)

#push-options "--z3rlimit 40"
let ag_alloc_w (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (x': config c)
    (w1 w2: world)
  : Lemma (requires agree w1.maj w2.maj /\ alloc_w x sz tag vs x' w1) (ensures alloc_w x sz tag vs x' w2)
  = let (_, _, r) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
    match r with
    | NoRoom -> ()
    | Ok o ->
      ag_iu x' w1.maj w2.maj o;
      C.forall_intro (fun (y: nat) -> ag_iu x' w1.maj w2.maj y);
      C.forall_intro (C.move_requires (ag_field w1.maj w2.maj o))
#pop-options

let ag_cs_alloc (#c: comps) (x: config c) (e: event) (x': config c) (w1 w2: world)
  : Lemma (requires agree w1.maj w2.maj /\ cs_alloc x e x' w1) (ensures cs_alloc x e x' w2)
  = reveal_opaque (`%cs_alloc) (cs_alloc #c);
    match e with EAlloc sz tag vs -> ag_alloc_w x sz tag vs x' w1 w2 | _ -> ()

let ag_cs_words (#c: comps) (x: config c) (e: event) (x': config c) (w1 w2: world)
  : Lemma (requires agree w1.maj w2.maj /\ cs_words x e x' w1) (ensures cs_words x e x' w2)
  = reveal_opaque (`%cs_words) (cs_words #c);
    C.forall_intro (fun (n: nat) -> ag_free_word c.a x'.ast x'.w.cmaj w1.maj w2.maj n);
    C.forall_intro (fun (n: nat) -> ag_in_use_word c.a x'.ast x'.w.cmaj w1.maj w2.maj n)

let ag_cs_mark (#c: comps) (x: config c) (e: event) (x': config c) (w1 w2: world)
  : Lemma (requires agree w1.maj w2.maj /\ cs_mark x e x' w1) (ensures cs_mark x e x' w2)
  = reveal_opaque (`%cs_mark) (cs_mark #c);
    agree_refl (mj x);
    ag_dec (mj x) w1.maj (mj x) w2.maj (scan_of x) (scan_of x') (live x')

let ag_rback (#c: comps) (x: config c) (w1 w2: world)
  : Lemma (requires wagree w1 w2 /\ rback_w x w1) (ensures rback_w x w2)
  = reveal_opaque (`%rback_w) (rback_w #c);
    wagree_sym w1 w2;
    C.forall_intro (C.move_requires (ag_reachable w2 w1))

let keep_concl (#c: comps) (x: config c) (e: event) (x': config c) (o: nat)
  : Lemma (requires cs_keep x e x' (vw x') /\ kept x o) (ensures in_use_c x' o == true /\ contents_step x e x' o)
  = reveal_opaque (`%cs_keep) (cs_keep #c)

let alloc_concl (#c: comps) (x: config c) (e: event) (x': config c)
  : Lemma (requires cs_alloc x e x' (vw x'))
          (ensures (match e with EAlloc sz tag vs -> alloc_step x sz tag vs x' | _ -> True))
  = reveal_opaque (`%cs_alloc) (cs_alloc #c)

let words_concl (#c: comps) (x: config c) (e: event) (x': config c) (n: nat)
  : Lemma (requires cs_words x e x' (vw x') /\ n < (mj x).size)
          (ensures (in_use_word_c x n /\ free_word_c x' n ==> ESweep? e) /\
                   (free_word_c x n /\ in_use_word_c x' n ==> EAlloc? e \/ EMinor? e))
  = reveal_opaque (`%cs_words) (cs_words #c)

let mark_concl (#c: comps) (x: config c) (e: event) (x': config c)
  : Lemma (requires cs_mark x e x' (vw x'))
          (ensures Marking? x.ph /\ Marking? x'.ph ==>
                     (ESlice? e ==> mark_dec (mj x) (scan_of x) (mj x') (scan_of x') (live x')) /\
                     (~(ESlice? e) ==> mark_noinc (mj x) (scan_of x) (mj x') (scan_of x') (live x')))
  = reveal_opaque (`%cs_mark) (cs_mark #c)

let concl_of_cs (#c: comps) (x: config c) (e: event) (x': config c)
  : Lemma (requires cs_keep x e x' (vw x') /\ cs_alloc x e x' (vw x') /\ cs_old x e x' /\
                    cs_words x e x' (vw x') /\ cs_mark x e x' (vw x'))
          (ensures concl_step x e x')
  = C.forall_intro (C.move_requires (keep_concl x e x'));
    alloc_concl x e x';
    C.forall_intro (C.move_requires (words_concl x e x'));
    mark_concl x e x'

let ag_cyc1 (#c: comps) (x x': config c) (w1: world) (o: nat)
  : Lemma (requires agree w1.maj (mj x') /\ cs_cyc x x' w1)
          (ensures (x'.allocd o ==> x.allocd o \/ in_use_c x o == false) /\
                   (in_use_c x' o == true /\ in_use_c x o == false ==> x'.allocd o) /\
                   (in_use_c x o == true /\ in_use_c x' o == true ==> wz_of (mj x') o == wz_of (mj x) o) /\
                   (forall (n: nat). in_use_c x o == true /\ in_use_c x' o == false /\ covers (mj x) o n ==>
                      free_word_c x' n))
  = reveal_opaque (`%cs_cyc) (cs_cyc #c);
    ag_iu x' w1.maj (mj x') o;
    ag_hd w1.maj (mj x') o;
    C.forall_intro (fun (n: nat) -> ag_free_word c.a x'.ast x'.w.cmaj w1.maj (mj x') n)

let ag_cyc (#c: comps) (x x': config c) (w1: world)
  : Lemma (requires agree w1.maj (mj x') /\ cs_cyc x x' w1) (ensures cyc x x')
  = C.forall_intro (ag_cyc1 x x' w1);
    reveal_opaque (`%cs_cyc) (cs_cyc #c)

/// **A step lemma's result, at `vw x'`.**
let step_out_intro (#c: comps) (x: config c) (e: event) (x': config c) (w': world)
  : Lemma (requires faithful c.r /\ step_out x e x' w')
          (ensures rinv x' /\ concl_step x e x' /\ rback x x' /\ cyc x x')
  = vw_agree x' w';
    let w2 = vw x' in
    rinv_w_agree x' w' w2;
    ag_cs_keep x e x' w' w2; ag_cs_alloc x e x' w' w2; ag_cs_words x e x' w' w2; ag_cs_mark x e x' w' w2;
    concl_of_cs x e x';
    ag_rback x w' w2;
    reveal_opaque (`%rback_w) (rback_w #c);
    ag_cyc x x' w'

/// `cs_cyc` for a step that allocates nothing and keeps what is in use, and
/// the sizes of the blocks in use.
let cyc_same (#c: comps) (x x': config c) (w': world)
  : Lemma (requires (forall (p: nat). x'.allocd p ==> x.allocd p) /\ w'.maj.size == (mj x).size /\
                    (forall (o: nat). iu x' w'.maj o == in_use_c x o) /\
                    (forall (o: nat). in_use_c x o ==> wz_of w'.maj o == wz_of (mj x) o))
          (ensures cs_cyc x x' w')
  = reveal_opaque (`%cs_cyc) (cs_cyc #c)

/// The same, when the model agrees with the old one.
let cyc_agree (#c: comps) (x x': config c) (w': world)
  : Lemma (requires (forall (p: nat). x'.allocd p ==> x.allocd p) /\ agree (mj x) w'.maj /\
                    (forall (o: nat). c.a.free x'.ast x'.w.cmaj o == c.a.free x.ast x.w.cmaj o))
          (ensures cs_cyc x x' w')
  = C.forall_intro (fun (o: nat) -> ag_hd (mj x) w'.maj o);
    cyc_same x x' w'

/// ---------------------------------------------------------------------------
/// Common cases
/// ---------------------------------------------------------------------------

/// A step that leaves the major heap's model and the allocator alone.
let same_major (#c: comps) (x x': config c) (w': world) : prop =
  x'.ph == x.ph /\ x'.ast == x.ast /\ x'.w.cmaj == x.w.cmaj /\ x'.snap == x.snap /\ x'.allocd == x.allocd /\
  x'.ms == x.ms /\ agree (mj x) w'.maj

let same_iu (#c: comps) (x x': config c) (w': world) (o: nat)
  : Lemma (requires same_major x x' w') (ensures iu x' w'.maj o == in_use_c x o /\
                                                 (in_use_c x o ==> col_of w'.maj o == col_of (mj x) o))
  = ag_iu x (mj x) w'.maj o

let same_keep1 (#c: comps) (x: config c) (e: event) (x': config c) (w': world) (o: nat)
  : Lemma (requires same_major x x' w' /\ ~(EWrite? e /\ Major? (EWrite?.p e)) /\ ~(EMinor? e) /\ kept x o)
          (ensures iu x' w'.maj o == true /\ contents_w x e w' o)
  = same_iu x x' w' o;
    ag_hd (mj x) w'.maj o;
    C.forall_intro (C.move_requires (ag_field (mj x) w'.maj o))

let same_mark (#c: comps) (x: config c) (e: event) (x': config c) (w': world)
  : Lemma (requires same_major x x' w' /\ ~(ESlice? e)) (ensures cs_mark x e x' w')
  = C.forall_intro (fun (o: nat) -> ag_white_live (mj x) w'.maj (live x') o);
    ag_fleft (mj x) w'.maj (scan_of x);
    reveal_opaque (`%cs_mark) (cs_mark #c)

let same_word1 (#c: comps) (x: config c) (e: event) (x': config c) (w': world) (n: nat)
  : Lemma (requires same_major x x' w' /\ well_formed (mj x) /\ n < (mj x).size)
          (ensures (in_use_word_c x n /\ free_w x' w' n ==> ESweep? e) /\
                   (free_word_c x n /\ used_w x' w' n ==> EAlloc? e \/ EMinor? e))
  = ag_free_word c.a x.ast x.w.cmaj (mj x) w'.maj n;
    ag_in_use_word c.a x.ast x.w.cmaj (mj x) w'.maj n;
    word_xor c.a x.ast x.w.cmaj (mj x) n

let same_words (#c: comps) (x: config c) (e: event) (x': config c) (w': world)
  : Lemma (requires same_major x x' w' /\ well_formed (mj x)) (ensures cs_words x e x' w')
  = C.forall_intro (C.move_requires (same_word1 x e x' w'));
    reveal_opaque (`%cs_words) (cs_words #c)

let same_cs (#c: comps) (x: config c) (e: event) (x': config c) (w': world)
  : Lemma (requires same_major x x' w' /\ well_formed (mj x) /\ ~(EWrite? e /\ Major? (EWrite?.p e)) /\
                    ~(EMinor? e) /\ ~(EAlloc? e) /\ ~(ESlice? e))
          (ensures cs_keep x e x' w' /\ cs_alloc x e x' w' /\ cs_words x e x' w' /\ cs_mark x e x' w')
  = C.forall_intro (C.move_requires (same_keep1 x e x' w'));
    reveal_opaque (`%cs_keep) (cs_keep #c);
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    same_words x e x' w';
    same_mark x e x' w'

/// ---------------------------------------------------------------------------
/// Steps that keep every reachable block
/// ---------------------------------------------------------------------------

/// What a step that replaces the major heap's model by `w'.maj` (roots,
/// nursery and remembered set unchanged) must show: it keeps the reachable
/// blocks, kept, and the blocks the program may use afterwards it may use
/// before, and keeps them.
let heap_ok (#c: comps) (x x': config c) (w': world) : prop =
  let w = vw x in
  w'.yng == w.yng /\ w'.roots == w.roots /\ w'.rem == w.rem /\ unique_cover w'.maj /\
  (forall (o: nat). reachable w o ==> keeps w.maj w'.maj o /\ kept_w x' w' o) /\
  (forall (o: nat). live_target c.a x'.ph x'.ast x'.w.cmaj w'.maj o ==>
     live_target c.a x.ph x.ast x.w.cmaj w.maj o /\ keeps w.maj w'.maj o)

let heap_root (#c: comps) (x x': config c) (w': world) (a o: nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ L.memP (VPtr (Major a)) w'.roots /\ resolve w'.maj a == Some o)
          (ensures reachable (vw x) o)
  = let w = vw x in
    res_root w (VPtr (Major a));
    let o0 = Some?.v (resolve w.maj a) in
    reach_root w a o0;
    resolve_keep w.maj w'.maj a o0

let heap_yref (#c: comps) (x x': config c) (w': world) (o y i a: nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ ptr_field w'.yng y i /\ field w'.yng y i == VPtr (Major a) /\
                    resolve w'.maj a == Some o)
          (ensures reachable (vw x) o)
  = let w = vw x in
    res_yng w y i;
    let o0 = Some?.v (resolve w.maj a) in
    reach_young w y i a o0;
    resolve_keep w.maj w'.maj a o0

let heap_outside (#c: comps) (x x': config c) (w': world) (o: nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ outside_ref w' o) (ensures reachable (vw x) o)
  = if FStar.IndefiniteDescription.strong_excluded_middle (root_ref w' o) then begin
      eliminate exists (a: nat). L.memP (VPtr (Major a)) w'.roots /\ resolve w'.maj a == Some o
      with heap_root x x' w' a o
    end else begin
      eliminate exists (y i a: nat). ptr_field w'.yng y i /\ field w'.yng y i == VPtr (Major a) /\
                                     resolve w'.maj a == Some o
      with heap_yref x x' w' o y i a
    end

let heap_edge1 (#c: comps) (x x': config c) (w': world) (o o' i a: nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ reachable (vw x) o /\ ptr_field w'.maj o i /\
                    field w'.maj o i == VPtr (Major a) /\ resolve w'.maj a == Some o')
          (ensures reachable (vw x) o')
  = let w = vw x in
    assert (ptr_field w.maj o i /\ field w.maj o i == VPtr (Major a));
    res_maj w o i;
    let o0 = Some?.v (resolve w.maj a) in
    reach_field w o i a o0;
    resolve_keep w.maj w'.maj a o0

let heap_edge (#c: comps) (x x': config c) (w': world) (o o': nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ reachable (vw x) o /\ major_edge w'.maj o o')
          (ensures reachable (vw x) o')
  = C.forall_intro_2 (fun i a -> C.move_requires (heap_edge1 x x' w' o o' i) a)

let heap_reach (#c: comps) (x x': config c) (w': world) (o: nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ reachable w' o) (ensures reachable (vw x) o)
  = C.forall_intro (C.move_requires (heap_outside x x' w'));
    C.forall_intro_2 (fun a b -> C.move_requires (heap_edge x x' w' a) b);
    reachable_within w' (reachable (vw x)) o

/// A value of the old world that resolves to a reachable block, or is young.
let heap_resolves (#c: comps) (x x': config c) (w': world) (v: value)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ resolves (vw x) v /\
                    (match v with VPtr (Major a) -> reachable (vw x) (Some?.v (resolve (vw x).maj a)) | _ -> True))
          (ensures resolves w' v)
  = match v with
    | VPtr (Major a) -> resolve_keep (vw x).maj w'.maj a (Some?.v (resolve (vw x).maj a))
    | _ -> ()

let heap_res_root (#c: comps) (x x': config c) (w': world) (v: value)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ L.memP v w'.roots) (ensures resolves w' v)
  = let w = vw x in
    res_root w v;
    (match v with VPtr (Major a) -> reach_root w a (Some?.v (resolve w.maj a)) | _ -> ());
    heap_resolves x x' w' v

let heap_res_maj (#c: comps) (x x': config c) (w': world) (o i: nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ reachable w' o /\ ptr_field w'.maj o i)
          (ensures resolves w' (field w'.maj o i))
  = let w = vw x in
    heap_reach x x' w' o;
    assert (ptr_field w.maj o i /\ field w'.maj o i == field w.maj o i);
    res_maj w o i;
    (match field w.maj o i with VPtr (Major a) -> reach_field w o i a (Some?.v (resolve w.maj a)) | _ -> ());
    heap_resolves x x' w' (field w.maj o i)

let heap_res_yng (#c: comps) (x x': config c) (w': world) (o i: nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ ptr_field w'.yng o i) (ensures resolves w' (field w'.yng o i))
  = let w = vw x in
    res_yng w o i;
    (match field w.yng o i with VPtr (Major a) -> reach_young w o i a (Some?.v (resolve w.maj a)) | _ -> ());
    heap_resolves x x' w' (field w.yng o i)

let heap_young1 (#c: comps) (x x': config c) (w': world) (o i b: nat)
  : Lemma (requires rinv x /\ heap_ok x x' w' /\ live_target c.a x'.ph x'.ast x'.w.cmaj w'.maj o /\
                    ptr_field w'.maj o i /\ field w'.maj o i == VPtr (Young b))
          (ensures Some? (resolve w'.yng b) /\ L.memP (o, i) w'.rem)
  = reveal_opaque (`%r_young) (r_young #c);
    let w = vw x in
    assert (ptr_field w.maj o i /\ field w.maj o i == VPtr (Young b))

/// **The invariant's reachability parts, and `rback`, after such a step.**
let heap_step (#c: comps) (x x': config c) (w': world)
  : Lemma (requires rinv x /\ heap_ok x x' w')
          (ensures r_reach x' w' /\ r_res w' /\ r_young x' w' /\ rback_w x w')
  = C.forall_intro (C.move_requires (heap_reach x x' w'));
    reveal_opaque (`%r_reach) (r_reach #c);
    reveal_opaque (`%rback_w) (rback_w #c);
    C.forall_intro (C.move_requires (heap_res_root x x' w'));
    C.forall_intro_2 (fun o i -> C.move_requires (heap_res_maj x x' w' o) i);
    C.forall_intro_2 (fun o i -> C.move_requires (heap_res_yng x x' w' o) i);
    reveal_opaque (`%r_res) r_res;
    C.forall_intro_3 (fun o i b -> C.move_requires (heap_young1 x x' w' o i) b);
    reveal_opaque (`%r_young) (r_young #c)

/// `cs_keep` for an event other than a major write or a minor collection,
/// from: every kept block is in use after, and kept.
let keep_cs (#c: comps) (x: config c) (e: event) (x': config c) (w': world)
  : Lemma (requires ~(EWrite? e /\ Major? (EWrite?.p e)) /\ ~(EMinor? e) /\
                    (forall (o: nat). kept x o ==> iu x' w'.maj o == true /\ keeps (mj x) w'.maj o))
          (ensures cs_keep x e x' w')
  = reveal_opaque (`%cs_keep) (cs_keep #c)
