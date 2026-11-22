/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PromoteRun - what the promotion of GC.Spec.Pages.Promote
/// forwards, for any allocator
/// ---------------------------------------------------------------------------
///
/// The minor collection of GC.Spec.Pages.Promote (`promote`: the roots
/// forwarded, then the queue scanned) reports no failure: an allocation that
/// finds no room leaves the state as it was.  The minor collection of
/// GC.Spec.Top.Iface must report one, and justify it by an order of
/// promotion in which the allocator refuses.  For any allocator meeting
/// `Promote.contract`, every state of the loop carries, besides
/// `Promote.Loop.linv`:
///
///   * `qok`: the queue lists each forwarded object that is not infix,
///     once, in the order promoted, and the heap and the allocator's state
///     are the replay of its promotions (`replay`), each of which succeeded
///     with the copy the forwarding map records;
///   * `lv`: every object queued is live, for any `live` the roots justify
///     and that is closed under the fields scanned (`live_ok`);
///   * `wit` or closure: either some live object, not queued among the
///     first `k`, could not be promoted after them (`wit`: the allocator
///     refused at the replay of `k` promotions), or every root and every
///     field scanned so far is covered: its object forwarded, and an infix
///     address forwarded itself.
///
/// `promote_done`: at the end of promotion every queued object is live and
/// either `wit` holds or every root and every field of every queued object
/// is covered.  The queue fits in the nursery's objects, so the scan's fuel
/// suffices (`distinct_le`).

module GC.Spec.Top.PromoteRun

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Promote
open GC.Spec.Pages.Promote.Loop

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Replaying the queue
/// ---------------------------------------------------------------------------

/// One promotion (none for an object of no field).
let promote_at (#s: Type0) (a: tal s) (minor: minor_state) (g: heap) (st: s) (m: U64.t) : GTot (heap & s & U64.t) =
  let w = minor_wosize minor m in
  if w > 0 then promote_object a minor g m st w else (g, st, 0UL)

/// The heap and the state after promoting the first `k` objects of `q`.
let rec replay (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (q: seq U64.t) (k: nat)
  : GTot (heap & s) (decreases k) =
  if k = 0 || k > Seq.length q then (g0, st0)
  else
    let (g, st) = replay a minor g0 st0 q (k - 1) in
    let (g2, s2, _) = promote_at a minor g st (Seq.index q (k - 1)) in
    (g2, s2)

/// `q'` extends `q`.
let extends (q q': seq U64.t) : prop =
  Seq.length q <= Seq.length q' /\ (forall (j: nat). j < Seq.length q ==> Seq.index q' j == Seq.index q j)

#push-options "--fuel 1"
let rec replay_prefix (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (q q': seq U64.t) (k: nat)
  : Lemma (requires extends q q' /\ k <= Seq.length q)
          (ensures replay a minor g0 st0 q' k == replay a minor g0 st0 q k) (decreases k)
  = if k > 0 then replay_prefix a minor g0 st0 q q' (k - 1)

let replay_snoc (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (q: seq U64.t) (m: U64.t)
  : Lemma (let q' = Seq.snoc q m in
           let (g, st) = replay a minor g0 st0 q (Seq.length q) in
           let (g2, s2, _) = promote_at a minor g st m in
           replay a minor g0 st0 q' (Seq.length q') == (g2, s2))
  = let q' = Seq.snoc q m in
    let pre (j: nat) : Lemma (j < Seq.length q ==> Seq.index q' j == Seq.index q j) = () in
    FStar.Classical.forall_intro pre;
    replay_prefix a minor g0 st0 q q' (Seq.length q)
#pop-options

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

let qdistinct (q: seq U64.t) : prop =
  forall (i j: nat). i < Seq.length q /\ j < Seq.length q /\ Seq.index q i == Seq.index q j ==> i == j

/// The `j`-th promotion of the replay succeeded with copy `v`.
let promoted_at (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (q: seq U64.t) (j: nat) (v: U64.t)
  : prop =
  j < Seq.length q /\
  (let (g, st) = replay a minor g0 st0 q j in
   let (_, _, o) = promote_at a minor g st (Seq.index q j) in o == v)

/// One queued object.
let qentry (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (cs: gstate s) (j: nat) : prop =
  j < Seq.length cs.queue /\
  (let m = Seq.index cs.queue j in
   Seq.mem m (minor_objects minor) /\ ~(is_infix_in_minor minor m) /\ minor_wosize minor m > 0 /\
   cs.fwd m <> 0UL /\ promoted_at a minor g0 st0 cs.queue j (cs.fwd m))

/// **The queue.**
let qok (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (cs: gstate s) : prop =
  qdistinct cs.queue /\
  (forall (j: nat). j < Seq.length cs.queue ==> qentry a minor g0 st0 cs j) /\
  (forall (m: U64.t). cs.fwd m <> 0UL /\ ~(is_infix_in_minor minor m) ==> Seq.mem m cs.queue) /\
  replay a minor g0 st0 cs.queue (Seq.length cs.queue) == (cs.major, cs.st)

/// An address whose object, if any, is live.
let justified (minor: minor_state) (live: U64.t -> prop) (addr: U64.t) : prop =
  let x = resolve_minor minor addr in
  Seq.mem x (minor_objects minor) /\ minor_wosize minor x > 0 ==> live x

/// `live` is closed under the fields the scan reads.
let live_ok (minor: minor_state) (live: U64.t -> prop) : prop =
  forall (x: U64.t) (i: nat). live x /\ Seq.mem x (minor_objects minor) /\ i < minor_scan_wosize minor x ==>
    justified minor live (to_minor_offset (minor_read_field minor x i))

/// **Every queued object is live.**
let lv (#s: Type0) (live: U64.t -> prop) (cs: gstate s) : prop =
  forall (j: nat). j < Seq.length cs.queue ==> live (Seq.index cs.queue j)

/// The allocator refuses `m` after the first `k` promotions.
let fails_at (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (q: seq U64.t) (k: nat) (m: U64.t)
  : prop =
  let (g, st) = replay a minor g0 st0 q k in
  let (_, _, o) = promote_at a minor g st m in o == 0UL

/// **A failed promotion**: a live object, not among the first `k` queued,
/// that the allocator refuses after them.
let wit (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s) (q: seq U64.t)
  : prop =
  exists (k: nat) (m: U64.t).
    k <= Seq.length q /\ Seq.mem m (minor_objects minor) /\ ~(is_infix_in_minor minor m) /\
    minor_wosize minor m > 0 /\ live m /\
    (forall (j: nat). j < k ==> Seq.index q j =!= m) /\ fails_at a minor g0 st0 q k m

/// An address is covered: its object, if any, is forwarded, and an infix
/// address is forwarded itself.
[@@"opaque_to_smt"]
let covered (#s: Type0) (minor: minor_state) (cs: gstate s) (addr: U64.t) : prop =
  (let x = resolve_minor minor addr in
   Seq.mem x (minor_objects minor) /\ minor_wosize minor x > 0 ==> cs.fwd x <> 0UL) /\
  (is_infix_in_minor minor addr ==> cs.fwd addr <> 0UL)

let covered_def (#s: Type0) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : Lemma (covered minor cs addr <==>
           ((let x = resolve_minor minor addr in
             Seq.mem x (minor_objects minor) /\ minor_wosize minor x > 0 ==> cs.fwd x <> 0UL) /\
            (is_infix_in_minor minor addr ==> cs.fwd addr <> 0UL)))
  = reveal_opaque (`%covered) (covered #s minor cs addr)

/// `cs'` follows `cs`: the queue extended, every entry kept.
let follows (#s: Type0) (cs cs': gstate s) : prop =
  extends cs.queue cs'.queue /\ (forall (m: U64.t). cs.fwd m <> 0UL ==> cs'.fwd m == cs.fwd m)

let follows_refl (#s: Type0) (cs: gstate s) : Lemma (follows cs cs) = ()

let follows_trans (#s: Type0) (cs1 cs2 cs3: gstate s)
  : Lemma (requires follows cs1 cs2 /\ follows cs2 cs3) (ensures follows cs1 cs3) = ()

let covered_follows (#s: Type0) (minor: minor_state) (cs cs': gstate s) (addr: U64.t)
  : Lemma (requires follows cs cs' /\ covered minor cs addr) (ensures covered minor cs' addr)
  = covered_def minor cs addr; covered_def minor cs' addr

let wit_follows (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
                (cs cs': gstate s)
  : Lemma (requires follows cs cs' /\ wit a minor live g0 st0 cs.queue) (ensures wit a minor live g0 st0 cs'.queue)
  = eliminate exists (k: nat) (m: U64.t).
      k <= Seq.length cs.queue /\ Seq.mem m (minor_objects minor) /\ ~(is_infix_in_minor minor m) /\
      minor_wosize minor m > 0 /\ live m /\
      (forall (j: nat). j < k ==> Seq.index cs.queue j =!= m) /\ fails_at a minor g0 st0 cs.queue k m
    with begin
      replay_prefix a minor g0 st0 cs.queue cs'.queue k;
      assert (fails_at a minor g0 st0 cs'.queue k m)
    end

/// ---------------------------------------------------------------------------
/// Forwarding one object
/// ---------------------------------------------------------------------------

/// The state of the loop: Loop's invariant, the queue, liveness.
let sok (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s) (cs: gstate s) : prop =
  linv a minor g0 cs /\ qok a minor g0 st0 cs /\ lv live cs

/// The state after a successful promotion of `addr`.
let pushed (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t) : GTot (gstate s) =
  let (g', s', o) = promote_at a minor cs.major cs.st addr in
  { major = g'; st = s'; fwd = extend_forwarding cs.fwd addr o; queue = Seq.append cs.queue (Seq.create 1 addr) }

let pushed_queue (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : Lemma (let q' = (pushed a minor cs addr).queue in
           Seq.length q' == Seq.length cs.queue + 1 /\ extends cs.queue q' /\
           Seq.index q' (Seq.length cs.queue) == addr /\ q' == Seq.snoc cs.queue addr)
  = let q' = (pushed a minor cs addr).queue in
    assert (Seq.equal q' (Seq.snoc cs.queue addr))

/// What the conditions of a successful push are.
let push_pre (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (cs: gstate s) (addr: U64.t) : prop =
  qok a minor g0 st0 cs /\ Seq.mem addr (minor_objects minor) /\
  ~(is_infix_in_minor minor addr) /\ cs.fwd addr == 0UL /\ minor_wosize minor addr > 0 /\
  (let (_, _, o) = promote_object a minor cs.major addr cs.st (minor_wosize minor addr) in o <> 0UL)

let push_notin (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (cs: gstate s) (addr: U64.t) (j: nat)
  : Lemma (requires qok a minor g0 st0 cs /\ cs.fwd addr == 0UL /\ j < Seq.length cs.queue)
          (ensures Seq.index cs.queue j =!= addr)
  = assert (qentry a minor g0 st0 cs j)

#push-options "--z3rlimit 40"
let push_old (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (cs: gstate s) (addr: U64.t) (j: nat)
  : Lemma (requires push_pre a minor g0 st0 cs addr /\ j < Seq.length cs.queue)
          (ensures qentry a minor g0 st0 (pushed a minor cs addr) j)
  = let cs' = pushed a minor cs addr in
    pushed_queue a minor cs addr;
    assert (qentry a minor g0 st0 cs j);
    push_notin a minor g0 st0 cs addr j;
    replay_prefix a minor g0 st0 cs.queue cs'.queue j;
    assert (cs'.fwd (Seq.index cs.queue j) == cs.fwd (Seq.index cs.queue j))

let push_new (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (cs: gstate s) (addr: U64.t)
  : Lemma (requires push_pre a minor g0 st0 cs addr)
          (ensures qentry a minor g0 st0 (pushed a minor cs addr) (Seq.length cs.queue))
  = let cs' = pushed a minor cs addr in
    pushed_queue a minor cs addr;
    replay_prefix a minor g0 st0 cs.queue cs'.queue (Seq.length cs.queue)

let qd_elim (q: seq U64.t) (i j: nat)
  : Lemma (requires qdistinct q /\ i < Seq.length q /\ j < Seq.length q /\ Seq.index q i == Seq.index q j)
          (ensures i == j)
  = ()

let push_pair (q: seq U64.t) (addr: U64.t) (i j: nat)
  : Lemma (requires qdistinct q /\ (forall (k: nat). k < Seq.length q ==> Seq.index q k =!= addr) /\
                    i < Seq.length q + 1 /\ j < Seq.length q + 1 /\
                    Seq.index (Seq.snoc q addr) i == Seq.index (Seq.snoc q addr) j)
          (ensures i == j)
  = let n = Seq.length q in
    if i < n then assert (Seq.index (Seq.snoc q addr) i == Seq.index q i);
    if j < n then assert (Seq.index (Seq.snoc q addr) j == Seq.index q j);
    if i < n && j < n then qd_elim q i j

let push_distinct (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (cs: gstate s) (addr: U64.t)
  : Lemma (requires push_pre a minor g0 st0 cs addr) (ensures qdistinct (pushed a minor cs addr).queue)
  = pushed_queue a minor cs addr;
    let q = cs.queue in
    let ni (k: nat) : Lemma (k < Seq.length q ==> Seq.index q k =!= addr)
      = if k < Seq.length q then push_notin a minor g0 st0 cs addr k in
    FStar.Classical.forall_intro ni;
    assert (qdistinct q);
    let dq (i j: nat)
      : Lemma (i < Seq.length q + 1 /\ j < Seq.length q + 1 /\
               Seq.index (Seq.snoc q addr) i == Seq.index (Seq.snoc q addr) j ==> i == j)
      = FStar.Classical.move_requires (push_pair q addr i) j in
    FStar.Classical.forall_intro_2 dq
#pop-options

let lv_snoc (#s: Type0) (live: U64.t -> prop) (cs cs': gstate s) (addr: U64.t)
  : Lemma (requires lv live cs /\ live addr /\ cs'.queue == Seq.snoc cs.queue addr)
          (ensures lv live cs')
  = let one (j: nat) : Lemma (j < Seq.length cs'.queue ==> live (Seq.index cs'.queue j))
      = if j < Seq.length cs.queue then assert (Seq.index cs'.queue j == Seq.index cs.queue j) in
    FStar.Classical.forall_intro one

let follows_snoc (#s: Type0) (cs cs': gstate s) (addr: U64.t)
  : Lemma (requires cs'.queue == Seq.snoc cs.queue addr /\ cs.fwd addr == 0UL /\
                    (forall (m: U64.t). m <> addr ==> cs'.fwd m == cs.fwd m))
          (ensures follows cs cs')
  = let one (j: nat) : Lemma (j < Seq.length cs.queue ==> Seq.index cs'.queue j == Seq.index cs.queue j) = () in
    FStar.Classical.forall_intro one

/// **A promotion that succeeds queues the object.**
#push-options "--z3rlimit 40"
let fn_success (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
               (cs: gstate s) (addr: U64.t)
  : Lemma (requires push_pre a minor g0 st0 cs addr /\ lv live cs /\ live addr)
          (ensures (let cs' = pushed a minor cs addr in
                    qok a minor g0 st0 cs' /\ lv live cs' /\ follows cs cs'))
  = let cs' = pushed a minor cs addr in
    let q = cs.queue in
    pushed_queue a minor cs addr;
    replay_snoc a minor g0 st0 q addr;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (push_old a minor g0 st0 cs addr));
    push_new a minor g0 st0 cs addr;
    push_distinct a minor g0 st0 cs addr;
    let qm (m: U64.t) : Lemma (cs'.fwd m <> 0UL /\ ~(is_infix_in_minor minor m) ==> Seq.mem m cs'.queue)
      = FStar.Seq.Properties.lemma_mem_snoc q addr in
    FStar.Classical.forall_intro qm;
    assert (forall (j: nat). j < Seq.length cs'.queue ==> qentry a minor g0 st0 cs' j);
    assert (qok a minor g0 st0 cs');
    lv_snoc live cs cs' addr;
    follows_snoc cs cs' addr
#pop-options

/// A promotion that fails is a witness.
let fn_failure (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
               (cs: gstate s) (addr: U64.t)
  : Lemma (requires qok a minor g0 st0 cs /\ Seq.mem addr (minor_objects minor) /\
                    ~(is_infix_in_minor minor addr) /\ cs.fwd addr == 0UL /\ minor_wosize minor addr > 0 /\
                    live addr /\
                    (let (_, _, o) = promote_object a minor cs.major addr cs.st (minor_wosize minor addr) in o == 0UL))
          (ensures wit a minor live g0 st0 cs.queue)
  = let notin (j: nat) : Lemma (j < Seq.length cs.queue ==> Seq.index cs.queue j =!= addr)
      = if j < Seq.length cs.queue then assert (qentry a minor g0 st0 cs j) in
    FStar.Classical.forall_intro notin;
    assert (fails_at a minor g0 st0 cs.queue (Seq.length cs.queue) addr)

/// **Forwarding an object that is not infix.**
#push-options "--z3rlimit 40"
let fn_ok (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
          (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx a minor g0 /\ sok a minor live g0 st0 cs /\ ~(is_infix_in_minor minor addr) /\
                    (Seq.mem addr (minor_objects minor) /\ minor_wosize minor addr > 0 ==> live addr))
          (ensures (let cs' = forward_normal a minor cs addr in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    ((Seq.mem addr (minor_objects minor) /\ minor_wosize minor addr > 0 ==> cs'.fwd addr <> 0UL) \/
                     wit a minor live g0 st0 cs'.queue)))
  = forward_normal_keeps a minor g0 cs addr;
    if not (Seq.mem addr (minor_objects minor)) || cs.fwd addr <> 0UL then ()
    else begin
      let wz = minor_wosize minor addr in
      if wz = 0 then ()
      else begin
        let (g', s', o) = promote_object a minor cs.major addr cs.st wz in
        if o = 0UL then fn_failure a minor live g0 st0 cs addr
        else begin
          fn_success a minor live g0 st0 cs addr;
          assert (forward_normal a minor cs addr == pushed a minor cs addr)
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Forwarding an address
/// ---------------------------------------------------------------------------

/// An address already forwarded is covered.
let fwd_covered (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx a minor g0 /\ linv a minor g0 cs /\ cs.fwd addr <> 0UL) (ensures covered minor cs addr)
  = assert (entry a minor g0 cs.major cs.fwd addr);
    covered_def minor cs addr;
    if is_infix_in_minor minor addr then begin
      parent_facts minor addr;
      reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor)
    end
    else resolve_minor_non_infix minor addr

/// The infix address's entry, at the same offset in its closure's copy.
#push-options "--z3rlimit 40"
let infix_bound (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx a minor g0 /\ linv a minor g0 cs /\ is_infix_in_minor minor addr /\
                    cs.fwd (infix_parent minor addr) <> 0UL)
          (ensures (let p = infix_parent minor addr in
                    U64.v addr >= U64.v p /\ U64.v (cs.fwd p) + (U64.v addr - U64.v p) < heap_size /\
                    U64.v (cs.fwd p) >= 8))
  = let p = infix_parent minor addr in
    parent_facts minor addr;
    infix_parent_in_minor_objects minor addr;
    assert (entry a minor g0 cs.major cs.fwd p);
    assert (copy_of a minor g0 cs.major p (cs.fwd p))
#pop-options

/// Extending the map at an infix address keeps the state.
#push-options "--z3rlimit 40"
let infix_extend (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
                 (cs: gstate s) (addr: U64.t) (v: U64.t)
  : Lemma (requires ctx a minor g0 /\ sok a minor live g0 st0 cs /\ is_infix_in_minor minor addr /\
                    cs.fwd addr == 0UL /\
                    (let p = infix_parent minor addr in
                     cs.fwd p <> 0UL /\ U64.v addr >= U64.v p /\
                     U64.v v == U64.v (cs.fwd p) + (U64.v addr - U64.v p) /\ U64.v v >= 8))
          (ensures (let cs' = { cs with fwd = extend_forwarding cs.fwd addr v } in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\ covered minor cs' addr))
  = let cs' = { cs with fwd = extend_forwarding cs.fwd addr v } in
    infix_step a minor g0 cs.major cs.fwd addr v;
    covered_def minor cs' addr;
    parent_facts minor addr;
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    let en (j: nat) : Lemma (j < Seq.length cs.queue ==> qentry a minor g0 st0 cs' j)
      = if j < Seq.length cs.queue then assert (qentry a minor g0 st0 cs j) in
    FStar.Classical.forall_intro en;
    assert (qok a minor g0 st0 cs')
#pop-options

let parent_wz (minor: minor_state) (addr: U64.t)
  : Lemma (requires minor_infix_wf minor /\ is_infix_in_minor minor addr)
          (ensures Seq.mem (infix_parent minor addr) (minor_objects minor) /\
                   minor_wosize minor (infix_parent minor addr) > 0)
  = infix_parent_in_minor_objects minor addr

let fo_unfold (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : Lemma (requires cs.fwd addr == 0UL /\ is_infix_in_minor minor addr)
          (ensures (let p = infix_parent minor addr in
                    let cs' = forward_normal a minor cs p in
                    forward_one a minor cs addr ==
                    (if cs'.fwd p <> 0UL && U64.v addr >= U64.v p &&
                        U64.v (cs'.fwd p) + (U64.v addr - U64.v p) < heap_size
                     then { cs' with fwd = extend_forwarding cs'.fwd addr
                                             (U64.uint_to_t (U64.v (cs'.fwd p) + (U64.v addr - U64.v p))) }
                     else cs')))
  = ()

let fo_hit (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : Lemma (requires cs.fwd addr == 0UL /\ is_infix_in_minor minor addr /\
                    (let p = infix_parent minor addr in
                     let cs' = forward_normal a minor cs p in
                     cs'.fwd p <> 0UL /\ U64.v addr >= U64.v p /\
                     U64.v (cs'.fwd p) + (U64.v addr - U64.v p) < heap_size))
          (ensures (let p = infix_parent minor addr in
                    let cs' = forward_normal a minor cs p in
                    forward_one a minor cs addr ==
                    { cs' with fwd = extend_forwarding cs'.fwd addr
                                       (U64.uint_to_t (U64.v (cs'.fwd p) + (U64.v addr - U64.v p))) }))
  = fo_unfold a minor cs addr

let fo_miss (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : Lemma (requires cs.fwd addr == 0UL /\ is_infix_in_minor minor addr /\
                    (forward_normal a minor cs (infix_parent minor addr)).fwd (infix_parent minor addr) == 0UL)
          (ensures forward_one a minor cs addr == forward_normal a minor cs (infix_parent minor addr))
  = fo_unfold a minor cs addr

/// Forwarding an infix address: its closure, then the address itself.
#push-options "--z3rlimit 40"
let fo_infix (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
             (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx a minor g0 /\ sok a minor live g0 st0 cs /\ justified minor live addr /\
                    cs.fwd addr == 0UL /\ is_infix_in_minor minor addr)
          (ensures (let cs' = forward_one a minor cs addr in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (covered minor cs' addr \/ wit a minor live g0 st0 cs'.queue)))
  = let p = infix_parent minor addr in
    parent_facts minor addr;
    infix_parent_in_minor_objects minor addr;
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    assert (resolve_minor minor addr == p);
    fn_ok a minor live g0 st0 cs p;
    let cs' = forward_normal a minor cs p in
    forward_normal_keeps a minor g0 cs p;
    assert (cs'.fwd addr == 0UL);
    if cs'.fwd p <> 0UL then begin
      infix_bound a minor g0 cs' addr;
      fo_hit a minor cs addr;
      let v = U64.uint_to_t (U64.v (cs'.fwd p) + (U64.v addr - U64.v p)) in
      infix_extend a minor live g0 st0 cs' addr v;
      let cs'' = { cs' with fwd = extend_forwarding cs'.fwd addr v } in
      follows_trans cs cs' cs''
    end
    else begin
      fo_miss a minor cs addr;
      parent_wz minor addr;
      assert (wit a minor live g0 st0 cs'.queue)
    end
#pop-options

/// **Forwarding an address**: covered after, or a witness.
let fo_ok (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
          (cs: gstate s) (addr: U64.t)
  : Lemma (requires ctx a minor g0 /\ sok a minor live g0 st0 cs /\ justified minor live addr)
          (ensures (let cs' = forward_one a minor cs addr in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (covered minor cs' addr \/ wit a minor live g0 st0 cs'.queue)))
  = if cs.fwd addr <> 0UL then fwd_covered a minor g0 cs addr
    else if is_infix_in_minor minor addr then fo_infix a minor live g0 st0 cs addr
    else begin
      resolve_minor_non_infix minor addr;
      fn_ok a minor live g0 st0 cs addr;
      covered_def minor (forward_one a minor cs addr) addr
    end

/// ---------------------------------------------------------------------------
/// The loops
/// ---------------------------------------------------------------------------

/// The field `i` of `x`, as the scan reads it.
[@@"opaque_to_smt"]
let fld (minor: minor_state) (x: U64.t) (i: nat) : GTot U64.t = to_minor_offset (minor_read_field minor x i)

let fld_def (minor: minor_state) (x: U64.t) (i: nat)
  : Lemma (fld minor x i == to_minor_offset (minor_read_field minor x i))
  = reveal_opaque (`%fld) (fld minor x i)

let combine_cov (#s: Type0) (minor: minor_state) (cs: gstate s) (parent: U64.t) (idx wz: nat)
  : Lemma (requires covered minor cs (fld minor parent idx) /\
                    (forall (i: nat). idx + 1 <= i /\ i < wz ==> covered minor cs (fld minor parent i)))
          (ensures forall (i: nat). idx <= i /\ i < wz ==> covered minor cs (fld minor parent i))
  = let q (i: nat) : Lemma (idx <= i /\ i < wz ==> covered minor cs (fld minor parent i))
      = if i = idx then () in
    FStar.Classical.forall_intro q

let combine_roots (#s: Type0) (minor: minor_state) (cs: gstate s) (roots: seq U64.t) (idx: nat)
  : Lemma (requires idx < Seq.length roots /\ covered minor cs (Seq.index roots idx) /\
                    (forall (i: nat). idx + 1 <= i /\ i < Seq.length roots ==> covered minor cs (Seq.index roots i)))
          (ensures forall (i: nat). idx <= i /\ i < Seq.length roots ==> covered minor cs (Seq.index roots i))
  = let q (i: nat) : Lemma (idx <= i /\ i < Seq.length roots ==> covered minor cs (Seq.index roots i))
      = if i = idx then () in
    FStar.Classical.forall_intro q

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec ff_ok (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
              (cs: gstate s) (parent: U64.t) (idx: nat) (wz: nat)
  : Lemma (requires ctx a minor g0 /\ sok a minor live g0 st0 cs /\
                    (forall (i: nat). idx <= i /\ i < wz ==> justified minor live (fld minor parent i)))
          (ensures (let cs' = forward_fields a minor cs parent idx wz in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (wit a minor live g0 st0 cs'.queue \/
                     (forall (i: nat). idx <= i /\ i < wz ==> covered minor cs' (fld minor parent i)))))
          (decreases (if idx >= wz then 0 else wz - idx))
  = if idx < wz then begin
      let fv = fld minor parent idx in
      fld_def minor parent idx;
      fo_ok a minor live g0 st0 cs fv;
      let cs1 = forward_one a minor cs fv in
      ff_ok a minor live g0 st0 cs1 parent (idx + 1) wz;
      let cs' = forward_fields a minor cs1 parent (idx + 1) wz in
      assert (forward_fields a minor cs parent idx wz == cs');
      follows_trans cs cs1 cs';
      if FStar.IndefiniteDescription.strong_excluded_middle (wit a minor live g0 st0 cs1.queue)
      then wit_follows a minor live g0 st0 cs1 cs'
      else begin
        covered_follows minor cs1 cs' fv;
        if FStar.IndefiniteDescription.strong_excluded_middle (wit a minor live g0 st0 cs'.queue) then ()
        else combine_cov minor cs' parent idx wz
      end
    end

let rec fr_ok (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
              (cs: gstate s) (roots: seq U64.t) (idx: nat)
  : Lemma (requires ctx a minor g0 /\ sok a minor live g0 st0 cs /\
                    (forall (i: nat). idx <= i /\ i < Seq.length roots ==> justified minor live (Seq.index roots i)))
          (ensures (let cs' = forward_roots a minor cs roots idx in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (wit a minor live g0 st0 cs'.queue \/
                     (forall (i: nat). idx <= i /\ i < Seq.length roots ==> covered minor cs' (Seq.index roots i)))))
          (decreases (if idx >= Seq.length roots then 0 else Seq.length roots - idx))
  = if idx < Seq.length roots then begin
      let r = Seq.index roots idx in
      fo_ok a minor live g0 st0 cs r;
      let cs1 = forward_one a minor cs r in
      fr_ok a minor live g0 st0 cs1 roots (idx + 1);
      let cs' = forward_roots a minor cs1 roots (idx + 1) in
      assert (forward_roots a minor cs roots idx == cs');
      follows_trans cs cs1 cs';
      if FStar.IndefiniteDescription.strong_excluded_middle (wit a minor live g0 st0 cs1.queue)
      then wit_follows a minor live g0 st0 cs1 cs'
      else begin
        covered_follows minor cs1 cs' r;
        if FStar.IndefiniteDescription.strong_excluded_middle (wit a minor live g0 st0 cs'.queue) then ()
        else combine_roots minor cs' roots idx
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The queue fits in the nursery
/// ---------------------------------------------------------------------------

/// `s` without its element at `i`.
let drop (s: seq U64.t) (i: nat{i < Seq.length s}) : seq U64.t =
  Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))

#push-options "--fuel 1 --ifuel 1"
let drop_mem (s: seq U64.t) (i: nat{i < Seq.length s}) (y: U64.t)
  : Lemma (requires Seq.mem y s /\ y =!= Seq.index s i) (ensures Seq.mem y (drop s i))
  = let j = FStar.Seq.Properties.index_mem y s in
    FStar.Seq.Properties.lemma_mem_append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s));
    if j < i then begin
      assert (Seq.index (Seq.slice s 0 i) j == y);
      GC.Spec.Top.ByteMark.mem_of_index (Seq.slice s 0 i) j
    end
    else begin
      assert (Seq.index (Seq.slice s (i + 1) (Seq.length s)) (j - i - 1) == y);
      GC.Spec.Top.ByteMark.mem_of_index (Seq.slice s (i + 1) (Seq.length s)) (j - i - 1)
    end

/// **Distinct elements of `s` are no more than `s`.**
let rec distinct_le (q s: seq U64.t)
  : Lemma (requires qdistinct q /\ (forall (j: nat). j < Seq.length q ==> Seq.mem (Seq.index q j) s))
          (ensures Seq.length q <= Seq.length s) (decreases Seq.length q)
  = if Seq.length q > 0 then begin
      let n = Seq.length q - 1 in
      let x = Seq.index q n in
      let i = FStar.Seq.Properties.index_mem x s in
      let q' = Seq.slice q 0 n in
      let s' = drop s i in
      let m (j: nat) : Lemma (j < n ==> Seq.mem (Seq.index q' j) s')
        = if j < n then begin
            assert (Seq.index q' j == Seq.index q j);
            assert (Seq.index q j =!= x);
            drop_mem s i (Seq.index q j)
          end in
      FStar.Classical.forall_intro m;
      distinct_le q' s'
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The scan
/// ---------------------------------------------------------------------------

/// The number of fields the scan reads.
[@@"opaque_to_smt"]
let nsc (minor: minor_state) (x: U64.t) : GTot nat = minor_scan_wosize minor x

let nsc_def (minor: minor_state) (x: U64.t) : Lemma (nsc minor x == minor_scan_wosize minor x)
  = reveal_opaque (`%nsc) (nsc minor x)

/// The fields of the first `sc` queued objects are covered.
let scanned (#s: Type0) (minor: minor_state) (cs: gstate s) (sc: nat) : prop =
  forall (j: nat) (i: nat). j < sc /\ j < Seq.length cs.queue /\ i < nsc minor (Seq.index cs.queue j) ==>
    covered minor cs (fld minor (Seq.index cs.queue j) i)

let scanned_follows (#s: Type0) (minor: minor_state) (cs cs': gstate s) (sc: nat)
  : Lemma (requires follows cs cs' /\ scanned minor cs sc /\ sc <= Seq.length cs.queue)
          (ensures scanned minor cs' sc)
  = let one (j i: nat)
      : Lemma (j < sc /\ j < Seq.length cs'.queue /\ i < nsc minor (Seq.index cs'.queue j) ==>
               covered minor cs' (fld minor (Seq.index cs'.queue j) i))
      = if j < sc && j < Seq.length cs'.queue && i < nsc minor (Seq.index cs'.queue j) then begin
          assert (Seq.index cs'.queue j == Seq.index cs.queue j);
          covered_follows minor cs cs' (fld minor (Seq.index cs.queue j) i)
        end in
    FStar.Classical.forall_intro_2 one

let queue_le (#s: Type0) (a: tal s) (minor: minor_state) (g0: heap) (st0: s) (cs: gstate s)
  : Lemma (requires qok a minor g0 st0 cs) (ensures Seq.length cs.queue <= Seq.length (minor_objects minor))
  = let m (j: nat) : Lemma (j < Seq.length cs.queue ==> Seq.mem (Seq.index cs.queue j) (minor_objects minor))
      = if j < Seq.length cs.queue then assert (qentry a minor g0 st0 cs j) in
    FStar.Classical.forall_intro m;
    distinct_le cs.queue (minor_objects minor)

let scan_one_just (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
                  (cs: gstate s) (sc: nat)
  : Lemma (requires sok a minor live g0 st0 cs /\ live_ok minor live /\ sc < Seq.length cs.queue)
          (ensures (let x = Seq.index cs.queue sc in
                    forall (i: nat). 0 <= i /\ i < minor_scan_wosize minor x ==> justified minor live (fld minor x i)))
  = assert (qentry a minor g0 st0 cs sc);
    FStar.Classical.forall_intro (fld_def minor (Seq.index cs.queue sc))

#push-options "--ifuel 0 --z3rlimit 40"
let scanned_step (#s: Type0) (minor: minor_state) (cs cs1: gstate s) (sc: nat) (x: U64.t)
  : Lemma (requires scanned minor cs sc /\ follows cs cs1 /\ sc < Seq.length cs.queue /\
                    Seq.index cs.queue sc == x /\
                    (forall (i: nat). 0 <= i /\ i < nsc minor x ==> covered minor cs1 (fld minor x i)))
          (ensures scanned minor cs1 (sc + 1))
  = scanned_follows minor cs cs1 sc;
    assert (Seq.index cs1.queue sc == x);
    let one (j i: nat)
      : Lemma (j < sc + 1 /\ j < Seq.length cs1.queue /\ i < nsc minor (Seq.index cs1.queue j) ==>
               covered minor cs1 (fld minor (Seq.index cs1.queue j) i))
      = if j = sc && i < nsc minor x then begin
          assert (Seq.index cs1.queue j == x);
          assert (covered minor cs1 (fld minor x i))
        end in
    FStar.Classical.forall_intro_2 one
#pop-options

/// One object scanned.
#push-options "--z3rlimit 40"
let scan_step (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
              (cs: gstate s) (sc: nat)
  : Lemma (requires ctx a minor g0 /\ sok a minor live g0 st0 cs /\ live_ok minor live /\ sc < Seq.length cs.queue /\
                    (wit a minor live g0 st0 cs.queue \/ scanned minor cs sc))
          (ensures (let x = Seq.index cs.queue sc in
                    let cs1 = forward_fields a minor cs x 0 (minor_scan_wosize minor x) in
                    sok a minor live g0 st0 cs1 /\ follows cs cs1 /\
                    (wit a minor live g0 st0 cs1.queue \/ scanned minor cs1 (sc + 1))))
  = let x = Seq.index cs.queue sc in
    scan_one_just a minor live g0 st0 cs sc;
    ff_ok a minor live g0 st0 cs x 0 (minor_scan_wosize minor x);
    let cs1 = forward_fields a minor cs x 0 (minor_scan_wosize minor x) in
    if FStar.IndefiniteDescription.strong_excluded_middle (wit a minor live g0 st0 cs.queue)
    then wit_follows a minor live g0 st0 cs cs1
    else if FStar.IndefiniteDescription.strong_excluded_middle (wit a minor live g0 st0 cs1.queue) then ()
    else begin
      nsc_def minor x;
      scanned_step minor cs cs1 sc x
    end
#pop-options

#push-options "--fuel 1 --ifuel 0"
let scan_unfold (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (sc: nat) (fuel: nat)
  : Lemma (requires fuel > 0 /\ sc < Seq.length cs.queue)
          (ensures (let x = Seq.index cs.queue sc in
                    scan a minor cs sc fuel ==
                    scan a minor (forward_fields a minor cs x 0 (minor_scan_wosize minor x)) (sc + 1) (fuel - 1)))
  = ()
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec scan_ok (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
                (cs: gstate s) (sc: nat) (fuel: nat)
  : Lemma (requires ctx a minor g0 /\ sok a minor live g0 st0 cs /\ live_ok minor live /\
                    sc <= Seq.length cs.queue /\ Seq.length (minor_objects minor) <= sc + fuel /\
                    (wit a minor live g0 st0 cs.queue \/ scanned minor cs sc))
          (ensures (let cs' = scan a minor cs sc fuel in
                    sok a minor live g0 st0 cs' /\ follows cs cs' /\
                    (wit a minor live g0 st0 cs'.queue \/ scanned minor cs' (Seq.length cs'.queue))))
          (decreases fuel)
  = if fuel = 0 || sc >= Seq.length cs.queue then queue_le a minor g0 st0 cs
    else begin
      let x = Seq.index cs.queue sc in
      scan_step a minor live g0 st0 cs sc;
      let cs1 = forward_fields a minor cs x 0 (minor_scan_wosize minor x) in
      scan_unfold a minor cs sc fuel;
      let f' : nat = fuel - 1 in
      scan_ok a minor live g0 st0 cs1 (sc + 1) f';
      follows_trans cs cs1 (scan a minor cs1 (sc + 1) f')
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The whole promotion
/// ---------------------------------------------------------------------------

let cs0 (#s: Type0) (g0: heap) (st0: s) : gstate s =
  { major = g0; st = st0; fwd = empty_forwarding; queue = Seq.empty }

#push-options "--fuel 1"
let start_ok (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
  : Lemma (requires a.inv g0 st0) (ensures sok a minor live g0 st0 (cs0 g0 st0))
  = let cs = cs0 #s g0 st0 in
    assert (olds a g0 g0);
    assert (news a minor g0 g0 empty_forwarding);
    assert (entries a minor g0 g0 empty_forwarding);
    assert (replay a minor g0 st0 cs.queue 0 == (g0, st0));
    assert (qok a minor g0 st0 cs)
#pop-options

/// **What promotion ends in**: every queued object live, and a failed
/// promotion, or every root and every field of every queued object covered.
#push-options "--z3rlimit 40"
let promote_done (#s: Type0) (a: tal s) (minor: minor_state) (live: U64.t -> prop) (g0: heap) (st0: s)
                 (roots: seq U64.t)
  : Lemma (requires ctx a minor g0 /\ a.inv g0 st0 /\ live_ok minor live /\
                    (forall (i: nat). i < Seq.length roots ==> justified minor live (Seq.index roots i)))
          (ensures (let cs = promote a minor g0 st0 roots in
                    sok a minor live g0 st0 cs /\
                    (wit a minor live g0 st0 cs.queue \/
                     ((forall (i: nat). i < Seq.length roots ==> covered minor cs (Seq.index roots i)) /\
                      scanned minor cs (Seq.length cs.queue)))))
  = start_ok a minor live g0 st0;
    let c0 = cs0 #s g0 st0 in
    fr_ok a minor live g0 st0 c0 roots 0;
    let cs1 = forward_roots a minor c0 roots 0 in
    assert (scanned minor cs1 0);
    scan_ok a minor live g0 st0 cs1 0 (Seq.length (minor_objects minor));
    let cs = scan a minor cs1 0 (Seq.length (minor_objects minor)) in
    assert (promote a minor g0 st0 roots == cs);
    if FStar.IndefiniteDescription.strong_excluded_middle (wit a minor live g0 st0 cs1.queue)
    then wit_follows a minor live g0 st0 cs1 cs
    else begin
      let r (i: nat) : Lemma (i < Seq.length roots ==> covered minor cs (Seq.index roots i))
        = if i < Seq.length roots then covered_follows minor cs1 cs (Seq.index roots i) in
      FStar.Classical.forall_intro r
    end
#pop-options
