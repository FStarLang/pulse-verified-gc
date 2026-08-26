/// GC.Gen.Cheney.SimOne — Queue validity/bound for cheney_forward_one
///
/// Proofs about the single-step forwarding function, separated to prevent
/// WP inlining in recursive callers.

module GC.Gen.Cheney.SimOne

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.Impl.UpdatePtrs

module CheneySpec = GC.Gen.Cheney

/// Definition of queue_valid (hidden from outside by the val in .fsti)
let queue_valid (minor: minor_state) (q: seq U64.t) : prop =
  forall (j:nat). j < Seq.length q ==> Seq.mem (Seq.index q j) (minor_objects minor)

let queue_valid_intro (minor: minor_state) (q: seq U64.t)
  = ()

let queue_valid_elim (minor: minor_state) (q: seq U64.t)
  = ()

/// Helper: when forward_one appends addr to queue, the extended queue is still valid
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

private let forward_one_append_valid
  (minor: minor_state) (old_q new_q: seq U64.t) (addr: U64.t)
  : Lemma (requires new_q == Seq.append old_q (Seq.create 1 addr) /\
                    Seq.mem addr (minor_objects minor) /\
                    queue_valid minor old_q)
          (ensures queue_valid minor new_q)
  =
  Seq.Base.lemma_len_append old_q (Seq.create 1 addr);
  let aux (j: nat{j < Seq.length new_q})
    : Lemma (Seq.mem (Seq.index new_q j) (minor_objects minor))
    = if j < Seq.length old_q then
        Seq.Base.lemma_index_app1 old_q (Seq.create 1 addr) j
      else
        Seq.Base.lemma_index_app2 old_q (Seq.create 1 addr) j
  in
  FStar.Classical.forall_intro aux

#pop-options

/// Queue validity: fuel 0, rely on unfold lemmas
/// ---------------------------------------------------------------------------
/// Recursive queue validity proofs
/// These live in SimOne (where queue_valid's definition is known)
/// to avoid WP encoding issues in the client module (where queue_valid
/// is abstract).
///
/// Since cheney_forward_fields/roots/scan are opaque (behind .fsti),
/// we use their equation lemmas (_base/_step) to unfold the recursive
/// definitions one step at a time.
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// Potential-function based BFS invariant
///
/// Key idea: count_unforwarded counts how many minor objects still have
/// fwd == 0UL. The invariant |queue| + count_unforwarded <= |minor_objects|
/// is preserved because each successful forward_one:
///   - increments |queue| by 1
///   - decrements count_unforwarded by at least 1 (the forwarded addr)
/// Since count_unforwarded >= 0, we get |queue| <= |minor_objects|.
/// ---------------------------------------------------------------------------

/// Count positions in a sequence where the forwarding map is zero
let rec count_unforwarded (objs: seq U64.t) (fwd: forwarding_map) (i: nat)
  : GTot nat (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then 0
    else (if fwd (Seq.index objs i) = 0UL then 1 else 0) +
         count_unforwarded objs fwd (i + 1)
/// With empty_forwarding, every element contributes 1
private let rec count_unforwarded_empty (objs: seq U64.t) (i: nat)
  : Lemma (ensures count_unforwarded objs empty_forwarding i ==
                   (if i < Seq.length objs then Seq.length objs - i else 0))
          (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then ()
    else count_unforwarded_empty objs (i + 1)

/// When extend_forwarding sets fwd for addr (which was 0UL and is in objs),
/// count_unforwarded decreases by at least 1.
private let rec count_unforwarded_decrease
  (objs: seq U64.t) (fwd: forwarding_map)
  (addr: U64.t) (new_addr: U64.t) (i: nat)
  : Lemma (requires new_addr <> 0UL /\ fwd addr = 0UL /\
                    (exists (k:nat). k >= i /\ k < Seq.length objs /\ Seq.index objs k == addr))
          (ensures count_unforwarded objs (extend_forwarding fwd addr new_addr) i + 1
                   <= count_unforwarded objs fwd i)
          (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then ()  // unreachable by precondition
    else
      let x = Seq.index objs i in
      let fwd' = extend_forwarding fwd addr new_addr in
      if x = addr then begin
        // x == addr: old contribution = 1 (fwd addr == 0UL), new = 0 (fwd' addr = new_addr <> 0UL)
        // rest: count_unforwarded objs fwd' (i+1) <= count_unforwarded objs fwd (i+1)
        count_unforwarded_monotone objs fwd addr new_addr (i + 1)
      end else begin
        // x <> addr: contributions are the same, recurse to find addr later
        assert (fwd' x == fwd x);
        // addr must appear at some k > i (since objs[i] <> addr)
        FStar.Classical.exists_elim
          (count_unforwarded objs fwd' i + 1 <= count_unforwarded objs fwd i)
          ()
          (fun (k:nat{k >= i /\ k < Seq.length objs /\ Seq.index objs k == addr}) ->
            if k = i then () // contradiction since x <> addr
            else count_unforwarded_decrease objs fwd addr new_addr (i + 1))
      end

/// Helper: extend_forwarding only turns 1s into 0s, never 0s into 1s
and count_unforwarded_monotone
  (objs: seq U64.t) (fwd: forwarding_map)
  (addr: U64.t) (new_addr: U64.t) (i: nat)
  : Lemma (requires new_addr <> 0UL)
          (ensures count_unforwarded objs (extend_forwarding fwd addr new_addr) i
                   <= count_unforwarded objs fwd i)
          (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then ()
    else begin
      let x = Seq.index objs i in
      let fwd' = extend_forwarding fwd addr new_addr in
      // For x = addr: old might be 1 (if fwd addr == 0UL), new is 0
      // For x <> addr: fwd' x == fwd x, same contribution
      count_unforwarded_monotone objs fwd addr new_addr (i + 1)
    end

/// If two forwarding maps agree on all elements of objs, count_unforwarded is the same
private let rec count_unforwarded_ext
  (objs: seq U64.t) (fwd1 fwd2: forwarding_map) (i: nat)
  : Lemma (requires (forall (k:nat). k >= i /\ k < Seq.length objs ==>
                      fwd1 (Seq.index objs k) == fwd2 (Seq.index objs k)))
          (ensures count_unforwarded objs fwd1 i == count_unforwarded objs fwd2 i)
          (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then ()
    else count_unforwarded_ext objs fwd1 fwd2 (i + 1)

/// ---------------------------------------------------------------------------
/// Compound BFS invariant definition and lemmas
/// ---------------------------------------------------------------------------

/// Once an interior nursery pointer has an entry in the forwarding map, so
/// does the closure it points into.  Stock OCaml stores such pointers in
/// ordinary fields of nursery blocks (`runtime/interp.c:575` builds mutually
/// recursive closures with `Alloc_small`), so the same interior address can be
/// reached twice; the second visit takes the *already forwarded* branch of
/// `cheney_forward_one` and returns the state untouched, which is only enough
/// to keep the parent alive because of this invariant.
let fwd_infix_closed (minor: minor_state) (fwd: forwarding_map) : prop =
  forall (x: U64.t). is_infix_in_minor minor x /\ fwd x <> 0UL ==>
                     fwd (infix_parent minor x) <> 0UL

/// Extending the forwarding map with a non-zero image preserves infix closure,
/// provided an interior key brings its parent's entry along.
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
private let fwd_infix_closed_extend
  (minor: minor_state) (fwd: forwarding_map) (a v: U64.t)
  : Lemma (requires fwd_infix_closed minor fwd /\ v <> 0UL /\
                    (is_infix_in_minor minor a ==>
                       infix_parent minor a <> a /\ fwd (infix_parent minor a) <> 0UL))
          (ensures fwd_infix_closed minor (extend_forwarding fwd a v))
  = let fwd' = extend_forwarding fwd a v in
    let aux (x: U64.t) : Lemma
      (requires is_infix_in_minor minor x /\ fwd' x <> 0UL)
      (ensures fwd' (infix_parent minor x) <> 0UL)
      = if x = a then ()
        else begin
          assert (fwd' x == fwd x);
          assert (fwd (infix_parent minor x) <> 0UL)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let cheney_bfs_inv (minor: minor_state) (cs: CheneySpec.cheney_state) : prop =
  fwd_infix_closed minor cs.cs_fwd /\
  queue_valid minor cs.cs_queue /\
  (forall (j:nat). j < Seq.length cs.cs_queue ==>
    cs.cs_fwd (Seq.index cs.cs_queue j) <> 0UL) /\
  (forall (x: U64.t).
    Seq.mem x (minor_objects minor) /\
    cs.cs_fwd x <> 0UL ==> Seq.mem x cs.cs_queue) /\
  Seq.length cs.cs_queue + count_unforwarded (minor_objects minor) cs.cs_fwd 0
    <= Seq.length (minor_objects minor)

let cheney_bfs_inv_fwd_in_queue
  (minor: minor_state) (cs: CheneySpec.cheney_state)
  = ()

let cheney_bfs_inv_initial (minor: minor_state) (cs: CheneySpec.cheney_state)
  = queue_valid_intro minor Seq.empty;
    count_unforwarded_empty (minor_objects minor) 0;
    let aux_complete (x: U64.t) : Lemma
      (requires Seq.mem x (minor_objects minor) /\ cs.CheneySpec.cs_fwd x <> 0UL)
      (ensures Seq.mem x cs.CheneySpec.cs_queue)
    =
      assert (cs.CheneySpec.cs_fwd x == 0UL);
      assert False
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_complete)

let cheney_bfs_inv_bound (minor: minor_state) (cs: CheneySpec.cheney_state)
  = ()  // Direct from the invariant (count_unforwarded >= 0 by type nat)

let cheney_bfs_inv_valid (minor: minor_state) (cs: CheneySpec.cheney_state)
  = ()

let cheney_bfs_inv_infix_closed (minor: minor_state) (cs: CheneySpec.cheney_state)
  = ()

/// ---------------------------------------------------------------------------
/// Forward_one preserves BFS invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --using_facts_from '* -GC.Gen.Cheney.cheney_forward_one -GC.Gen.Cheney.cheney_forward_normal'"

private let fwd_one_bfs_inv_success
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\ minor_wf minor /\
                    Seq.mem addr (minor_objects minor) /\
                    cs.cs_fwd addr = 0UL /\
                    minor_wosize minor addr > 0 /\
                    (promote_object minor cs.cs_major addr cs.cs_fp
                       (minor_wosize minor addr)).new_addr <> 0UL)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_normal minor cs addr))
  =
  let wz = minor_wosize minor addr in
  let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
  minor_objects_not_infix minor addr;
  fwd_infix_closed_extend minor cs.cs_fwd addr res.new_addr;
  CheneySpec.cheney_forward_normal_success minor cs addr;
  let cs' = CheneySpec.cheney_forward_normal minor cs addr in
  let fwd' = extend_forwarding cs.cs_fwd addr res.new_addr in
  forward_one_append_valid minor cs.cs_queue cs'.cs_queue addr;
  let aux_fwd (j: nat{j < Seq.length cs'.cs_queue})
    : Lemma (cs'.cs_fwd (Seq.index cs'.cs_queue j) <> 0UL)
    = Seq.Base.lemma_len_append cs.cs_queue (Seq.create 1 addr);
      if j < Seq.length cs.cs_queue then begin
        Seq.Base.lemma_index_app1 cs.cs_queue (Seq.create 1 addr) j;
        let entry = Seq.index cs.cs_queue j in
        assert (cs.cs_fwd entry <> 0UL);
        assert (entry <> addr);
        assert (fwd' entry == cs.cs_fwd entry)
      end else begin
        Seq.Base.lemma_index_app2 cs.cs_queue (Seq.create 1 addr) j;
        assert (Seq.index cs'.cs_queue j == addr);
        assert (fwd' addr == res.new_addr)
      end
  in
  FStar.Classical.forall_intro aux_fwd;
  let aux_complete (x: U64.t) : Lemma
    (requires Seq.mem x (minor_objects minor) /\ cs'.cs_fwd x <> 0UL)
    (ensures Seq.mem x cs'.cs_queue)
  =
    Seq.Base.lemma_len_append cs.cs_queue (Seq.create 1 addr);
    if x = addr then begin
      Seq.lemma_mem_append cs.cs_queue (Seq.create 1 addr);
      Seq.mem_cons addr Seq.empty
    end else begin
      assert (fwd' x == cs.cs_fwd x);
      assert (cs.cs_fwd x <> 0UL);
      cheney_bfs_inv_fwd_in_queue minor cs;
      assert (Seq.mem x cs.cs_queue);
      Seq.lemma_mem_append cs.cs_queue (Seq.create 1 addr)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux_complete);
  FStar.Classical.exists_intro
    (fun (k:nat) -> k >= 0 /\ k < Seq.length (minor_objects minor) /\
                    Seq.index (minor_objects minor) k == addr)
    (Seq.index_mem addr (minor_objects minor));
  count_unforwarded_decrease (minor_objects minor) cs.cs_fwd addr res.new_addr 0;
  Seq.Base.lemma_len_append cs.cs_queue (Seq.create 1 addr)

#pop-options

/// Forward_normal preserves BFS invariant (same logic as old forward_one)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --using_facts_from '* -GC.Gen.Cheney.cheney_forward_one -GC.Gen.Cheney.cheney_forward_normal'"

private let fwd_normal_preserves_bfs_inv
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\ minor_wf minor)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_normal minor cs addr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    CheneySpec.cheney_forward_normal_noop minor cs addr
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      CheneySpec.cheney_forward_normal_noop_wz0 minor cs addr
    else begin
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        CheneySpec.cheney_forward_normal_noop_oom minor cs addr
      else
        fwd_one_bfs_inv_success minor cs addr
    end
  end

#pop-options

/// Forward_one preserves BFS invariant (infix-aware).
/// For the infix case: forward parent preserves bfs_inv, then extending
/// fwd for the infix addr (which is NOT in minor_objects) doesn't change
/// the queue or count_unforwarded.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --using_facts_from '* -GC.Gen.Cheney.cheney_forward_one -GC.Gen.Cheney.cheney_forward_normal'"

let fwd_one_preserves_bfs_inv
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  =
  if cs.cs_fwd addr <> 0UL then
    CheneySpec.cheney_forward_one_noop minor cs addr
  else if is_infix_in_minor minor addr then begin
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf minor);
    assert (U64.v addr >= U64.v (infix_parent minor addr));
    let parent = infix_parent minor addr in
    // parent < addr since wosize > 0 implies delta > 0
    assert (parent <> addr);
    // Forward parent preserves bfs_inv
    fwd_normal_preserves_bfs_inv minor cs parent;
    let cs' = CheneySpec.cheney_forward_normal minor cs parent in
    assert (cheney_bfs_inv minor cs');
    // cs'.cs_fwd addr = 0UL (forward_normal on parent doesn't touch addr)
    CheneySpec.cheney_forward_normal_other_fwd minor cs parent addr;
    assert (cs'.cs_fwd addr == cs.cs_fwd addr);
    assert (cs'.cs_fwd addr = 0UL);
    // r = cheney_forward_one minor cs addr
    let r = CheneySpec.cheney_forward_one minor cs addr in
    CheneySpec.cheney_forward_one_infix minor cs addr;
    // r.cs_queue == cs'.cs_queue
    assert (r.cs_queue == cs'.cs_queue);
    // For all queue members y: cs'.cs_fwd y <> 0UL, hence y <> addr, hence r.cs_fwd y == cs'.cs_fwd y <> 0UL
    let aux_queue (j: nat{j < Seq.length r.cs_queue})
      : Lemma (r.cs_fwd (Seq.index r.cs_queue j) <> 0UL)
      = let y = Seq.index r.cs_queue j in
        assert (cs'.cs_fwd y <> 0UL); // from bfs_inv of cs'
        assert (y <> addr); // since cs'.cs_fwd addr = 0UL but cs'.cs_fwd y <> 0UL
        CheneySpec.cheney_forward_one_infix_fwd minor cs addr y
    in
    FStar.Classical.forall_intro aux_queue;
    // count_unforwarded is the same because all minor_objects members have tag <> 249 (hence <> addr)
    let objs = minor_objects minor in
    let aux_ext (k: nat{k >= 0 /\ k < Seq.length objs})
      : Lemma (r.cs_fwd (Seq.index objs k) == cs'.cs_fwd (Seq.index objs k))
      = let y = Seq.index objs k in
        minor_objects_not_infix minor y;
        // y has tag <> 249, addr has tag == 249 (is_infix_in_minor), hence y <> addr
        assert (minor_tag minor y <> 249);
        assert (minor_tag minor addr = 249);
        assert (y <> addr);
        CheneySpec.cheney_forward_one_infix_fwd minor cs addr y
    in
    FStar.Classical.forall_intro aux_ext;
    let aux_complete (x: U64.t) : Lemma
      (requires Seq.mem x objs /\ r.cs_fwd x <> 0UL)
      (ensures Seq.mem x r.cs_queue)
    =
      let k = Seq.index_mem x objs in
      aux_ext k;
      assert (r.cs_fwd x == cs'.cs_fwd x);
      assert (cs'.cs_fwd x <> 0UL);
      cheney_bfs_inv_fwd_in_queue minor cs';
      assert (Seq.mem x cs'.cs_queue);
      assert (r.cs_queue == cs'.cs_queue)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_complete);
    count_unforwarded_ext objs r.cs_fwd cs'.cs_fwd 0;
    // queue_valid is same since queues are equal
    assert (queue_valid minor r.cs_queue);
    // Infix closure: the parent's entry is installed before the interior one.
    if cs'.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then begin
      CheneySpec.cheney_forward_one_infix_guard_pass minor cs addr;
      let sum = U64.uint_to_t (U64.v (cs'.cs_fwd parent) + (U64.v addr - U64.v parent)) in
      assert (U64.v (cs'.cs_fwd parent) > 0);
      assert (U64.v sum > 0);
      fwd_infix_closed_extend minor cs'.cs_fwd addr sum
    end
    else CheneySpec.cheney_forward_one_infix_guard_fail minor cs addr
  end
  else begin
    CheneySpec.cheney_forward_one_normal minor cs addr;
    fwd_normal_preserves_bfs_inv minor cs addr
  end

#pop-options

/// ---------------------------------------------------------------------------
/// Recursive BFS invariant preservation
/// ---------------------------------------------------------------------------

/// ---------------------------------------------------------------------------
/// BFS invariant: strict room when forwarding an unforwarded object
/// ---------------------------------------------------------------------------

/// Helper: if addr is in objs at index k with fwd(addr)=0, count_unforwarded from start <= k is >= 1
private let rec count_unforwarded_positive
  (objs: seq U64.t) (fwd: forwarding_map) (start: nat) (k: nat)
  : Lemma (requires start <= k /\ k < Seq.length objs /\
                    fwd (Seq.index objs k) = 0UL)
          (ensures count_unforwarded objs fwd start >= 1)
          (decreases k - start)
  = if start >= Seq.length objs then ()
    else if fwd (Seq.index objs start) = 0UL then ()
    else count_unforwarded_positive objs fwd (start + 1) k

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

let cheney_bfs_inv_strict_room
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  =
  let objs = minor_objects minor in
  let fwd = cs.CheneySpec.cs_fwd in
  // addr is in objs, find its index
  let k = Seq.index_mem addr objs in
  // count_unforwarded >= 1 because addr at index k has fwd = 0UL
  count_unforwarded_positive objs fwd 0 k
  // From invariant: |queue| + count_unforwarded <= |objs|
  // count_unforwarded >= 1, so |queue| <= |objs| - 1, i.e., |queue| < |objs|

#pop-options
