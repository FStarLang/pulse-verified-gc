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
  : Lemma (requires (forall (j:nat). j < Seq.length q ==> Seq.mem (Seq.index q j) (minor_objects minor)))
          (ensures queue_valid minor q)
  = ()

let queue_valid_elim (minor: minor_state) (q: seq U64.t)
  : Lemma (requires queue_valid minor q)
          (ensures (forall (j:nat). j < Seq.length q ==> Seq.mem (Seq.index q j) (minor_objects minor)))
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
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --using_facts_from '* -GC.Gen.Cheney.cheney_forward_one'"

let fwd_one_preserves_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires queue_valid minor cs.cs_queue)
          (ensures queue_valid minor (CheneySpec.cheney_forward_one minor cs addr).cs_queue)
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    CheneySpec.cheney_forward_one_noop minor cs addr
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      CheneySpec.cheney_forward_one_noop_wz0 minor cs addr
    else begin
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        CheneySpec.cheney_forward_one_noop_oom minor cs addr
      else begin
        CheneySpec.cheney_forward_one_success minor cs addr;
        let cs' = CheneySpec.cheney_forward_one minor cs addr in
        forward_one_append_valid minor cs.cs_queue cs'.cs_queue addr
      end
    end
  end

#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --using_facts_from '* -GC.Gen.Cheney.cheney_forward_one'"

let cheney_forward_one_queue_bound
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (ensures (let cs' = CheneySpec.cheney_forward_one minor cs addr in
                    Seq.length cs'.cs_queue <= Seq.length cs.cs_queue + 1))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    CheneySpec.cheney_forward_one_noop minor cs addr
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      CheneySpec.cheney_forward_one_noop_wz0 minor cs addr
    else begin
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        CheneySpec.cheney_forward_one_noop_oom minor cs addr
      else begin
        CheneySpec.cheney_forward_one_success minor cs addr;
        Seq.Base.lemma_len_append cs.cs_queue (Seq.create 1 addr)
      end
    end
  end

#pop-options

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

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"

private let rec forward_fields_qv_aux
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma
    (requires queue_valid minor cs.cs_queue)
    (ensures queue_valid minor (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_queue)
    (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then
    CheneySpec.cheney_forward_fields_base minor cs parent idx wosize
  else begin
    CheneySpec.cheney_forward_fields_step minor cs parent idx wosize;
    let field_val = minor_read_field minor parent idx in
    let cs' = CheneySpec.cheney_forward_one minor cs field_val in
    fwd_one_preserves_queue_valid minor cs field_val;
    forward_fields_qv_aux minor cs' parent (idx + 1) wosize
  end

let forward_fields_preserves_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires queue_valid minor cs.cs_queue)
          (ensures queue_valid minor (CheneySpec.cheney_forward_fields minor cs parent idx wosize).cs_queue)
  = forward_fields_qv_aux minor cs parent idx wosize

private let rec forward_roots_qv_aux
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma
    (requires queue_valid minor cs.cs_queue)
    (ensures queue_valid minor (CheneySpec.cheney_forward_roots minor cs roots idx).cs_queue)
    (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  =
  if idx >= Seq.length roots then
    CheneySpec.cheney_forward_roots_base minor cs roots idx
  else begin
    CheneySpec.cheney_forward_roots_step minor cs roots idx;
    let r = Seq.index roots idx in
    let cs' = CheneySpec.cheney_forward_one minor cs r in
    fwd_one_preserves_queue_valid minor cs r;
    forward_roots_qv_aux minor cs' roots (idx + 1)
  end

let forward_roots_preserves_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires queue_valid minor cs.cs_queue)
          (ensures queue_valid minor (CheneySpec.cheney_forward_roots minor cs roots idx).cs_queue)
  = forward_roots_qv_aux minor cs roots idx

private let rec scan_qv_aux
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma
    (requires queue_valid minor cs.cs_queue)
    (ensures queue_valid minor (CheneySpec.cheney_scan minor cs scan fuel).cs_queue)
    (decreases fuel)
  =
  if fuel = 0 || scan >= Seq.length cs.cs_queue then
    CheneySpec.cheney_scan_base minor cs scan fuel
  else begin
    CheneySpec.cheney_scan_step minor cs scan fuel;
    let obj = Seq.index cs.cs_queue scan in
    let wz = minor_wosize minor obj in
    let cs' = CheneySpec.cheney_forward_fields minor cs obj 0 wz in
    forward_fields_qv_aux minor cs obj 0 wz;
    scan_qv_aux minor cs' (scan + 1) (fuel - 1)
  end

let scan_preserves_queue_valid
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires queue_valid minor cs.cs_queue)
          (ensures queue_valid minor (CheneySpec.cheney_scan minor cs scan fuel).cs_queue)
  = scan_qv_aux minor cs scan fuel

#pop-options

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

/// count_unforwarded is bounded by the remaining length
private let rec count_unforwarded_bound (objs: seq U64.t) (fwd: forwarding_map) (i: nat)
  : Lemma (ensures count_unforwarded objs fwd i <= (if i < Seq.length objs then Seq.length objs - i else 0))
          (decreases (if i < Seq.length objs then Seq.length objs - i else 0))
  = if i >= Seq.length objs then ()
    else count_unforwarded_bound objs fwd (i + 1)

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

/// ---------------------------------------------------------------------------
/// Compound BFS invariant definition and lemmas
/// ---------------------------------------------------------------------------

let cheney_bfs_inv (minor: minor_state) (cs: CheneySpec.cheney_state) : prop =
  queue_valid minor cs.cs_queue /\
  (forall (j:nat). j < Seq.length cs.cs_queue ==>
    cs.cs_fwd (Seq.index cs.cs_queue j) <> 0UL) /\
  Seq.length cs.cs_queue + count_unforwarded (minor_objects minor) cs.cs_fwd 0
    <= Seq.length (minor_objects minor)

let cheney_bfs_inv_initial (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (requires cs.CheneySpec.cs_queue == Seq.empty /\
                    cs.CheneySpec.cs_fwd == empty_forwarding)
          (ensures cheney_bfs_inv minor cs)
  = queue_valid_intro minor Seq.empty;
    count_unforwarded_empty (minor_objects minor) 0

let cheney_bfs_inv_bound (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures Seq.length cs.CheneySpec.cs_queue <= Seq.length (minor_objects minor))
  = ()  // Direct from the invariant (count_unforwarded >= 0 by type nat)

let cheney_bfs_inv_valid (minor: minor_state) (cs: CheneySpec.cheney_state)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures queue_valid minor cs.CheneySpec.cs_queue)
  = ()

/// ---------------------------------------------------------------------------
/// Forward_one preserves BFS invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --using_facts_from '* -GC.Gen.Cheney.cheney_forward_one'"

private let fwd_one_bfs_inv_noop
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\
                    (~(Seq.mem addr (minor_objects minor)) \/ cs.cs_fwd addr <> 0UL))
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_one minor cs addr))
  = CheneySpec.cheney_forward_one_noop minor cs addr

private let fwd_one_bfs_inv_noop_wz0
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\
                    Seq.mem addr (minor_objects minor) /\
                    cs.cs_fwd addr = 0UL /\
                    minor_wosize minor addr = 0)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_one minor cs addr))
  = CheneySpec.cheney_forward_one_noop_wz0 minor cs addr

private let fwd_one_bfs_inv_noop_oom
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\
                    Seq.mem addr (minor_objects minor) /\
                    cs.cs_fwd addr = 0UL /\
                    minor_wosize minor addr > 0 /\
                    (promote_object minor cs.cs_major addr cs.cs_fp
                       (minor_wosize minor addr)).new_addr = 0UL)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_one minor cs addr))
  = CheneySpec.cheney_forward_one_noop_oom minor cs addr

#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0 --using_facts_from '* -GC.Gen.Cheney.cheney_forward_one'"

private let fwd_one_bfs_inv_success
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs /\
                    Seq.mem addr (minor_objects minor) /\
                    cs.cs_fwd addr = 0UL /\
                    minor_wosize minor addr > 0 /\
                    (promote_object minor cs.cs_major addr cs.cs_fp
                       (minor_wosize minor addr)).new_addr <> 0UL)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_one minor cs addr))
  =
  let wz = minor_wosize minor addr in
  let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
  CheneySpec.cheney_forward_one_success minor cs addr;
  let cs' = CheneySpec.cheney_forward_one minor cs addr in
  // cs'.cs_queue = append cs.cs_queue [addr]
  // cs'.cs_fwd = extend_forwarding cs.cs_fwd addr res.new_addr
  let fwd' = extend_forwarding cs.cs_fwd addr res.new_addr in
  // (1) queue_valid: addr is a minor object, old queue was valid
  forward_one_append_valid minor cs.cs_queue cs'.cs_queue addr;
  // (2) queue_fwd_consistent for new queue:
  //   - Old entries: fwd' x = fwd x (for x <> addr), and fwd x <> 0UL by invariant
  //   - New entry (addr): fwd' addr = res.new_addr <> 0UL
  let aux_fwd (j: nat{j < Seq.length cs'.cs_queue})
    : Lemma (cs'.cs_fwd (Seq.index cs'.cs_queue j) <> 0UL)
    = Seq.Base.lemma_len_append cs.cs_queue (Seq.create 1 addr);
      if j < Seq.length cs.cs_queue then begin
        Seq.Base.lemma_index_app1 cs.cs_queue (Seq.create 1 addr) j;
        let entry = Seq.index cs.cs_queue j in
        // entry <> addr because entry has fwd set but addr has fwd == 0
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
  // (3) Potential decreases: addr is in minor_objects and was unforwarded
  //     After extend_forwarding, count_unforwarded decreases by at least 1
  FStar.Classical.exists_intro
    (fun (k:nat) -> k >= 0 /\ k < Seq.length (minor_objects minor) /\
                    Seq.index (minor_objects minor) k == addr)
    (Seq.index_mem addr (minor_objects minor));
  count_unforwarded_decrease (minor_objects minor) cs.cs_fwd addr res.new_addr 0;
  // Now: count_unforwarded objs fwd' 0 + 1 <= count_unforwarded objs fwd 0
  // Combined with invariant: |queue| + count_unforwarded objs fwd 0 <= |minor_objects|
  // Get: (|queue| + 1) + count_unforwarded objs fwd' 0 <= |minor_objects|
  Seq.Base.lemma_len_append cs.cs_queue (Seq.create 1 addr)

#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0 --using_facts_from '* -GC.Gen.Cheney.cheney_forward_one'"

let fwd_one_preserves_bfs_inv
  (minor: minor_state) (cs: CheneySpec.cheney_state) (addr: U64.t)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_one minor cs addr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL then
    fwd_one_bfs_inv_noop minor cs addr
  else begin
    let wz = minor_wosize minor addr in
    if wz = 0 then
      fwd_one_bfs_inv_noop_wz0 minor cs addr
    else begin
      let res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      if res.new_addr = 0UL then
        fwd_one_bfs_inv_noop_oom minor cs addr
      else
        fwd_one_bfs_inv_success minor cs addr
    end
  end

#pop-options

/// ---------------------------------------------------------------------------
/// Recursive BFS invariant preservation
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"

private let rec forward_fields_bfs_inv_aux
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_fields minor cs parent idx wosize))
          (decreases (if idx < wosize then wosize - idx else 0))
  = if idx >= wosize then
      CheneySpec.cheney_forward_fields_base minor cs parent idx wosize
    else begin
      CheneySpec.cheney_forward_fields_step minor cs parent idx wosize;
      let field_val = minor_read_field minor parent idx in
      let cs' = CheneySpec.cheney_forward_one minor cs field_val in
      fwd_one_preserves_bfs_inv minor cs field_val;
      forward_fields_bfs_inv_aux minor cs' parent (idx + 1) wosize
    end

let forward_fields_preserves_bfs_inv
  (minor: minor_state) (cs: CheneySpec.cheney_state) (parent: U64.t) (idx: nat) (wosize: nat)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_fields minor cs parent idx wosize))
  = forward_fields_bfs_inv_aux minor cs parent idx wosize

private let rec forward_roots_bfs_inv_aux
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_roots minor cs roots idx))
          (decreases (if idx < Seq.length roots then Seq.length roots - idx else 0))
  = if idx >= Seq.length roots then
      CheneySpec.cheney_forward_roots_base minor cs roots idx
    else begin
      CheneySpec.cheney_forward_roots_step minor cs roots idx;
      let r = Seq.index roots idx in
      let cs' = CheneySpec.cheney_forward_one minor cs r in
      fwd_one_preserves_bfs_inv minor cs r;
      forward_roots_bfs_inv_aux minor cs' roots (idx + 1)
    end

let forward_roots_preserves_bfs_inv
  (minor: minor_state) (cs: CheneySpec.cheney_state) (roots: seq U64.t) (idx: nat)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_forward_roots minor cs roots idx))
  = forward_roots_bfs_inv_aux minor cs roots idx

private let rec scan_bfs_inv_aux
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_scan minor cs scan fuel))
          (decreases fuel)
  = if fuel = 0 || scan >= Seq.length cs.cs_queue then
      CheneySpec.cheney_scan_base minor cs scan fuel
    else begin
      CheneySpec.cheney_scan_step minor cs scan fuel;
      let obj = Seq.index cs.cs_queue scan in
      let wz = minor_wosize minor obj in
      let cs' = CheneySpec.cheney_forward_fields minor cs obj 0 wz in
      forward_fields_bfs_inv_aux minor cs obj 0 wz;
      scan_bfs_inv_aux minor cs' (scan + 1) (fuel - 1)
    end

let scan_preserves_bfs_inv
  (minor: minor_state) (cs: CheneySpec.cheney_state) (scan: nat) (fuel: nat)
  : Lemma (requires cheney_bfs_inv minor cs)
          (ensures cheney_bfs_inv minor (CheneySpec.cheney_scan minor cs scan fuel))
  = scan_bfs_inv_aux minor cs scan fuel

#pop-options
