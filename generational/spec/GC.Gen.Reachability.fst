/// ---------------------------------------------------------------------------
/// GC.Gen.Reachability — Implementation of minor-heap reachability
/// ---------------------------------------------------------------------------

module GC.Gen.Reachability

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap

/// ---------------------------------------------------------------------------
/// Helper: collect successors from fields
/// ---------------------------------------------------------------------------

/// Iterate over fields [idx, wosize) and collect those that are valid
/// intra-minor pointers to allocated objects.
let rec collect_minor_successors
  (ms: minor_state)
  (obj: U64.t)
  (idx: nat)
  (wosize: nat)
  : GTot (seq U64.t)
         (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then Seq.empty
  else
    let field_val = minor_read_field ms obj idx in
    let rest = collect_minor_successors ms obj (idx + 1) wosize in
    if is_minor_addr field_val && Seq.mem field_val (minor_objects ms)
    then Seq.cons field_val rest
    else rest

/// ---------------------------------------------------------------------------
/// minor_successors
/// ---------------------------------------------------------------------------

let minor_successors (ms: minor_state) (obj: U64.t) : GTot (seq U64.t) =
  collect_minor_successors ms obj 0 (minor_wosize ms obj)

/// ---------------------------------------------------------------------------
/// Helper lemma: every element collected is in minor_objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"

let rec collect_minor_successors_valid
  (ms: minor_state)
  (obj: U64.t)
  (idx: nat)
  (wosize: nat)
  (x: U64.t)
  : Lemma
    (requires Seq.mem x (collect_minor_successors ms obj idx wosize))
    (ensures Seq.mem x (minor_objects ms))
    (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else
    let field_val = minor_read_field ms obj idx in
    let rest = collect_minor_successors ms obj (idx + 1) wosize in
    if is_minor_addr field_val && Seq.mem field_val (minor_objects ms)
    then begin
      // result = Seq.cons field_val rest = append (create 1 field_val) rest
      Seq.lemma_mem_append (Seq.create 1 field_val) rest;
      // mem x (cons field_val rest) <==> mem x (create 1 field_val) || mem x rest
      if x = field_val then ()
      else
        // x must be in rest
        collect_minor_successors_valid ms obj (idx + 1) wosize x
    end
    else
      collect_minor_successors_valid ms obj (idx + 1) wosize x

#pop-options

let minor_successors_valid (ms: minor_state) (obj: U64.t) (x: U64.t)
  : Lemma (requires Seq.mem x (minor_successors ms obj))
          (ensures Seq.mem x (minor_objects ms))
  =
  collect_minor_successors_valid ms obj 0 (minor_wosize ms obj) x

/// ---------------------------------------------------------------------------
/// BFS worklist algorithm for reachability
/// ---------------------------------------------------------------------------

/// Worklist-based BFS: process items from worklist, adding unvisited
/// valid minor objects and their successors.
let rec minor_reachable_aux
  (ms: minor_state)
  (worklist: seq U64.t)
  (visited: seq U64.t)
  (fuel: nat)
  : GTot (seq U64.t)
         (decreases fuel)
  =
  if fuel = 0 || Seq.length worklist = 0
  then visited
  else
    let obj = Seq.index worklist 0 in
    let rest = Seq.slice worklist 1 (Seq.length worklist) in
    if Seq.mem obj visited || not (Seq.mem obj (minor_objects ms))
    then
      // Skip: already visited or not a valid minor object
      minor_reachable_aux ms rest visited (fuel - 1)
    else
      // Process: add to visited, enqueue successors
      let succs = minor_successors ms obj in
      let new_worklist = Seq.append rest succs in
      let new_visited = Seq.cons obj visited in
      minor_reachable_aux ms new_worklist new_visited (fuel - 1)

/// Fuel bound: large enough to guarantee the BFS exhausts the worklist.
/// Each of the at most n objects is processed once, adding < minor_heap_size
/// successors. So total worklist items ≤ |roots| + n * minor_heap_size.
let minor_reachable_fuel (ms: minor_state) (roots: seq U64.t) : GTot nat =
  Seq.length roots + (Seq.length (minor_objects ms) + 1) * minor_heap_size

/// ---------------------------------------------------------------------------
/// minor_reachable
/// ---------------------------------------------------------------------------

let minor_reachable (ms: minor_state) (roots: seq U64.t) : GTot (seq U64.t) =
  minor_reachable_aux ms roots Seq.empty (minor_reachable_fuel ms roots)

/// ---------------------------------------------------------------------------
/// Proof: subset property
/// ---------------------------------------------------------------------------

/// Key insight: visited only grows with items from minor_objects.
/// We maintain the invariant that visited ⊆ minor_objects.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"

let rec minor_reachable_aux_subset
  (ms: minor_state)
  (worklist: seq U64.t)
  (visited: seq U64.t)
  (fuel: nat)
  (x: U64.t)
  : Lemma
    (requires Seq.mem x (minor_reachable_aux ms worklist visited fuel) /\
              (forall v. Seq.mem v visited ==> Seq.mem v (minor_objects ms)))
    (ensures Seq.mem x (minor_objects ms))
    (decreases fuel)
  =
  if fuel = 0 || Seq.length worklist = 0
  then ()
  else
    let obj = Seq.index worklist 0 in
    let rest = Seq.slice worklist 1 (Seq.length worklist) in
    if Seq.mem obj visited || not (Seq.mem obj (minor_objects ms))
    then
      minor_reachable_aux_subset ms rest visited (fuel - 1) x
    else begin
      let succs = minor_successors ms obj in
      let new_worklist = Seq.append rest succs in
      let new_visited = Seq.cons obj visited in
      // Establish: forall v. mem v new_visited ==> mem v (minor_objects ms)
      Seq.lemma_mem_append (Seq.create 1 obj) visited;
      Seq.seq_mem_k #U64.t (Seq.create 1 obj) 0;
      minor_reachable_aux_subset ms new_worklist new_visited (fuel - 1) x
    end

#pop-options

let minor_reachable_subset (ms: minor_state) (roots: seq U64.t)
  : Lemma (ensures forall x. Seq.mem x (minor_reachable ms roots) ==>
                             Seq.mem x (minor_objects ms))
  =
  let aux (x: U64.t)
    : Lemma (requires Seq.mem x (minor_reachable ms roots))
            (ensures Seq.mem x (minor_objects ms))
    = minor_reachable_aux_subset ms roots Seq.empty (minor_reachable_fuel ms roots) x
  in
  Classical.forall_intro (Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Proof: roots property
/// ---------------------------------------------------------------------------

/// Helper: anything in visited stays in the output (visited is monotone)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"

let rec minor_reachable_aux_mem_visited
  (ms: minor_state)
  (worklist: seq U64.t)
  (visited: seq U64.t)
  (fuel: nat)
  (x: U64.t)
  : Lemma
    (requires Seq.mem x visited)
    (ensures Seq.mem x (minor_reachable_aux ms worklist visited fuel))
    (decreases fuel)
  =
  if fuel = 0 || Seq.length worklist = 0
  then ()
  else
    let obj = Seq.index worklist 0 in
    let rest = Seq.slice worklist 1 (Seq.length worklist) in
    if Seq.mem obj visited || not (Seq.mem obj (minor_objects ms))
    then
      minor_reachable_aux_mem_visited ms rest visited (fuel - 1) x
    else begin
      let succs = minor_successors ms obj in
      let new_worklist = Seq.append rest succs in
      let new_visited = Seq.cons obj visited in
      // x was in visited, so x is in new_visited (cons only adds)
      Seq.lemma_mem_append (Seq.create 1 obj) visited;
      minor_reachable_aux_mem_visited ms new_worklist new_visited (fuel - 1) x
    end

#pop-options

/// Helper: if the head of the worklist is a valid minor object, it ends up in the output
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"

let minor_reachable_aux_processes_head
  (ms: minor_state)
  (worklist: seq U64.t)
  (visited: seq U64.t)
  (fuel: nat)
  : Lemma
    (requires Seq.length worklist > 0 /\ fuel > 0 /\
              Seq.mem (Seq.index worklist 0) (minor_objects ms))
    (ensures Seq.mem (Seq.index worklist 0) (minor_reachable_aux ms worklist visited fuel))
  =
  let obj = Seq.index worklist 0 in
  let rest = Seq.slice worklist 1 (Seq.length worklist) in
  if Seq.mem obj visited || not (Seq.mem obj (minor_objects ms))
  then
    // obj is already in visited, so it's in the output by monotonicity
    minor_reachable_aux_mem_visited ms rest visited (fuel - 1) obj
  else begin
    // obj gets added to new_visited
    let succs = minor_successors ms obj in
    let new_worklist = Seq.append rest succs in
    let new_visited = Seq.cons obj visited in
    // obj is head of new_visited
    Seq.lemma_mem_append (Seq.create 1 obj) visited;
    Seq.seq_mem_k #U64.t (Seq.create 1 obj) 0;
    minor_reachable_aux_mem_visited ms new_worklist new_visited (fuel - 1) obj
  end

#pop-options

/// Helper: position-based induction — if r is at position `pos` in the worklist,
/// is a valid minor object, and fuel > pos, then r ends up in the output.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"

let rec minor_reachable_aux_at_pos
  (ms: minor_state)
  (worklist: seq U64.t)
  (visited: seq U64.t)
  (fuel: nat)
  (r: U64.t)
  (pos: nat)
  : Lemma
    (requires pos < Seq.length worklist /\
              Seq.index worklist pos = r /\
              Seq.mem r (minor_objects ms) /\
              fuel > pos)
    (ensures Seq.mem r (minor_reachable_aux ms worklist visited fuel))
    (decreases pos)
  =
  if pos = 0 then
    // r is the head of the worklist
    minor_reachable_aux_processes_head ms worklist visited fuel
  else begin
    // pos > 0: r is not the head. After one BFS step, r's position decreases.
    let obj = Seq.index worklist 0 in
    let rest = Seq.slice worklist 1 (Seq.length worklist) in
    // r is at position pos-1 in rest
    assert (Seq.index rest (pos - 1) == r);
    if Seq.mem obj visited || not (Seq.mem obj (minor_objects ms))
    then
      // Skip case: recurse on rest with fuel-1, pos-1
      minor_reachable_aux_at_pos ms rest visited (fuel - 1) r (pos - 1)
    else begin
      // Process case: new_worklist = append rest succs
      let succs = minor_successors ms obj in
      let new_worklist = Seq.append rest succs in
      let new_visited = Seq.cons obj visited in
      // r is at position pos-1 in rest, which is pos-1 < length rest <= length new_worklist
      Seq.lemma_mem_append rest succs;
      assert (pos - 1 < Seq.length rest);
      assert (Seq.index new_worklist (pos - 1) == r);
      minor_reachable_aux_at_pos ms new_worklist new_visited (fuel - 1) r (pos - 1)
    end
  end

#pop-options

/// Helper: obtain witness position from Seq.mem
let rec seq_mem_to_index (#a: eqtype) (x: a) (s: seq a)
  : Ghost nat
    (requires Seq.mem x s)
    (ensures fun i -> i < Seq.length s /\ Seq.index s i = x)
    (decreases Seq.length s)
  =
  if Seq.index s 0 = x then 0
  else begin
    let tl = Seq.slice s 1 (Seq.length s) in
    Seq.lemma_count_slice s 1;
    1 + seq_mem_to_index x tl
  end

let minor_reachable_roots (ms: minor_state) (roots: seq U64.t)
  : Lemma (ensures forall r. Seq.mem r roots /\ Seq.mem r (minor_objects ms) ==>
                             Seq.mem r (minor_reachable ms roots))
  =
  let fuel = minor_reachable_fuel ms roots in
  let aux (r: U64.t)
    : Lemma (requires Seq.mem r roots /\ Seq.mem r (minor_objects ms))
            (ensures Seq.mem r (minor_reachable ms roots))
    =
    let pos = seq_mem_to_index r roots in
    // pos < length roots, fuel >= length roots > pos
    minor_reachable_aux_at_pos ms roots Seq.empty fuel r pos
  in
  Classical.forall_intro (Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Proof: closure property
/// ---------------------------------------------------------------------------

/// Length bound on collect_minor_successors
let rec collect_minor_successors_length
  (ms: minor_state)
  (obj: U64.t)
  (idx: nat)
  (wosize: nat)
  : Lemma
    (ensures Seq.length (collect_minor_successors ms obj idx wosize) <=
               (if idx < wosize then wosize - idx else 0))
    (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    collect_minor_successors_length ms obj (idx + 1) wosize;
    let field_val = minor_read_field ms obj idx in
    let rest = collect_minor_successors ms obj (idx + 1) wosize in
    if is_minor_addr field_val && Seq.mem field_val (minor_objects ms)
    then ()
    else ()
  end

/// Length of minor_successors bounded by wosize
let minor_successors_length (ms: minor_state) (obj: U64.t)
  : Lemma (ensures Seq.length (minor_successors ms obj) <= minor_wosize ms obj)
  = collect_minor_successors_length ms obj 0 (minor_wosize ms obj)

/// For objects in minor_objects, successors length < minor_heap_size
let minor_successors_length_bound (ms: minor_state) (obj: U64.t)
  : Lemma (requires Seq.mem obj (minor_objects ms))
          (ensures Seq.length (minor_successors ms obj) < minor_heap_size)
  =
  minor_successors_length ms obj;
  minor_objects_wosize_bound ms obj
  // (minor_wosize ms obj + 1) * 8 <= minor_heap_size
  // so minor_wosize ms obj <= minor_heap_size / 8 - 1 < minor_heap_size

/// Characterization of collect_minor_successors
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec collect_minor_successors_char
  (ms: minor_state)
  (obj: U64.t)
  (idx: nat)
  (wosize: nat)
  (y: U64.t)
  : Lemma
    (ensures Seq.mem y (collect_minor_successors ms obj idx wosize) <==>
             (exists (i:nat). idx <= i /\ i < wosize /\
                              minor_read_field ms obj i == y /\
                              is_minor_addr y /\
                              Seq.mem y (minor_objects ms)))
    (decreases (if idx < wosize then wosize - idx else 0))
  =
  if idx >= wosize then ()
  else begin
    let field_val = minor_read_field ms obj idx in
    let rest = collect_minor_successors ms obj (idx + 1) wosize in
    collect_minor_successors_char ms obj (idx + 1) wosize y;
    if is_minor_addr field_val && Seq.mem field_val (minor_objects ms)
    then Seq.mem_cons field_val rest
    else ()
  end
#pop-options

/// Characterization: y ∈ minor_successors ms x iff a field of x equals y
/// and y is a valid minor-heap object
let minor_successors_char (ms: minor_state) (x y: U64.t)
  : Lemma (ensures Seq.mem y (minor_successors ms x) <==>
                   (exists (i:nat). i < minor_wosize ms x /\
                                    minor_read_field ms x i == y /\
                                    is_minor_addr y /\
                                    Seq.mem y (minor_objects ms)))
  = collect_minor_successors_char ms x 0 (minor_wosize ms x) y

/// Count of elements in `objects` that are not in `visited`
let rec count_not_mem (objects visited: seq U64.t) : GTot nat
  (decreases Seq.length objects) =
  if Seq.length objects = 0 then 0
  else
    let hd = Seq.index objects 0 in
    let tl = Seq.slice objects 1 (Seq.length objects) in
    (if Seq.mem hd visited then 0 else 1) + count_not_mem tl visited

/// count_not_mem is bounded by the length of objects
let rec count_not_mem_bound (objects visited: seq U64.t)
  : Lemma (ensures count_not_mem objects visited <= Seq.length objects)
          (decreases Seq.length objects)
  =
  if Seq.length objects = 0 then ()
  else count_not_mem_bound (Seq.slice objects 1 (Seq.length objects)) visited

/// If x ∈ objects and x ∉ visited, count is at least 1
let rec count_not_mem_positive (objects: seq U64.t) (x: U64.t) (visited: seq U64.t)
  : Lemma (requires Seq.mem x objects /\ not (Seq.mem x visited))
          (ensures count_not_mem objects visited >= 1)
          (decreases Seq.length objects)
  =
  if Seq.length objects = 0 then ()
  else begin
    let hd = Seq.index objects 0 in
    let tl = Seq.slice objects 1 (Seq.length objects) in
    if hd = x then ()  // hd not in visited => contributes 1
    else begin
      Seq.lemma_count_slice objects 1;
      count_not_mem_positive tl x visited
    end
  end

/// Adding a fresh element to visited decreases count by at least 1
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"

let rec count_not_mem_cons_mem (objects: seq U64.t) (x: U64.t) (visited: seq U64.t)
  : Lemma
    (requires Seq.mem x objects /\ not (Seq.mem x visited))
    (ensures count_not_mem objects (Seq.cons x visited) <= count_not_mem objects visited - 1)
    (decreases Seq.length objects)
  =
  if Seq.length objects = 0 then ()
  else begin
    let hd = Seq.index objects 0 in
    let tl = Seq.slice objects 1 (Seq.length objects) in
    Seq.mem_cons x visited;
    if hd = x then begin
      // hd = x, not in visited: old contributes 1, new contributes 0
      // For tail: count_not_mem tl (cons x vis) <= count_not_mem tl vis
      // (monotonicity — adding to visited can't increase count)
      count_not_mem_monotone tl x visited
    end
    else begin
      // hd ≠ x: contributions are the same (mem hd (cons x vis) ↔ mem hd vis)
      // x must be in tl
      Seq.lemma_count_slice objects 1;
      count_not_mem_cons_mem tl x visited
    end
  end

and count_not_mem_monotone (objects: seq U64.t) (x: U64.t) (visited: seq U64.t)
  : Lemma
    (ensures count_not_mem objects (Seq.cons x visited) <= count_not_mem objects visited)
    (decreases Seq.length objects)
  =
  if Seq.length objects = 0 then ()
  else begin
    Seq.mem_cons x visited;
    count_not_mem_monotone (Seq.slice objects 1 (Seq.length objects)) x visited
  end

#pop-options

/// ---------------------------------------------------------------------------
/// Main inductive closure lemma
/// ---------------------------------------------------------------------------

/// The BFS result is closed under successors for any object x that appears
/// in the output but NOT in the initial visited set.
/// Key invariant: fuel >= |worklist| + count_not_mem(minor_objects, visited) * minor_heap_size
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"

let rec minor_reachable_aux_closed_aux
  (ms: minor_state)
  (worklist: seq U64.t)
  (visited: seq U64.t)
  (fuel: nat)
  (x y: U64.t)
  : Lemma
    (requires
      Seq.mem x (minor_reachable_aux ms worklist visited fuel) /\
      not (Seq.mem x visited) /\
      Seq.mem y (minor_successors ms x) /\
      Seq.mem y (minor_objects ms) /\
      // All visited are valid minor objects
      (forall v. Seq.mem v visited ==> Seq.mem v (minor_objects ms)) /\
      // Sufficient fuel
      fuel >= Seq.length worklist +
              count_not_mem (minor_objects ms) visited * minor_heap_size)
    (ensures Seq.mem y (minor_reachable_aux ms worklist visited fuel))
    (decreases fuel)
  =
  if fuel = 0 || Seq.length worklist = 0
  then
    // Base case: output = visited, x ∈ visited contradicts ¬(mem x visited).
    // So precondition is false and this is vacuously true.
    ()
  else begin
    let obj = Seq.index worklist 0 in
    let rest = Seq.slice worklist 1 (Seq.length worklist) in
    if Seq.mem obj visited || not (Seq.mem obj (minor_objects ms))
    then begin
      // Skip case: result = minor_reachable_aux ms rest visited (fuel - 1)
      // count unchanged, |rest| = |wl| - 1, fuel - 1 >= |rest| + count * mhs
      minor_reachable_aux_closed_aux ms rest visited (fuel - 1) x y
    end
    else begin
      // Process case: obj ∉ visited, obj ∈ minor_objects
      let succs = minor_successors ms obj in
      let new_worklist = Seq.append rest succs in
      let new_visited = Seq.cons obj visited in
      let fuel' : nat = fuel - 1 in
      // Establish all new_visited ⊆ minor_objects
      Seq.mem_cons obj visited;
      // Arithmetic for fuel condition:
      //   count' = count_not_mem(minor_objects, new_visited) <= count - 1
      //   |succs| < minor_heap_size
      //   |new_wl| = |rest| + |succs|
      //   fuel - 1 >= |wl| - 1 + count * mhs = |rest| + count * mhs
      //            >= |rest| + (count' + 1) * mhs = |rest| + count' * mhs + mhs
      //            > |rest| + |succs| + count' * mhs = |new_wl| + count' * mhs
      minor_successors_length_bound ms obj;
      count_not_mem_cons_mem (minor_objects ms) obj visited;
      if x = obj then begin
        // x is being processed — its successors are enqueued
        // y ∈ succs(x) = succs(obj) = succs
        // y ∈ minor_objects (given)
        if Seq.mem y new_visited then
          // y already in visited set — it's in the output by monotonicity
          minor_reachable_aux_mem_visited ms new_worklist new_visited fuel' y
        else begin
          // y is in succs, hence in new_worklist
          Seq.lemma_mem_append rest succs;
          assert (Seq.mem y new_worklist);
          let pos = seq_mem_to_index y new_worklist in
          // Arithmetic: fuel' > pos
          let count = count_not_mem (minor_objects ms) visited in
          count_not_mem_positive (minor_objects ms) obj visited;
          FStar.Math.Lemmas.lemma_mult_le_right minor_heap_size 1 count;
          minor_reachable_aux_at_pos ms new_worklist new_visited fuel' y pos
        end
      end
      else begin
        // x ≠ obj: x is not yet processed, still not in new_visited
        // Apply IH on (new_worklist, new_visited, fuel-1)
        // Establish fuel precondition with explicit NL arithmetic
        let count = count_not_mem (minor_objects ms) visited in
        let count' = count_not_mem (minor_objects ms) new_visited in
        assert (count' <= count - 1);
        assert (Seq.length succs < minor_heap_size);
        FStar.Math.Lemmas.lemma_mult_le_right minor_heap_size count' (count - 1);
        FStar.Math.Lemmas.distributivity_sub_left count 1 minor_heap_size;
        assert (count' * minor_heap_size <= (count - 1) * minor_heap_size);
        assert (fuel' >= Seq.length new_worklist + count' * minor_heap_size);
        // x ≠ obj and x ∉ visited implies x ∉ new_visited
        Seq.mem_cons obj visited;
        minor_reachable_aux_closed_aux ms new_worklist new_visited fuel' x y
      end
    end
  end

#pop-options

/// Top-level closure lemma
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"

let minor_reachable_closed (ms: minor_state) (roots: seq U64.t) (x y: U64.t)
  : Lemma (requires Seq.mem x (minor_reachable ms roots) /\
                    Seq.mem y (minor_successors ms x))
          (ensures Seq.mem y (minor_reachable ms roots))
  =
  minor_successors_valid ms x y;
  // Initial: visited = empty, so not (mem x empty) is trivially true.
  // Fuel condition: fuel = |roots| + (n+1)*mhs
  //   count_not_mem(minor_objects, empty) <= n (by count_not_mem_bound)
  //   So fuel >= |roots| + (n+1)*mhs >= |roots| + n*mhs >= |roots| + count*mhs
  count_not_mem_bound (minor_objects ms) (Seq.empty #U64.t);
  minor_reachable_aux_closed_aux ms roots Seq.empty
    (minor_reachable_fuel ms roots) x y

#pop-options

/// ---------------------------------------------------------------------------
/// Proof: induction principle (least fixed point)
/// ---------------------------------------------------------------------------

/// Helper: if a predicate holds for all visited and worklist members,
/// and is closed under successors, then it holds for all BFS output.
#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"

let rec minor_reachable_aux_ind
  (ms: minor_state)
  (worklist: seq U64.t)
  (visited: seq U64.t)
  (fuel: nat)
  (p: U64.t -> prop)
  (x: U64.t)
  : Lemma
    (requires
      Seq.mem x (minor_reachable_aux ms worklist visited fuel) /\
      (forall v. Seq.mem v visited ==> p v) /\
      (forall w. Seq.mem w worklist /\ Seq.mem w (minor_objects ms) ==> p w) /\
      (forall a b. p a /\ Seq.mem b (minor_successors ms a) ==> p b))
    (ensures p x)
    (decreases fuel)
  =
  if fuel = 0 || Seq.length worklist = 0
  then ()
  else begin
    let obj = Seq.index worklist 0 in
    let rest = Seq.slice worklist 1 (Seq.length worklist) in
    assert (forall (i:nat). i < Seq.length rest ==>
              Seq.index rest i == Seq.index worklist (i + 1));
    if Seq.mem obj visited || not (Seq.mem obj (minor_objects ms))
    then begin
      let aux_rest (w: U64.t)
        : Lemma (requires Seq.mem w rest /\ Seq.mem w (minor_objects ms))
                (ensures p w)
        = let i = seq_mem_to_index w rest in
          assert (Seq.index worklist (i + 1) == w);
          Seq.lemma_index_is_nth worklist (i + 1);
          Seq.lemma_count_slice worklist (i + 1);
          assert (Seq.mem w worklist)
      in
      Classical.forall_intro (Classical.move_requires aux_rest);
      minor_reachable_aux_ind ms rest visited (fuel - 1) p x
    end
    else begin
      let succs = minor_successors ms obj in
      let new_worklist = Seq.append rest succs in
      let new_visited = Seq.cons obj visited in
      Seq.lemma_index_is_nth worklist 0;
      assert (Seq.mem obj worklist);
      assert (p obj);
      Seq.mem_cons obj visited;
      let aux_rest (w: U64.t)
        : Lemma (requires Seq.mem w rest /\ Seq.mem w (minor_objects ms))
                (ensures p w)
        = let i = seq_mem_to_index w rest in
          assert (Seq.index worklist (i + 1) == w);
          Seq.lemma_index_is_nth worklist (i + 1);
          Seq.lemma_count_slice worklist (i + 1);
          assert (Seq.mem w worklist)
      in
      Classical.forall_intro (Classical.move_requires aux_rest);
      assert (forall s. Seq.mem s succs ==> p s);
      Seq.lemma_mem_append rest succs;
      let aux_nw (w: U64.t)
        : Lemma (requires Seq.mem w new_worklist /\ Seq.mem w (minor_objects ms))
                (ensures p w)
        = ()
      in
      Classical.forall_intro (Classical.move_requires aux_nw);
      minor_reachable_aux_ind ms new_worklist new_visited (fuel - 1) p x
    end
  end

#pop-options

let minor_reachable_ind (ms: minor_state) (roots: seq U64.t) (p: U64.t -> prop) (x: U64.t)
  : Lemma (requires
             Seq.mem x (minor_reachable ms roots) /\
             (forall r. Seq.mem r roots /\ Seq.mem r (minor_objects ms) ==> p r) /\
             (forall a b. p a /\ Seq.mem b (minor_successors ms a) ==> p b))
          (ensures p x)
  =
  minor_reachable_aux_ind ms roots Seq.empty (minor_reachable_fuel ms roots) p x
