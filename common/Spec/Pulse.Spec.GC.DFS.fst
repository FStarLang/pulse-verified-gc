/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.DFS - DFS Traversal for Reachability Proofs
/// ---------------------------------------------------------------------------
///
/// This module provides DFS-based proofs for GC correctness:
/// - dfs: depth-first traversal algorithm
/// - dfs_lemma_forward: soundness (visited => reachable)
/// - dfs_lemma_backward: completeness (reachable => visited)
///
/// Ported from: Proofs/DFS2.fst

module Pulse.Spec.GC.DFS

open FStar.Seq
open FStar.Classical
open FStar.Ghost
module U64 = FStar.UInt64

open Pulse.Spec.GC.Graph

/// ---------------------------------------------------------------------------
/// Helper Functions for DFS
/// ---------------------------------------------------------------------------

/// Push unvisited successors onto stack
let rec push_unvisited_successors (g: graph_state{graph_wf g}) (succs: vertex_list) 
                                   (visited: vertex_set) (stack: vertex_set)
  : GTot vertex_set (decreases Seq.length succs)
  = if Seq.length succs = 0 then stack
    else 
      let s = Seq.head succs in
      let rest = push_unvisited_successors g (Seq.tail succs) visited stack in
      if Seq.mem s visited then rest
      else if Seq.mem s rest then rest
      else (
        is_vertex_set_cons s rest;
        Seq.cons s rest
      )

/// Lemma: push_unvisited_successors preserves elements from input stack
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec push_unvisited_successors_preserves_stack (g: graph_state{graph_wf g}) (succs: vertex_list)
                                                   (visited: vertex_set) (stack: vertex_set)
  : Lemma (ensures (forall y. Seq.mem y stack ==> 
                              Seq.mem y (push_unvisited_successors g succs visited stack)))
          (decreases Seq.length succs)
  = if Seq.length succs = 0 then ()
    else (
      let s = Seq.head succs in
      push_unvisited_successors_preserves_stack g (Seq.tail succs) visited stack;
      let rest = push_unvisited_successors g (Seq.tail succs) visited stack in
      if Seq.mem s visited then ()
      else if Seq.mem s rest then ()
      else (
        let result = Seq.cons s rest in
        let aux (y: vertex_id)
          : Lemma (Seq.mem y stack ==> Seq.mem y result)
          = if Seq.mem y stack then (
              assert (Seq.mem y rest); // from IH
              mem_cons_lemma y s rest
            )
        in
        FStar.Classical.forall_intro aux
      )
    )
#pop-options

/// Lemma: push_unvisited_successors preserves disjointness with visited
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec push_unvisited_successors_disjoint (g: graph_state{graph_wf g}) (succs: vertex_list)
                                            (visited: vertex_set) (stack: vertex_set)
  : Lemma (requires forall x. Seq.mem x visited ==> ~(Seq.mem x stack))
          (ensures (let result = push_unvisited_successors g succs visited stack in
                    forall x. Seq.mem x visited ==> ~(Seq.mem x result)))
          (decreases Seq.length succs)
  = if Seq.length succs = 0 then ()
    else (
      let s = Seq.head succs in
      // Prove for tail first
      push_unvisited_successors_disjoint g (Seq.tail succs) visited stack;
      let rest = push_unvisited_successors g (Seq.tail succs) visited stack in
      
      if Seq.mem s visited then (
        // Result is rest, which is already disjoint from visited
        ()
      ) else if Seq.mem s rest then (
        // Result is rest, which is already disjoint from visited
        ()
      ) else (
        // Result is cons s rest
        // Need to show: forall x in visited. ~(x in cons s rest)
        // i.e., forall x in visited. x <> s /\ ~(x in rest)
        // We know: s is not in visited (the check above)
        // We know: rest is disjoint from visited (by IH)
        let result = Seq.cons s rest in
        let aux (x: vertex_id) 
          : Lemma (Seq.mem x visited ==> ~(Seq.mem x result))
          = if Seq.mem x visited then (
              assert (~(Seq.mem x rest)); // By IH
              assert (s <> x); // Since s is not in visited
              mem_cons_lemma x s rest;
              assert (~(Seq.mem x result))
            )
        in
        FStar.Classical.forall_intro aux
      )
    )
#pop-options

/// Lemma: if y is in succs and y is not in visited, then y is in result
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec push_unvisited_successors_includes_new (g: graph_state{graph_wf g}) (succs: vertex_list)
                                                (visited: vertex_set) (stack: vertex_set)
                                                (y: vertex_id)
  : Lemma (requires Seq.mem y succs /\ ~(Seq.mem y visited))
          (ensures Seq.mem y (push_unvisited_successors g succs visited stack))
          (decreases Seq.length succs)
  = if Seq.length succs = 0 then ()
    else (
      let hd = Seq.head succs in
      let tl = Seq.tail succs in
      let rest = push_unvisited_successors g tl visited stack in
      
      if hd = y then (
        // y is the head, so it will be added (since y not in visited)
        if Seq.mem y visited then ()  // contradiction
        else if Seq.mem y rest then (
          // y is already in rest
          ()
        ) else (
          // y is added via Seq.cons
          let result = Seq.cons y rest in
          mem_cons_lemma y y rest
        )
      ) else (
        // y is in tail
        FStar.Seq.Properties.lemma_mem_append (Seq.create 1 hd) tl;
        assert (Seq.mem y tl);
        push_unvisited_successors_includes_new g tl visited stack y;
        assert (Seq.mem y rest);
        // Now show y is in final result
        if Seq.mem hd visited then ()
        else if Seq.mem hd rest then ()
        else (
          let result = Seq.cons hd rest in
          mem_cons_lemma y hd rest
        )
      )
    )
#pop-options

/// Lemma: if stack is a subset of vertices and all successors are in vertices,
/// then push_unvisited_successors result is also a subset
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec push_unvisited_successors_subset (g: graph_state{graph_wf g}) (succs: vertex_list)
                                          (visited: vertex_set) (stack: vertex_set)
  : Lemma (requires subset_vertices stack g.vertices /\
                    (forall s. Seq.mem s succs ==> mem_graph_vertex g s))
          (ensures (let result = push_unvisited_successors g succs visited stack in
                    subset_vertices result g.vertices))
          (decreases Seq.length succs)
  = if Seq.length succs = 0 then ()
    else (
      let s = Seq.head succs in
      // Prove for tail first
      push_unvisited_successors_subset g (Seq.tail succs) visited stack;
      let rest = push_unvisited_successors g (Seq.tail succs) visited stack in
      
      if Seq.mem s visited then (
        // Result is rest, which is already a subset
        ()
      ) else if Seq.mem s rest then (
        // Result is rest, which is already a subset
        ()
      ) else (
        // Result is cons s rest
        // Need to show: cons s rest is a subset of g.vertices
        // We know: s is a successor (from precondition), so s is in g.vertices
        // We know: rest is a subset of g.vertices (by IH)
        let result = Seq.cons s rest in
        let aux (x: vertex_id)
          : Lemma (Seq.mem x result ==> mem_graph_vertex g x)
          = if Seq.mem x result then (
              mem_cons_lemma x s rest;
              if x = s then
                assert (mem_graph_vertex g s) // from precondition
              else
                assert (Seq.mem x rest)  // so x in g.vertices by IH
            )
        in
        FStar.Classical.forall_intro aux
      )
    )
#pop-options

/// ---------------------------------------------------------------------------
/// Successors in Graph Lemma
/// ---------------------------------------------------------------------------

/// Helper lemma: successors are in graph if edge endpoints are in graph
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec successors_in_graph_aux (g: graph_state{graph_wf g}) (edges: edge_list) (v: vertex_id)
  : Lemma (requires (forall (e: edge). Seq.mem e edges ==> 
                       mem_graph_vertex g (fst e) /\ mem_graph_vertex g (snd e)))
          (ensures (forall s. Seq.mem s (successors_aux edges v) ==> 
                     mem_graph_vertex g s))
          (decreases Seq.length edges)
  = if Seq.length edges = 0 then ()
    else (
      let (src, dst) = Seq.head edges in
      successors_in_graph_aux g (Seq.tail edges) v;
      let aux (s: vertex_id) : Lemma (Seq.mem s (successors_aux edges v) ==>
                                       mem_graph_vertex g s) =
        if src = v then mem_cons_lemma s dst (successors_aux (Seq.tail edges) v)
      in
      FStar.Classical.forall_intro aux
    )
#pop-options

let successors_in_graph (g: graph_state{graph_wf g}) (v: vertex_id)
  : Lemma (ensures (forall s. Seq.mem s (successors g v) ==> mem_graph_vertex g s))
  = successors_in_graph_aux g g.edges v

/// ---------------------------------------------------------------------------
/// DFS Body - Single Step
/// ---------------------------------------------------------------------------

/// Single DFS step: pop from stack, add to visited, push successors
/// Return type includes properties needed for termination
#push-options "--z3rlimit 30"
let dfs_body (g: graph_state{graph_wf g}) 
             (stack: vertex_set{nonEmpty_set stack /\ subset_vertices stack g.vertices})
             (visited: vertex_set{subset_vertices visited g.vertices /\ 
                                   (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : GTot (sv: (vertex_set & vertex_set){
            let (stack', visited') = sv in
            // Termination: visited grows strictly
            Seq.length visited' > Seq.length visited /\
            // Preconditions for recursive call
            subset_vertices stack' g.vertices /\
            subset_vertices visited' g.vertices /\
            (forall y. Seq.mem y visited' ==> ~(Seq.mem y stack'))})
  = let x = get_last_elem stack in
    let stack_popped = get_first g stack in
    let visited' = insert_to_vertex_set g x visited in
    
    // Prove visited' > visited (for termination)
    // x is in stack, stack/visited disjoint, so x not in visited
    assert (~(Seq.mem x visited));
    insert_to_vertex_set_length_lemma g x visited;
    assert (Seq.length visited' = Seq.length visited + 1);
    
    // Prove stack_popped and visited' are disjoint
    let disjoint_lemma (y: vertex_id)
      : Lemma (Seq.mem y stack_popped ==> ~(Seq.mem y visited'))
      = if Seq.mem y stack_popped then (
          assert (y <> x);
          get_first_mem_lemma stack y;
          assert (Seq.mem y stack);
          assert (~(Seq.mem y visited));
          assert (~(Seq.mem y visited'))
        )
    in
    FStar.Classical.forall_intro disjoint_lemma;
    
    // Push unvisited successors - need successors_in_graph for subset proof
    successors_in_graph g x;
    let new_stack = push_unvisited_successors g (successors g x) visited' stack_popped in
    
    // Prove new_stack properties
    push_unvisited_successors_disjoint g (successors g x) visited' stack_popped;
    push_unvisited_successors_subset g (successors g x) visited' stack_popped;
    
    (new_stack, visited')
#pop-options

/// Lemma: dfs_body increases visited length by 1
#push-options "--z3rlimit 30"
let dfs_body_length (g: graph_state{graph_wf g})
                    (stack: vertex_set{nonEmpty_set stack /\ subset_vertices stack g.vertices})
                    (visited: vertex_set{subset_vertices visited g.vertices /\ 
                                          (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : Lemma (ensures (let (_, visited') = dfs_body g stack visited in
                    Seq.length visited' = Seq.length visited + 1))
  = let x = get_last_elem stack in
    assert (~(Seq.mem x visited));
    insert_to_vertex_set_length_lemma g x visited
#pop-options

/// Lemma: dfs_body returns visited' = insert_to_vertex_set g (get_last_elem stack) visited
#push-options "--z3rlimit 20"
let dfs_body_visited_grows (g: graph_state{graph_wf g})
                           (stack: vertex_set{nonEmpty_set stack /\ subset_vertices stack g.vertices})
                           (visited: vertex_set{subset_vertices visited g.vertices /\ 
                                                (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : Lemma (ensures (let (_, visited') = dfs_body g stack visited in
                    visited' == insert_to_vertex_set g (get_last_elem stack) visited))
  = ()
#pop-options

/// Lemma: dfs_body maintains disjointness between stack and visited
#push-options "--z3rlimit 20"
let dfs_body_disjoint (g: graph_state{graph_wf g})
                      (stack: vertex_set{nonEmpty_set stack /\ subset_vertices stack g.vertices})
                      (visited: vertex_set{subset_vertices visited g.vertices /\ 
                                           (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : Lemma (ensures (let (stack', visited') = dfs_body g stack visited in
                    forall y. Seq.mem y visited' ==> ~(Seq.mem y stack')))
  = () // Now follows from dfs_body's refined return type
#pop-options

/// Lemma: dfs_body preserves subset_vertices property for stack
#push-options "--z3rlimit 30"
let dfs_body_subset (g: graph_state{graph_wf g})
                    (stack: vertex_set{nonEmpty_set stack /\ subset_vertices stack g.vertices})
                    (visited: vertex_set{subset_vertices visited g.vertices /\ 
                                         (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : Lemma (ensures (let (stack', visited') = dfs_body g stack visited in
                    subset_vertices stack' g.vertices /\
                    subset_vertices visited' g.vertices))
  = () // Now follows from dfs_body's refined return type
#pop-options

/// Lemma: dfs_body preserves elements from get_first g stack
#push-options "--z3rlimit 50"
let dfs_body_stack_preserves (g: graph_state{graph_wf g})
                              (stack: vertex_set{nonEmpty_set stack /\ subset_vertices stack g.vertices})
                              (visited: vertex_set{subset_vertices visited g.vertices /\ 
                                                   (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : Lemma (ensures (let (stack', _) = dfs_body g stack visited in
                    forall y. Seq.mem y (get_first g stack) ==> Seq.mem y stack'))
  = let x = get_last_elem stack in
    let stack_popped = get_first g stack in
    let visited' = insert_to_vertex_set g x visited in
    push_unvisited_successors_preserves_stack g (successors g x) visited' stack_popped
#pop-options

/// Lemma: successors of popped element end up in stack' if not in visited'
#push-options "--z3rlimit 50"
let dfs_body_successor_in_stack (g: graph_state{graph_wf g})
                                 (stack: vertex_set{nonEmpty_set stack /\ subset_vertices stack g.vertices})
                                 (visited: vertex_set{subset_vertices visited g.vertices /\ 
                                                      (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
                                 (z: vertex_id)
  : Lemma (requires (let x = get_last_elem stack in
                     Seq.mem z (successors g x)))
          (ensures (let (stack', visited') = dfs_body g stack visited in
                    Seq.mem z stack' \/ Seq.mem z visited'))
  = let x = get_last_elem stack in
    let stack_popped = get_first g stack in
    let visited' = insert_to_vertex_set g x visited in
    let succs = successors g x in
    // stack' = push_unvisited_successors g succs visited' stack_popped
    // If z is in succs and not in visited', then z is pushed to stack'
    if Seq.mem z visited' then ()
    else (
      // z not in visited', and z is in succs
      // By push_unvisited_successors_includes_new: z is in stack'
      push_unvisited_successors_includes_new g succs visited' stack_popped z
    )
#pop-options

/// ---------------------------------------------------------------------------
/// DFS Main Loop with Ghost Spanning Tree
/// ---------------------------------------------------------------------------

/// DFS traversal with ghost spanning tree for provenance tracking
/// The tree is erased in extraction - this IS the main DFS
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec dfs_aux (g: graph_state{graph_wf g})
                (stack: vertex_set{subset_vertices stack g.vertices})
                (visited: vertex_set{subset_vertices visited g.vertices /\
                                      (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
                (remaining: nat{remaining = Seq.length g.vertices - Seq.length visited})
  : GTot (result: vertex_set{subset_vertices result g.vertices /\ 
                             subset_vertices visited result /\
                             subset_vertices stack result} &
          forest: erased dfs_forest{
            // Key property 1a: new vertices in result are in forest
            (forall x. Seq.mem x result /\ ~(Seq.mem x visited) ==> mem_forest x (reveal forest)) /\
            // Key property 1b: forest vertices are in result (reverse direction)
            (forall x. mem_forest x (reveal forest) ==> Seq.mem x result) /\
            // Key property 3: forest is successor-closed (wrt initial visited)
            // Successors are in forest OR were in initial visited
            forest_successor_closed_wrt g (reveal forest) visited
          })
        (decreases remaining)
  = if is_emptySet stack then (| visited, hide [] |)
    else 
      let x = get_last_elem stack in
      let sv = dfs_body g stack visited in
      let stack' = fst sv in
      let visited' = snd sv in
      
      // For termination
      assert (Seq.length visited' > Seq.length visited);
      subset_vertices_length_lemma visited' g.vertices;
      assert (Seq.length visited' <= Seq.length g.vertices);
      let remaining': nat = Seq.length g.vertices - Seq.length visited' in
      assert (remaining' < remaining);
      
      // Recursive call
      let (| result, child_forest |) = dfs_aux g stack' visited' remaining' in
      
      // Build tree node for x with its children from child_forest
      let x_node : dfs_tree = Node x (reveal child_forest) in
      let new_forest : dfs_forest = [x_node] in
      
      // Prove stack subset
      dfs_body_stack_preserves g stack visited;
      let stack_subset_lemma (y: vertex_id)
        : Lemma (Seq.mem y stack ==> Seq.mem y result)
        = if Seq.mem y stack then (
            if y = x then (
              assert (Seq.mem x visited');
              assert (Seq.mem x result)
            ) else (
              get_first_mem_lemma stack y;
              assert (Seq.mem y stack');
              assert (Seq.mem y result)
            )
          )
      in
      FStar.Classical.forall_intro stack_subset_lemma;
      
      // Prove tree properties
      assert (mem_tree x x_node);
      
      // Property 1a: new vertices in result are in new_forest
      let prop1a_lemma (y: vertex_id)
        : Lemma (Seq.mem y result /\ ~(Seq.mem y visited) ==> mem_forest y new_forest)
        = if Seq.mem y result && not (Seq.mem y visited) then (
            // y is in result and not in original visited
            // visited' = insert x visited
            insert_to_vertex_set_mem_lemma g x visited y;
            if y = x then (
              // y = x, so y is root of x_node, hence in new_forest
              assert (mem_tree x x_node);
              assert (mem_forest x new_forest)
            ) else (
              // y <> x, so y not in visited' either (since visited' = visited ∪ {x})
              assert (~(Seq.mem y visited'));
              // By IH: y in result /\ ~(y in visited') ==> mem_forest y child_forest
              assert (mem_forest y (reveal child_forest));
              // child_forest is children of x_node, so y is in x_node
              assert (mem_tree y x_node);
              assert (mem_forest y new_forest)
            )
          )
      in
      FStar.Classical.forall_intro prop1a_lemma;
      
      // Property 1b: forest vertices are in result
      let prop1b_lemma (y: vertex_id)
        : Lemma (mem_forest y new_forest ==> Seq.mem y result)
        = if mem_forest y new_forest then (
            // y is in new_forest = [x_node]
            // So y is in x_node = Node x child_forest
            // Either y = x or y is in child_forest
            assert (mem_tree y x_node);
            if y = x then (
              // x is in visited', and visited' ⊆ result
              assert (Seq.mem x visited');
              assert (Seq.mem x result)
            ) else (
              // y is in child_forest
              // By IH: mem_forest y child_forest ==> Seq.mem y result
              assert (mem_forest y (reveal child_forest));
              assert (Seq.mem y result)
            )
          )
      in
      FStar.Classical.forall_intro prop1b_lemma;
      
      // Property 3: forest is successor-closed wrt original visited
      // If y is in new_forest and z is successor of y, then z is in new_forest OR z in visited
      let prop3_lemma (y: vertex_id) (z: vertex_id)
        : Lemma (requires mem_forest y new_forest /\ mem_graph_edge g y z /\ mem_graph_vertex g z)
                (ensures mem_forest z new_forest \/ Seq.mem z visited)
        = // y is in new_forest = [x_node] = [Node x child_forest]
          // So either y = x or y is in child_forest
          assert (mem_tree y x_node);
          if y = x then (
            // z is successor of x
            // By edge_mem_successors: z is in successors g x
            edge_mem_successors g x z;
            assert (Seq.mem z (successors g x));
            
            // z was either in visited' already, or pushed to stack'
            // (by push_unvisited_successors behavior)
            if Seq.mem z visited then (
              // Done: z is in visited (satisfies disjunct)
              ()
            ) else (
              // z not in visited
              // visited' = insert x visited, so if z not in visited and z <> x, then z not in visited'
              insert_to_vertex_set_mem_lemma g x visited z;
              if z = x then (
                // z = x (self-loop edge x → x)
                // x is the root of x_node, so x is in new_forest
                assert (mem_tree x x_node);
                assert (mem_forest x new_forest)
              ) else (
                // z <> x and z not in visited, so z not in visited'
                assert (~(Seq.mem z visited'));
                // z is a successor of x, so z was pushed to stack'
                // Use the new helper lemma
                edge_mem_successors g x z;
                dfs_body_successor_in_stack g stack visited z;
                // By dfs_body_successor_in_stack: z in stack' \/ z in visited'
                // We know z not in visited', so z in stack'
                assert (Seq.mem z stack');
                // By IH postcondition: stack' ⊆ result
                assert (Seq.mem z result);
                // By IH property 1a: z in result /\ ~(z in visited') ==> z in child_forest
                assert (mem_forest z (reveal child_forest));
                assert (mem_forest z new_forest)
              )
            )
          ) else (
            // y <> x, so y is in child_forest
            assert (mem_forest y (reveal child_forest));
            // By IH: forest_successor_closed_wrt g child_forest visited'
            // So: z in child_forest OR z in visited'
            assert (forest_successor_closed_wrt g (reveal child_forest) visited');
            // Z3 should derive: mem_forest z child_forest \/ Seq.mem z visited'
            if mem_forest z (reveal child_forest) then (
              assert (mem_forest z new_forest)
            ) else (
              // z is in visited'
              assert (Seq.mem z visited');
              insert_to_vertex_set_mem_lemma g x visited z;
              // visited' = insert x visited
              // So z = x or z in visited
              if z = x then (
                assert (mem_tree x x_node);
                assert (mem_forest x new_forest)
              ) else (
                assert (Seq.mem z visited)
              )
            )
          )
      in
      FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 prop3_lemma);
      
      (| result, hide new_forest |)
#pop-options

/// Main DFS entry point - returns result and ghost tree
let dfs_full (g: graph_state{graph_wf g})
             (stack: vertex_set{subset_vertices stack g.vertices})
             (visited: vertex_set{subset_vertices visited g.vertices /\
                                   (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : GTot (result: vertex_set{subset_vertices result g.vertices /\ 
                             subset_vertices visited result /\
                             subset_vertices stack result} &
          forest: erased dfs_forest{
            (forall x. Seq.mem x result /\ ~(Seq.mem x visited) ==> mem_forest x (reveal forest)) /\
            (forall x. mem_forest x (reveal forest) ==> Seq.mem x result) /\
            forest_successor_closed_wrt g (reveal forest) visited
          })
  = dfs_aux g stack visited (Seq.length g.vertices - Seq.length visited)

/// Convenience: just get the visited set (tree is erased anyway)
let dfs (g: graph_state{graph_wf g})
        (stack: vertex_set{subset_vertices stack g.vertices})
        (visited: vertex_set{subset_vertices visited g.vertices /\
                              (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : GTot (result: vertex_set{subset_vertices result g.vertices /\ 
                             subset_vertices visited result /\
                             subset_vertices stack result})
  = dfst (dfs_full g stack visited)

/// ---------------------------------------------------------------------------
/// Soundness Lemma (Forward Direction)
/// ---------------------------------------------------------------------------

/// DFS invariant: all vertices in stack and visited are reachable from roots
let dfs_inv (g: graph_state{graph_wf g}) (roots: vertex_set{subset_vertices roots g.vertices})
            (stack: vertex_set) (visited: vertex_set) : prop =
  // All stack elements are reachable from roots
  (forall x. Seq.mem x stack ==> 
    (exists (r: vertex_id{mem_graph_vertex g r}). 
       Seq.mem r roots /\ reachable g r x)) /\
  // All visited elements are reachable from roots
  (forall x. Seq.mem x visited ==> 
    (exists (r: vertex_id{mem_graph_vertex g r}). 
       Seq.mem r roots /\ reachable g r x))

/// Helper lemma: if x is reachable from roots and y is a successor of x,
/// then y is also reachable from roots
#push-options "--z3rlimit 20"
let successor_reachable (g: graph_state{graph_wf g}) 
                        (roots: vertex_set{subset_vertices roots g.vertices})
                        (x: vertex_id{mem_graph_vertex g x})
                        (y: vertex_id{mem_graph_vertex g y})
  : Lemma (requires (exists (r: vertex_id{mem_graph_vertex g r}). 
                       Seq.mem r roots /\ reachable g r x) /\
                    mem_graph_edge g x y)
          (ensures (exists (r: vertex_id{mem_graph_vertex g r}). 
                      Seq.mem r roots /\ reachable g r y))
  = // Unpack the reachability from roots to x
    let aux (r: vertex_id{mem_graph_vertex g r}) 
      : Lemma (requires Seq.mem r roots /\ reachable g r x)
              (ensures (exists (r': vertex_id{mem_graph_vertex g r'}). 
                         Seq.mem r' roots /\ reachable g r' y))
      = // x is reachable from r, and y is a successor of x (edge x -> y)
        // Therefore y is reachable from r via edge
        edge_reach g x y;
        reach_trans g r x y;
        // Now we have reachable g r y
        assert (reachable g r y);
        assert (Seq.mem r roots);
        ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Helper lemma: push_unvisited_successors preserves reachability invariant
/// This key lemma ensures that all elements pushed to the stack are reachable from roots
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec push_unvisited_successors_preserves_inv 
  (g: graph_state{graph_wf g}) 
  (x: vertex_id{mem_graph_vertex g x})
  (succs: vertex_list)
  (roots: vertex_set{subset_vertices roots g.vertices})
  (visited: vertex_set) 
  (stack: vertex_set)
  : Lemma (requires 
             // All successors are successors of x
             (forall s. Seq.mem s succs ==> Seq.mem s (successors g x)) /\
             // x is reachable from roots
             (exists (r: vertex_id{mem_graph_vertex g r}). 
                Seq.mem r roots /\ reachable g r x) /\
             // Stack elements are reachable from roots
             (forall s. Seq.mem s stack ==> 
               (exists (r: vertex_id{mem_graph_vertex g r}). 
                  Seq.mem r roots /\ reachable g r s)) /\
             // All successors are in graph
             (forall s. Seq.mem s succs ==> mem_graph_vertex g s))
          (ensures (let new_stack = push_unvisited_successors g succs visited stack in
                    forall s. Seq.mem s new_stack ==> 
                      (exists (r: vertex_id{mem_graph_vertex g r}). 
                         Seq.mem r roots /\ reachable g r s)))
          (decreases Seq.length succs)
  = if Seq.length succs = 0 then ()
    else (
      let hd = Seq.head succs in
      let tl = Seq.tail succs in
      
      // Recursive call on tail
      push_unvisited_successors_preserves_inv g x tl roots visited stack;
      let rest = push_unvisited_successors g tl visited stack in
      
      // rest satisfies the invariant by IH
      assert (forall s. Seq.mem s rest ==> 
                (exists (r: vertex_id{mem_graph_vertex g r}). 
                   Seq.mem r roots /\ reachable g r s));
      
      if Seq.mem hd visited then ()
      else if Seq.mem hd rest then ()
      else (
        // hd is added to the result
        // hd is a successor of x, so there's an edge x -> hd
        // x is reachable from roots, so hd is also reachable
        assert (Seq.mem hd succs);
        assert (Seq.mem hd (successors g x));
        assert (mem_graph_vertex g hd); // from precondition: all successors are in graph
        successors_mem_edge g x hd;
        assert (mem_graph_edge g x hd);
        
        // Build reachability proof for hd:
        // x is reachable from some root r in roots
        // hd is reachable from x (via edge)
        // Therefore hd is reachable from r (via transitivity)
        edge_reach g x hd;
        assert (reachable g x hd);
        
        let result = Seq.cons hd rest in
        
        // Prove the postcondition for each element in result
        // Note: result is subset of g.vertices, so all elements are in graph
        let aux_lemma (s: vertex_id{mem_graph_vertex g s})
          : Lemma (requires Seq.mem s result)
                  (ensures exists (r: vertex_id{mem_graph_vertex g r}). 
                             Seq.mem r roots /\ reachable g r s)
          = mem_cons_lemma s hd rest;
            if s = hd then (
              // s = hd: need to show hd is reachable from some root
              // We have: reachable g x hd and x is reachable from roots
              // Use FStar.Classical to extract witness
              let extract_and_chain () 
                : Lemma (exists (r: vertex_id{mem_graph_vertex g r}). 
                            Seq.mem r roots /\ reachable g r hd)
                = FStar.Classical.exists_elim
                    (exists (r: vertex_id{mem_graph_vertex g r}). 
                       Seq.mem r roots /\ reachable g r hd)
                    #_
                    #(fun (r: vertex_id{mem_graph_vertex g r}) -> 
                        Seq.mem r roots /\ reachable g r x)
                    ()
                    (fun r -> 
                      // r reaches x, x reaches hd, so r reaches hd
                      reach_trans g r x hd;
                      assert (reachable g r hd))
              in
              extract_and_chain ()
            ) else (
              // s is in rest, use IH
              assert (Seq.mem s rest)
            )
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_lemma)
      )
    )
#pop-options

/// Strengthened DFS with invariant
#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let rec dfs_with_inv (g: graph_state{graph_wf g})
                     (roots: vertex_set{subset_vertices roots g.vertices})
                     (stack: vertex_set{subset_vertices stack g.vertices})
                     (visited: vertex_set{subset_vertices visited g.vertices /\
                                           (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
  : Lemma (requires dfs_inv g roots stack visited)
          (ensures (let result = dfs g stack visited in
                    forall x. Seq.mem x result ==> 
                      (exists (r: vertex_id{mem_graph_vertex g r}). 
                         Seq.mem r roots /\ reachable g r x)))
          (decreases %[cardinal g.vertices - cardinal visited; cardinal stack])
  = if is_emptySet stack then (
      // Base case: stack is empty, dfs returns visited
      // Invariant tells us all visited elements are reachable
      assert (dfs g stack visited == visited)
    )
    else (
      // Inductive case
      let x = get_last_elem stack in
      
      // x is in stack, so x is reachable from roots by invariant
      assert (Seq.mem x stack);
      assert (exists (r: vertex_id{mem_graph_vertex g r}). 
                Seq.mem r roots /\ reachable g r x);
      
      let (stack', visited') = dfs_body g stack visited in
      
      // Prove invariant holds for recursive call
      // 1. visited' elements are reachable
      //    - Old visited elements are reachable (by IH)
      //    - x is newly added and is reachable (from stack invariant)
      let visited_inv () : Lemma (forall y. Seq.mem y visited' ==>
                                    (exists (r: vertex_id{mem_graph_vertex g r}). 
                                       Seq.mem r roots /\ reachable g r y)) =
        // visited' = insert_to_vertex_set g x visited
        let aux (y: vertex_id) : Lemma (Seq.mem y visited' ==>
                                         (exists (r: vertex_id{mem_graph_vertex g r}). 
                                            Seq.mem r roots /\ reachable g r y)) =
          insert_to_vertex_set_mem_lemma g x visited y
        in
        FStar.Classical.forall_intro aux
      in
      visited_inv ();
      
      // 2. stack' elements are reachable
      //    - Elements from old stack (minus x) are reachable
      //    - Newly pushed successors of x are reachable (via x)
      successors_in_graph g x; // All successors are in graph
      
      let stack_inv () : Lemma (forall y. Seq.mem y stack' ==>
                                  (exists (r: vertex_id{mem_graph_vertex g r}). 
                                     Seq.mem r roots /\ reachable g r y)) =
        // stack' = push_unvisited_successors g (successors g x) visited' (get_first g stack)
        // First, show get_first g stack elements are reachable
        let old_stack_lemma () : Lemma (forall y. Seq.mem y (get_first g stack) ==>
                                          (exists (r: vertex_id{mem_graph_vertex g r}). 
                                             Seq.mem r roots /\ reachable g r y)) =
          let aux (y: vertex_id) : Lemma (Seq.mem y (get_first g stack) ==>
                                           (exists (r: vertex_id{mem_graph_vertex g r}). 
                                              Seq.mem r roots /\ reachable g r y)) =
            get_first_mem_lemma stack y
          in
          FStar.Classical.forall_intro aux
        in
        old_stack_lemma ();
        
        // Now apply push_unvisited_successors_preserves_inv
        let succs = successors g x in
        let base_stack = get_first g stack in
        push_unvisited_successors_preserves_inv g x succs roots visited' base_stack
      in
      stack_inv ();
      
      // Now we have dfs_inv g roots stack' visited'
      assert (dfs_inv g roots stack' visited');
      
      // Establish termination metric decrease
      assert (~(Seq.mem x visited));
      insert_to_vertex_set_length_lemma g x visited;
      assert (cardinal visited' = cardinal visited + 1);
      
      // Disjointness comes from dfs_body's refined return type
      // (forall y. Seq.mem y visited' ==> ~(Seq.mem y stack'))
      // is already in the postcondition of dfs_body
      
      // Apply inductive hypothesis
      dfs_with_inv g roots stack' visited';
      
      // Result preserves reachability
      let result = dfs g stack' visited' in
      assert (forall y. Seq.mem y result ==>
                (exists (r: vertex_id{mem_graph_vertex g r}). 
                   Seq.mem r roots /\ reachable g r y))
    )
#pop-options

/// Initial invariant: roots in stack, visited empty
#push-options "--z3rlimit 20"
let dfs_initial_inv (g: graph_state{graph_wf g}) (roots: vertex_set{subset_vertices roots g.vertices})
  : Lemma (ensures dfs_inv g roots roots empty_set)
  = // All elements in roots are reachable from themselves
    let stack_inv (x: vertex_id) : Lemma (Seq.mem x roots ==>
                                           (exists (r: vertex_id{mem_graph_vertex g r}). 
                                              Seq.mem r roots /\ reachable g r x)) =
      if Seq.mem x roots then (
        reach_refl g x;
        assert (reachable g x x);
        assert (mem_graph_vertex g x);
        ()
      )
    in
    FStar.Classical.forall_intro stack_inv;
    
    // visited is empty, so vacuously true
    let visited_inv (x: vertex_id) : Lemma (Seq.mem x empty_set ==>
                                             (exists (r: vertex_id{mem_graph_vertex g r}). 
                                                Seq.mem r roots /\ reachable g r x)) =
      assert (Seq.length empty_set = 0)
    in
    FStar.Classical.forall_intro visited_inv
#pop-options

/// Soundness: everything DFS visits is reachable from roots
val dfs_lemma_forward : (g: graph_state{graph_wf g}) -> 
                        (roots: vertex_set{subset_vertices roots g.vertices}) ->
                        (visited: vertex_set) ->
  Lemma (requires visited = dfs g roots empty_set)
        (ensures forall x. Seq.mem x visited ==> 
                  (exists (r: vertex_id{mem_graph_vertex g r}). 
                     Seq.mem r roots /\ reachable g r x))

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let dfs_lemma_forward g roots visited =
  // Establish initial invariant
  dfs_initial_inv g roots;
  // Apply strengthened DFS lemma
  dfs_with_inv g roots roots empty_set
#pop-options

/// ---------------------------------------------------------------------------
/// Tree-based Successor-Closedness Proof
/// ---------------------------------------------------------------------------

/// The key insight: when DFS starts from empty_set, every result vertex is in the tree.
/// The tree has the property that when x is added (with children as unvisited successors),
/// all successors of x either become children in the tree OR were already in visited (hence in tree).
/// Therefore: if x is in tree and y is a successor of x, then y is in tree.

/// Successor-closedness for results from empty_set
/// When visited starts as empty_set, the result is successor-closed
let dfs_successor_closed_from_empty (g: graph_state{graph_wf g})
                                     (stack: vertex_set{subset_vertices stack g.vertices})
                                     (x: vertex_id{mem_graph_vertex g x})
                                     (y: vertex_id{mem_graph_vertex g y})
  : Lemma (requires Seq.mem x (dfs g stack empty_set) /\ mem_graph_edge g x y)
          (ensures Seq.mem y (dfs g stack empty_set))
  = // Use dfs_full to get the ghost tree
    let (| result, forest |) = dfs_full g stack empty_set in
    // result == dfs g stack empty_set by definition
    
    // x is in result and empty_set is empty, so x is in forest
    // (by property 1a of dfs_full)
    assert (~(Seq.mem x empty_set));
    assert (mem_forest x (reveal forest));
    
    // forest is successor-closed wrt empty_set (property 3 of dfs_full)
    // When visited = empty_set, this means successors are in forest (no "or was in visited" escape)
    assert (forest_successor_closed_wrt g (reveal forest) empty_set);
    forest_successor_closed_wrt_empty g (reveal forest);
    assert (forest_successor_closed g (reveal forest));
    // So since x is in forest and edge x->y exists, y is in forest
    assert (mem_forest y (reveal forest));
    
    // By property 1b: forest vertices are in result
    assert (Seq.mem y result)

/// Helper: prove that elements initially in stack are eventually visited
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec dfs_stack_visited (g: graph_state{graph_wf g})
                          (stack: vertex_set{subset_vertices stack g.vertices})
                          (visited: vertex_set{subset_vertices visited g.vertices /\
                                                (forall x. Seq.mem x visited ==> ~(Seq.mem x stack))})
                          (x: vertex_id)
  : Lemma (requires Seq.mem x stack)
          (ensures Seq.mem x (dfs g stack visited))
          (decreases %[cardinal g.vertices - cardinal visited; cardinal stack])
  = if is_emptySet stack then (
      // Contradiction: x is in stack but stack is empty
      assert (Seq.length stack = 0);
      ()
    ) else (
      let y = get_last_elem stack in
      let (stack', visited') = dfs_body g stack visited in
      
      // Establish termination metric decrease
      assert (~(Seq.mem y visited));
      insert_to_vertex_set_length_lemma g y visited;
      
      // Get disjointness and subset properties for recursive call
      dfs_body_disjoint g stack visited;
      dfs_body_subset g stack visited;
      assert (forall z. Seq.mem z visited' ==> ~(Seq.mem z stack'));
      
      if x = y then (
        // x is the element being popped, so it goes into visited'
        insert_to_vertex_set_mem_lemma g y visited y;
        assert (Seq.mem y visited');
        // visited' ⊆ dfs g stack' visited' (postcondition of dfs)
        assert (Seq.mem y (dfs g stack' visited'))
      ) else (
        // x is still in stack' (via get_first preservation and push)
        // Since x in stack and x <> y, x is in get_first g stack
        // dfs_body preserves elements from get_first in stack'
        dfs_body_stack_preserves g stack visited;
        assert (Seq.mem x (get_first g stack) ==> Seq.mem x stack');
        // By IH on recursive call
        dfs_stack_visited g stack' visited' x;
        ()
      )
    )
#pop-options

/// Key insight: when an element x is processed (popped from stack, added to visited),
/// all its successors are pushed to stack (if not already visited).
/// Combined with dfs_stack_visited, this means all successors end up in the final result.
/// Main inductive proof: if r reaches x, then x is visited
/// Proof by induction on the reach witness
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec dfs_reachable_visited (g: graph_state{graph_wf g})
                               (roots: vertex_set{subset_vertices roots g.vertices})
                               (r: vertex_id{mem_graph_vertex g r})
                               (x: vertex_id{mem_graph_vertex g x})
                               (path: reach g r x)
  : Lemma (requires Seq.mem r roots)
          (ensures Seq.mem x (dfs g roots empty_set))
          (decreases path)
  = match path with
    | ReachRefl _ -> 
      // r reaches itself, r is in roots, so r is in initial stack
      // Therefore r is visited
      dfs_stack_visited g roots empty_set r
      
    | ReachTrans r y z path_ry ->
      // r reaches y via path_ry, and there's an edge y -> z
      // By IH, y is visited
      dfs_reachable_visited g roots r y path_ry;
      // Now we know y is in dfs g roots empty_set
      // Since there's an edge y -> z, z will be visited
      // Use the specialized lemma for empty_set
      dfs_successor_closed_from_empty g roots y z;
      ()
#pop-options

/// Completeness: everything reachable from roots is visited by DFS
val dfs_lemma_backward : (g: graph_state{graph_wf g}) ->
                         (roots: vertex_set{subset_vertices roots g.vertices}) ->
                         (visited: vertex_set) ->
  Lemma (requires visited = dfs g roots empty_set)
        (ensures forall (r: vertex_id{mem_graph_vertex g r}) 
                        (x: vertex_id{mem_graph_vertex g x}).
                   (Seq.mem r roots /\ reachable g r x) ==> Seq.mem x visited)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let dfs_lemma_backward g roots visited =
  // Use the inductive lemma
  let aux (r: vertex_id{mem_graph_vertex g r}) 
          (x: vertex_id{mem_graph_vertex g x})
    : Lemma (requires Seq.mem r roots /\ reachable g r x)
            (ensures Seq.mem x visited)
    = // Unpack reachable: exists path. ...
      let aux2 (path: reach g r x) 
        : Lemma (ensures Seq.mem x visited)
        = dfs_reachable_visited g roots r x path
      in
      FStar.Classical.forall_intro aux2
  in
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 aux)
#pop-options

/// ---- Reachable set API (convenience wrappers over dfs/dfs_full) ----

/// Compute reachable set with a ghost forest witness
let reachable_set_with_forest (g: graph_state{graph_wf g})
                               (roots: vertex_set{subset_vertices roots g.vertices})
  : GTot (result: vertex_set{subset_vertices result g.vertices} &
          forest: erased dfs_forest{
            (forall x. Seq.mem x result <==> mem_forest x (reveal forest)) /\
            forest_successor_closed g (reveal forest)
          })
  = let (| visited, forest |) = dfs_full g roots empty_set in
    forest_successor_closed_wrt_empty g (reveal forest);
    (| visited, forest |)

/// Just get the reachable set (forest erased)
let reachable_set (g: graph_state{graph_wf g})
                   (roots: vertex_set{subset_vertices roots g.vertices})
  : GTot (result: vertex_set{subset_vertices result g.vertices})
  = dfs g roots empty_set

/// reachable_set membership ⟺ reachable from some root
val reachable_set_correct : (g: graph_state{graph_wf g}) ->
                             (roots: vertex_set{subset_vertices roots g.vertices}) ->
  Lemma (ensures (let result = reachable_set g roots in
                  (forall x. Seq.mem x result ==> 
                    (exists (r: vertex_id{mem_graph_vertex g r}). 
                       Seq.mem r roots /\ reachable g r x)) /\
                  (forall (r: vertex_id{mem_graph_vertex g r}) 
                          (x: vertex_id{mem_graph_vertex g x}).
                     (Seq.mem r roots /\ reachable g r x) ==> Seq.mem x result)))

let reachable_set_correct g roots =
  let result = reachable_set g roots in
  dfs_lemma_forward g roots result;
  dfs_lemma_backward g roots result

/// Forest-based reachability check (constructive)
let is_reachable_via_forest (g: graph_state{graph_wf g})
                             (roots: vertex_set{subset_vertices roots g.vertices})
                             (x: vertex_id)
  : GTot bool
  = Seq.mem x (reachable_set g roots)

/// Successor closure: if x is reachable and has edge to y, then y is reachable
val reachable_successor_closed : (g: graph_state{graph_wf g}) ->
                                  (roots: vertex_set{subset_vertices roots g.vertices}) ->
                                  (x: vertex_id{mem_graph_vertex g x}) ->
                                  (y: vertex_id{mem_graph_vertex g y}) ->
  Lemma (requires Seq.mem x (reachable_set g roots) /\ mem_graph_edge g x y)
        (ensures Seq.mem y (reachable_set g roots))

let reachable_successor_closed g roots x y =
  let (| result, forest |) = reachable_set_with_forest g roots in
  assert (mem_forest x (reveal forest));
  assert (forest_successor_closed g (reveal forest));
  assert (mem_forest y (reveal forest));
  assert (Seq.mem y result)
