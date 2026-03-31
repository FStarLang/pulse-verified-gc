/// ---------------------------------------------------------------------------
/// GC.Spec.Graph - Graph theory for reachability proofs
/// ---------------------------------------------------------------------------
///
/// This module provides the abstract graph model for GC correctness:
/// - Vertex and edge types
/// - Vertex set (no duplicates)
/// - Reachability predicate (inductive)
/// - Successor functions
///
/// Ported from: Proofs/Spec.Graph3.fsti

module GC.Spec.Graph

open FStar.Seq
open FStar.Seq.Base
open FStar.Classical
open FStar.List.Tot

module U64 = FStar.UInt64

open GC.Spec.Base

/// ---------------------------------------------------------------------------
/// Basic Types
/// ---------------------------------------------------------------------------

/// Vertex identifier (heap address - refined U64.t)
type vertex_id = hp_addr

/// Edge: directed from first to second vertex
type edge = vertex_id & vertex_id

/// List of vertices
type vertex_list = seq vertex_id

/// List of edges
type edge_list = seq edge

/// ---------------------------------------------------------------------------
/// Vertex Set (No Duplicates)
/// ---------------------------------------------------------------------------

/// Count occurrences of element in sequence
let rec count (#a: eqtype) (l: seq a) (x: a) : Tot nat (decreases Seq.length l) =
  if Seq.length l = 0 then 0
  else if Seq.index l 0 = x then 1 + count (Seq.tail l) x
  else count (Seq.tail l) x

/// Element not in list means count is 0
let rec count_not_mem (#a: eqtype) (l: seq a) (x: a)
  : Lemma (requires not (Seq.mem x l))
          (ensures count l x == 0)
          (decreases Seq.length l)
  = if Seq.length l = 0 then ()
    else count_not_mem (Seq.tail l) x

/// Check if sequence has no duplicates
let rec is_vertex_set (l: vertex_list) : Tot bool (decreases Seq.length l) =
  if Seq.length l = 0 then true
  else not (Seq.mem (Seq.head l) (Seq.tail l)) && is_vertex_set (Seq.tail l)

/// Vertex set type
type vertex_set = l:vertex_list{is_vertex_set l}

/// ---------------------------------------------------------------------------
/// Vertex Set Lemmas
/// ---------------------------------------------------------------------------

/// Empty sequence is a vertex set
let is_vertex_set_empty () : Lemma (is_vertex_set Seq.empty) = ()

/// Singleton is a vertex set
let is_vertex_set_singleton (x: vertex_id) 
  : Lemma (is_vertex_set (Seq.create 1 x)) = ()

/// Tail of vertex set is vertex set
val is_vertex_set_tail : (l: vertex_list) ->
  Lemma (requires is_vertex_set l /\ Seq.length l > 0)
        (ensures is_vertex_set (Seq.tail l))

let is_vertex_set_tail l = ()

/// Cons preserves vertex set if element not in tail
val is_vertex_set_cons : (hd: vertex_id) -> (tl: vertex_list{is_vertex_set tl}) ->
  Lemma (requires not (Seq.mem hd tl))
        (ensures is_vertex_set (Seq.cons hd tl))

let is_vertex_set_cons hd tl = 
  assert (Seq.head (Seq.cons hd tl) == hd);
  assert (Seq.equal (Seq.tail (Seq.cons hd tl)) tl)

/// In a vertex set, each element appears exactly once
val is_vertex_set_count : (l: vertex_list) -> (x: vertex_id) ->
  Lemma (requires is_vertex_set l /\ Seq.mem x l)
        (ensures count l x == 1)
        (decreases Seq.length l)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec is_vertex_set_count l x =
  if Seq.length l = 0 then ()
  else if Seq.head l = x then
    count_not_mem (Seq.tail l) x
  else
    is_vertex_set_count (Seq.tail l) x
#pop-options

/// ---------------------------------------------------------------------------
/// Graph State
/// ---------------------------------------------------------------------------

/// Graph with vertices and edges
noeq type graph_state = {
  vertices: vertex_set;
  edges: edge_list;
}

/// Well-formedness: all edge endpoints are in vertices
let graph_wf (g: graph_state) : prop =
  forall (e: edge). Seq.mem e g.edges ==> 
    (Seq.mem (fst e) g.vertices /\ Seq.mem (snd e) g.vertices)

/// Well-formed graph type
type wf_graph = g:graph_state{graph_wf g}

/// Check if vertex is in graph
let mem_graph_vertex (g: graph_state) (v: vertex_id) : bool =
  Seq.mem v g.vertices

/// Check if edge is in graph
let mem_graph_edge (g: graph_state) (src: vertex_id) (dst: vertex_id) : bool =
  Seq.mem (src, dst) g.edges

/// ---------------------------------------------------------------------------
/// Successors
/// ---------------------------------------------------------------------------

/// Get all successors of a vertex (vertices reachable in one step)
let rec successors_aux (edges: edge_list) (v: vertex_id) 
  : Tot vertex_list (decreases Seq.length edges) =
  if Seq.length edges = 0 then Seq.empty
  else 
    let (src, dst) = Seq.head edges in
    let rest = successors_aux (Seq.tail edges) v in
    if src = v then Seq.cons dst rest
    else rest

let successors (g: graph_state) (v: vertex_id) : vertex_list =
  successors_aux g.edges v

/// Helper lemma: membership in cons
let mem_cons_lemma (#a: eqtype) (x: a) (hd: a) (tl: seq a)
  : Lemma (Seq.mem x (Seq.cons hd tl) <==> (x = hd \/ Seq.mem x tl))
  = FStar.Seq.Properties.lemma_mem_append (Seq.create 1 hd) tl

/// Successor implies edge exists (auxiliary on edge list)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec successors_mem_edge_aux (edges: edge_list) (v: vertex_id) (s: vertex_id)
  : Lemma (requires Seq.mem s (successors_aux edges v))
          (ensures Seq.mem (v, s) edges)
          (decreases Seq.length edges)
  =
  if Seq.length edges = 0 then ()
  else
    let (src, dst) = Seq.head edges in
    let rest = successors_aux (Seq.tail edges) v in
    if src = v then begin
      mem_cons_lemma s dst rest;
      if dst = s then ()
      else successors_mem_edge_aux (Seq.tail edges) v s
    end else
      successors_mem_edge_aux (Seq.tail edges) v s
#pop-options

/// Successor implies edge exists
val successors_mem_edge : (g: graph_state) -> (v: vertex_id) -> (s: vertex_id) ->
  Lemma (requires Seq.mem s (successors g v))
        (ensures mem_graph_edge g v s)

let successors_mem_edge g v s = 
  successors_mem_edge_aux g.edges v s

/// Edge implies successor (reverse direction)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec edge_mem_successors_aux (edges: edge_list) (v: vertex_id) (s: vertex_id)
  : Lemma (requires Seq.mem (v, s) edges)
          (ensures Seq.mem s (successors_aux edges v))
          (decreases Seq.length edges)
  =
  if Seq.length edges = 0 then ()
  else
    let (src, dst) = Seq.head edges in
    let rest = successors_aux (Seq.tail edges) v in
    if src = v && dst = s then (
      // The edge is the head, so s = dst is in the result
      mem_cons_lemma s dst rest
    ) else if Seq.mem (v, s) (Seq.tail edges) then (
      // The edge is in the tail
      edge_mem_successors_aux (Seq.tail edges) v s;
      if src = v then mem_cons_lemma s dst rest
    ) else (
      // Edge must be the head but with src = v and dst = s
      assert (src = v /\ dst = s);  // follows from precondition
      mem_cons_lemma s dst rest
    )
#pop-options

/// Edge implies successor
val edge_mem_successors : (g: graph_state) -> (v: vertex_id) -> (s: vertex_id) ->
  Lemma (requires mem_graph_edge g v s)
        (ensures Seq.mem s (successors g v))

let edge_mem_successors g v s = 
  edge_mem_successors_aux g.edges v s

/// ---------------------------------------------------------------------------
/// Reachability (Inductive)
/// ---------------------------------------------------------------------------

/// Reachability predicate: x can reach y via graph edges
/// Vertices must be in the graph for the type to be inhabited
noeq type reach (g: graph_state) 
  : (x:vertex_id{mem_graph_vertex g x}) -> 
    (y:vertex_id{mem_graph_vertex g y}) -> Type =
  | ReachRefl : (x:vertex_id{mem_graph_vertex g x}) -> reach g x x
  | ReachTrans : (x:vertex_id{mem_graph_vertex g x}) ->
                 (y:vertex_id{mem_graph_vertex g y}) ->
                 (z:vertex_id{mem_graph_vertex g z /\ mem_graph_edge g y z}) ->
                 reach g x y -> 
                 reach g x z

/// Decidable reachability witness - always true given a valid reach term
let reachfunc (g: graph_state) 
              (x: vertex_id{mem_graph_vertex g x})
              (y: vertex_id{mem_graph_vertex g y})
              (r: reach g x y) : bool = true

/// Witness that reachability holds (for vertices in the graph)
let reachable (g: graph_state) 
              (x: vertex_id{mem_graph_vertex g x}) 
              (y: vertex_id{mem_graph_vertex g y}) : prop =
  exists (r: reach g x y). True

/// ---------------------------------------------------------------------------
/// Reachability Lemmas
/// ---------------------------------------------------------------------------

/// Reflexivity: every vertex reaches itself
val reach_refl : (g: graph_state) -> (x: vertex_id{mem_graph_vertex g x}) ->
  Lemma (reachable g x x)

let reach_refl g x = 
  let r: reach g x x = ReachRefl #g x in
  FStar.Classical.exists_intro (fun (_: reach g x x) -> True) r

/// Transitivity helper: build witness
let rec reach_trans_witness (#g: graph_state) 
                             (#x: vertex_id{mem_graph_vertex g x}) 
                             (#y: vertex_id{mem_graph_vertex g y}) 
                             (#z: vertex_id{mem_graph_vertex g z}) 
                             (rxy: reach g x y) (ryz: reach g y z)
  : Tot (reach g x z) (decreases ryz)
  =
  match ryz with
  | ReachRefl _ -> rxy
  | ReachTrans _ w z' rwz' -> 
    let rxw: reach g x w = reach_trans_witness rxy rwz' in
    ReachTrans x w z rxw

/// Transitivity: if x reaches y and y reaches z, then x reaches z
val reach_trans : (g: graph_state) -> 
                  (x: vertex_id{mem_graph_vertex g x}) -> 
                  (y: vertex_id{mem_graph_vertex g y}) -> 
                  (z: vertex_id{mem_graph_vertex g z}) ->
  Lemma (requires reachable g x y /\ reachable g y z)
        (ensures reachable g x z)

let reach_trans g x y z = 
  let aux (rxy: reach g x y) : Lemma (reachable g x z) = 
    let aux2 (ryz: reach g y z) : Lemma (reachable g x z) = 
      let rxz = reach_trans_witness rxy ryz in
      FStar.Classical.exists_intro (fun (_: reach g x z) -> True) rxz
    in
    FStar.Classical.forall_intro aux2
  in
  FStar.Classical.forall_intro aux

/// Edge implies reachability
val edge_reach : (g: graph_state) -> 
                 (x: vertex_id{mem_graph_vertex g x}) -> 
                 (y: vertex_id{mem_graph_vertex g y}) ->
  Lemma (requires mem_graph_edge g x y)
        (ensures reachable g x y)

let edge_reach g x y =
  let r1: reach g x x = ReachRefl #g x in
  let r2: reach g x y = ReachTrans #g x x y r1 in
  FStar.Classical.exists_intro (fun (_: reach g x y) -> True) r2

/// ---------------------------------------------------------------------------
/// Subgraph Reachability Transfer
/// ---------------------------------------------------------------------------

/// Transfer a reach witness from g1 to g2 when vertices and edges are preserved
let rec reach_subgraph_witness
  (g1: graph_state) 
  (g2: graph_state)
  (x: vertex_id{mem_graph_vertex g1 x /\ mem_graph_vertex g2 x})
  (y: vertex_id{mem_graph_vertex g1 y /\ mem_graph_vertex g2 y})
  (r: reach g1 x y)
  : Pure (reach g2 x y)
    (requires forall s d. mem_graph_edge g1 s d ==> mem_graph_vertex g2 s /\ 
                                                     mem_graph_vertex g2 d /\ 
                                                     mem_graph_edge g2 s d)
    (ensures fun _ -> True)
    (decreases r)
  = match r with
  | ReachRefl _ -> ReachRefl #g2 x
  | ReachTrans _ z _ r_xz ->
    // z is in g1, and edge z->y is in g1
    // By hypothesis, edge z->y is in g2, so z,y in g2 as vertices
    let r_xz' : reach g2 x z = reach_subgraph_witness g1 g2 x z r_xz in
    ReachTrans #g2 x z y r_xz'

/// If vertices and edges are preserved, reachability transfers
val reach_subgraph : (g1: graph_state) -> (g2: graph_state) ->
  (x: vertex_id{mem_graph_vertex g1 x /\ mem_graph_vertex g2 x}) ->
  (y: vertex_id{mem_graph_vertex g1 y /\ mem_graph_vertex g2 y}) ->
  Lemma (requires 
           reachable g1 x y /\
           (forall s d. mem_graph_edge g1 s d ==> mem_graph_vertex g2 s /\ 
                                                   mem_graph_vertex g2 d /\ 
                                                   mem_graph_edge g2 s d))
        (ensures reachable g2 x y)

let reach_subgraph g1 g2 x y =
  FStar.Classical.exists_elim
    (reachable g2 x y)
    #(reach g1 x y)
    #(fun _ -> True)
    ()
    (fun r ->
      let r' = reach_subgraph_witness g1 g2 x y r in
      FStar.Classical.exists_intro (fun (_: reach g2 x y) -> True) r')

/// Extract vertices along the path (not including start, not including end)
let rec vertices_in_path (g: graph_state) 
                         (x: vertex_id{mem_graph_vertex g x})
                         (y: vertex_id{mem_graph_vertex g y})
                         (r: reach g x y)
  : Tot vertex_list (decreases r) =
  match r with
  | ReachRefl _ -> Seq.empty
  | ReachTrans _ z _ r_xz -> 
    if ReachRefl? r_xz then Seq.empty
    else Seq.cons z (vertices_in_path g x z r_xz)

/// ---------------------------------------------------------------------------
/// Reachability from Set
/// ---------------------------------------------------------------------------

/// Vertex is reachable from some vertex in the set
let reachable_from (g: graph_state) (roots: vertex_list) 
                   (x: vertex_id{mem_graph_vertex g x}) : prop =
  exists (r: vertex_id{mem_graph_vertex g r}). 
    Seq.mem r roots /\ reachable g r x

/// Alias for backward compatibility
let reachable_from_set = reachable_from

/// All roots are reachable from roots
val roots_reachable : (g: graph_state) -> (roots: vertex_list) -> 
                      (r: vertex_id{mem_graph_vertex g r}) ->
  Lemma (requires Seq.mem r roots)
        (ensures reachable_from g roots r)

let roots_reachable g roots r =
  reach_refl g r;
  assert (reachable_from g roots r)

/// ---------------------------------------------------------------------------
/// Subset Operations
/// ---------------------------------------------------------------------------

/// s1 is a subset of s2
let subset_vertices (s1 s2: vertex_list) : prop =
  forall x. Seq.mem x s1 ==> Seq.mem x s2

/// Cardinal (length) of vertex set
let cardinal (s: vertex_set) : nat = Seq.length s

/// ---------------------------------------------------------------------------
/// Set Utilities
/// ---------------------------------------------------------------------------

/// Empty vertex set
let empty_set : vertex_set = Seq.empty

/// Check if set is empty
let is_emptySet (s: vertex_set) : bool = Seq.length s = 0

/// Non-empty set predicate
let nonEmpty_set (s: vertex_set) : bool = Seq.length s > 0

/// Get the last element of a non-empty sequence
let get_last_elem (s: vertex_set{Seq.length s > 0}) : vertex_id =
  Seq.index s (Seq.length s - 1)

/// Membership in prefix slice
let slice_mem_prefix (#a: eqtype) (s: seq a) (n: nat{n <= Seq.length s}) (x: a)
  : Lemma (Seq.mem x (Seq.slice s 0 n) ==> Seq.mem x s)
  = if Seq.mem x (Seq.slice s 0 n) then (
      // x is at some index i < n in the slice
      // That same index exists in s, so x is in s
      FStar.Seq.Properties.lemma_mem_append (Seq.slice s 0 n) (Seq.slice s n (Seq.length s));
      assert (s `Seq.equal` Seq.append (Seq.slice s 0 n) (Seq.slice s n (Seq.length s)))
    )

/// Slice of vertex set is vertex set (prefix case)
/// This requires complex reasoning about sequences and no-duplicates property
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec is_vertex_set_slice_prefix (s: vertex_list) (n: nat)
  : Lemma (requires is_vertex_set s /\ n <= Seq.length s)
          (ensures is_vertex_set (Seq.slice s 0 n))
          (decreases n)
  = if n = 0 then (
      // Empty slice is trivially a vertex_set
      assert (Seq.slice s 0 0 `Seq.equal` Seq.empty);
      assert (is_vertex_set Seq.empty)
    ) else (
      // n > 0
      let prefix = Seq.slice s 0 n in
      let hd_p = Seq.head prefix in
      let tl_p = Seq.tail prefix in
      
      // hd_p = s[0] = head s
      assert (hd_p = Seq.head s);
      
      // tl_p = slice s 1 n
      Seq.lemma_tail_slice s 0 n;
      assert (tl_p `Seq.equal` Seq.slice s 1 n);
      
      // Need: (1) hd_p not in tl_p, (2) is_vertex_set tl_p
      
      // (2) IH on tail: is_vertex_set (tail s) and n-1 <= length (tail s)
      // We need is_vertex_set (slice s 1 n) = is_vertex_set (slice (tail s) 0 (n-1))
      let tl_s = Seq.tail s in
      assert (is_vertex_set tl_s);
      // Show that slice s 1 n == slice tl_s 0 (n-1)
      // This follows from: s = cons (head s) (tail s), so s[i] = tl_s[i-1] for i >= 1
      assert (Seq.length tl_s = Seq.length s - 1);
      assert (n - 1 <= Seq.length tl_s);
      // Use pointwise equality
      let eq_lemma (i: nat{i < n - 1}) : Lemma (Seq.index (Seq.slice s 1 n) i = Seq.index (Seq.slice tl_s 0 (n-1)) i) =
        assert (Seq.index (Seq.slice s 1 n) i = Seq.index s (i + 1));
        assert (Seq.index (Seq.slice tl_s 0 (n-1)) i = Seq.index tl_s i);
        assert (Seq.index s (i + 1) = Seq.index tl_s i)
      in
      FStar.Classical.forall_intro eq_lemma;
      Seq.lemma_eq_intro (Seq.slice s 1 n) (Seq.slice tl_s 0 (n - 1));
      assert (Seq.slice s 1 n `Seq.equal` Seq.slice tl_s 0 (n - 1));
      is_vertex_set_slice_prefix tl_s (n - 1);
      assert (is_vertex_set tl_p);
      
      // (1) hd_p not in tl_p
      // hd_p = head s, tl_p = slice s 1 n
      // Since hd_p not in (tail s) (from is_vertex_set s),
      // and tl_p ⊆ tail s, we have hd_p not in tl_p
      let aux () : Lemma (not (Seq.mem hd_p tl_p)) =
        if Seq.mem hd_p tl_p then (
          // tl_p = slice s 1 n ⊆ tail s
          slice_mem_prefix tl_s (n - 1) hd_p;
          assert (Seq.mem hd_p tl_s);
          assert (is_vertex_set s);
          assert (not (Seq.mem (Seq.head s) (Seq.tail s)));
          assert False
        )
      in
      aux ();
      
      assert (is_vertex_set prefix)
    )
#pop-options

/// Prefix slice membership (useful for get_first)
let get_first_mem_lemma (s: vertex_set{Seq.length s > 0})  (y: vertex_id)
  : Lemma (Seq.mem y (Seq.slice s 0 (Seq.length s - 1)) ==> Seq.mem y s)
  = slice_mem_prefix s (Seq.length s - 1) y

/// Helper: vertex_set has no duplicate at different indices
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec vertex_set_no_dup_index_aux (s: vertex_set) (i: nat) (j: nat)
  : Lemma (requires i < Seq.length s /\ j < Seq.length s /\ i <> j /\ 
                     Seq.index s i = Seq.index s j)
          (ensures False)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (
      let hd = Seq.head s in
      let tl = Seq.tail s in
      if i = 0 then (
        // s[0] = s[j] for j > 0
        // s[j] = tl[j-1]
        // So hd = tl[j-1], meaning hd is in tl
        FStar.Seq.Properties.lemma_index_is_nth tl (j - 1);
        FStar.Seq.Properties.lemma_mem_snoc (Seq.slice tl 0 (j-1)) (Seq.index tl (j-1));
        assert (Seq.mem hd tl);
        assert (is_vertex_set s);
        assert (not (Seq.mem hd tl)); // from is_vertex_set
        assert False
      ) else if j = 0 then (
        // Symmetric case
        FStar.Seq.Properties.lemma_index_is_nth tl (i - 1);
        FStar.Seq.Properties.lemma_mem_snoc (Seq.slice tl 0 (i-1)) (Seq.index tl (i-1));
        assert (Seq.mem hd tl);
        assert False
      ) else (
        // Both i, j > 0, recurse on tail
        assert (Seq.index s i = Seq.index tl (i - 1));
        assert (Seq.index s j = Seq.index tl (j - 1));
        assert (is_vertex_set tl);
        vertex_set_no_dup_index_aux tl (i - 1) (j - 1)
      )
    )
#pop-options

/// Element in prefix not equal to last
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let slice_neq_last (s: vertex_set{Seq.length s > 0}) (x: vertex_id)
  : Lemma (requires Seq.mem x (Seq.slice s 0 (Seq.length s - 1)))
          (ensures x <> get_last_elem s)
  = let prefix = Seq.slice s 0 (Seq.length s - 1) in
    let last_elem = get_last_elem s in
    let n = Seq.length s in
    if x = last_elem then (
      // x is in prefix, so there exists index i < n-1 with prefix[i] = x
      // Get the index using index_mem
      let i = FStar.Seq.Properties.index_mem x prefix in
      // i < length prefix = n-1, and prefix[i] = x
      assert (i < n - 1);
      assert (Seq.index prefix i = x);
      // prefix[i] = s[i] (slice preserves indices)
      assert (Seq.index s i = x);
      // Also s[n-1] = last_elem = x
      assert (Seq.index s (n - 1) = x);
      // So s[i] = s[n-1] with i < n-1, contradicting no-duplicates
      vertex_set_no_dup_index_aux s i (n - 1)
    )
#pop-options

/// Helper: element in s (except last) is in prefix slice
/// Proof: s == prefix ++ suffix where suffix is just the last element
/// If y in s and y <> last, then y must be in prefix
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let mem_except_last_in_prefix (s: vertex_set{Seq.length s > 0}) (y: vertex_id)
  : Lemma (requires Seq.mem y s /\ y <> get_last_elem s)
          (ensures Seq.mem y (Seq.slice s 0 (Seq.length s - 1)))
  = let prefix = Seq.slice s 0 (Seq.length s - 1) in
    let last_elem = get_last_elem s in
    let suffix = Seq.slice s (Seq.length s - 1) (Seq.length s) in
    // s = prefix ++ suffix
    Seq.lemma_split s (Seq.length s - 1);
    FStar.Seq.Properties.lemma_mem_append prefix suffix;
    // mem y s <==> mem y prefix \/ mem y suffix (from lemma_mem_append)
    // suffix is singleton [last_elem]
    // Since y <> last_elem and suffix = [last_elem], ~(mem y suffix)
    // Therefore mem y prefix
    ()
#pop-options

/// Get all but the last element (stack pop operation)
#push-options "--z3rlimit 50"
let get_first (g: graph_state) (s: vertex_set{Seq.length s > 0 /\ subset_vertices s g.vertices})
  : Tot (r: vertex_set{Seq.length r + 1 = Seq.length s /\ 
                        subset_vertices r g.vertices /\
                        (forall y. Seq.mem y r ==> y <> get_last_elem s) /\
                        (forall y. Seq.mem y s /\ y <> get_last_elem s ==> Seq.mem y r)})
  = let s' = Seq.slice s 0 (Seq.length s - 1) in
    is_vertex_set_slice_prefix s (Seq.length s - 1);
    let aux (y: vertex_id) : Lemma (Seq.mem y s' ==> Seq.mem y g.vertices) =
      if Seq.mem y s' then slice_mem_prefix s (Seq.length s - 1) y
    in
    FStar.Classical.forall_intro aux;
    let aux2 (y: vertex_id) : Lemma (requires Seq.mem y s') (ensures y <> get_last_elem s) =
      slice_neq_last s y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux2);
    let aux3 (y: vertex_id) 
      : Lemma (requires Seq.mem y s /\ y <> get_last_elem s) (ensures Seq.mem y s')
      = mem_except_last_in_prefix s y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux3);
    s'
#pop-options

/// Insert a vertex into a vertex set (maintains uniqueness)
/// Key property for termination: if x not in s, then |result| = |s| + 1
let insert_to_vertex_set (g: graph_state) (x: vertex_id{mem_graph_vertex g x}) 
                         (s: vertex_set{subset_vertices s g.vertices})
  : Tot (r: vertex_set{subset_vertices r g.vertices /\ 
                        (Seq.mem x r) /\ 
                        (forall y. Seq.mem y r <==> Seq.mem y s \/ y = x) /\
                        (Seq.length r >= Seq.length s) /\
                        (~(Seq.mem x s) ==> Seq.length r = Seq.length s + 1) /\
                        (Seq.mem x s ==> Seq.length r = Seq.length s)})
  = if Seq.mem x s then s
    else 
      (is_vertex_set_cons x s; 
       mem_cons_lemma x x s;
       assert (Seq.mem x (Seq.cons x s));
       let aux (y: vertex_id) : Lemma (Seq.mem y (Seq.cons x s) <==> Seq.mem y s \/ y = x) =
         mem_cons_lemma y x s
       in
       FStar.Classical.forall_intro aux;
       Seq.cons x s)

/// Remove a vertex from a vertex set
let rec remove (s: vertex_set) (x: vertex_id{Seq.mem x s})
  : Tot (r: vertex_set{~(Seq.mem x r) /\ 
                        Seq.length r + 1 = Seq.length s /\
                        (forall y. y <> x ==> (Seq.mem y r <==> Seq.mem y s))})
        (decreases Seq.length s)
  = if Seq.head s = x then
      (assert (is_vertex_set (Seq.tail s));
       assert (~(Seq.mem x (Seq.tail s)));
       Seq.tail s)
    else
      let rest = remove (Seq.tail s) x in
      (is_vertex_set_cons (Seq.head s) rest;
       let aux (y: vertex_id) : Lemma (requires y <> x)
                                      (ensures Seq.mem y (Seq.cons (Seq.head s) rest) 
                                              <==> Seq.mem y s) =
         mem_cons_lemma y (Seq.head s) rest;
         mem_cons_lemma y (Seq.head s) (Seq.tail s)
       in
       FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
       mem_cons_lemma x (Seq.head s) rest;
       assert (~(Seq.mem x (Seq.cons (Seq.head s) rest)));
       Seq.cons (Seq.head s) rest)

/// Remove preserves membership for other elements
let remove_preserves_other (s: vertex_set) (x: vertex_id{Seq.mem x s}) (y: vertex_id)
  : Lemma (requires y <> x)
          (ensures Seq.mem y (remove s x) <==> Seq.mem y s)
  = () // Follows from remove's refined return type

/// Remove produces a vertex_set (already in return type, but useful as lemma)
let is_vertex_set_remove (s: vertex_set) (x: vertex_id{Seq.mem x s})
  : Lemma (ensures is_vertex_set (remove s x))
  = () // Follows from remove's return type: r: vertex_set

/// Remove decreases length by 1
let remove_length_lemma (s: vertex_set) (x: vertex_id{Seq.mem x s})
  : Lemma (ensures Seq.length (remove s x) = Seq.length s - 1)
  = () // Follows from remove's return type: Seq.length r + 1 = Seq.length s

/// Helper: subset_vertices is preserved when removing matching elements
let subset_vertices_remove_lemma (s1: vertex_set) (s2: vertex_set) (x: vertex_id)
  : Lemma (requires subset_vertices s1 s2 /\ 
                    Seq.mem x s1 /\ Seq.mem x s2 /\
                    ~(Seq.mem x (Seq.tail s1)))
          (ensures subset_vertices (Seq.tail s1) (remove s2 x))
  = let aux (y: vertex_id) 
      : Lemma (Seq.mem y (Seq.tail s1) ==> Seq.mem y (remove s2 x))
      = if Seq.mem y (Seq.tail s1) then (
          assert (Seq.mem y s1);
          assert (Seq.mem y s2);
          assert (y <> x);
          remove_preserves_other s2 x y
        )
    in
    FStar.Classical.forall_intro aux

/// If s1 ⊆ s2 and both are vertex_sets (no duplicates), then |s1| <= |s2|
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec subset_vertices_length_lemma (s1: vertex_set) (s2: vertex_set)
  : Lemma (requires subset_vertices s1 s2)
          (ensures Seq.length s1 <= Seq.length s2)
          (decreases Seq.length s1)
          [SMTPat (subset_vertices s1 s2)]
  = if Seq.length s1 = 0 then () 
    else (
      let hd = Seq.head s1 in
      let tl = Seq.tail s1 in
      assert (Seq.mem hd s1);
      assert (Seq.mem hd s2);
      is_vertex_set_tail s1;
      assert (~(Seq.mem hd tl));
      is_vertex_set_remove s2 hd;
      let s2' = remove s2 hd in
      remove_length_lemma s2 hd;
      subset_vertices_remove_lemma s1 s2 hd;
      subset_vertices_length_lemma tl s2'
    )
#pop-options

/// Union of two vertex sets
let rec union_vertex_sets (g: graph_state) 
                          (s1: vertex_set{subset_vertices s1 g.vertices}) 
                          (s2: vertex_set{subset_vertices s2 g.vertices})
  : Tot (r: vertex_set{(forall x. Seq.mem x r <==> Seq.mem x s1 \/ Seq.mem x s2) /\
                       subset_vertices r g.vertices})
        (decreases Seq.length s1)
  = if Seq.length s1 = 0 then s2
    else if Seq.mem (Seq.head s1) s2 then
      union_vertex_sets g (Seq.tail s1) s2
    else
      let rest = union_vertex_sets g (Seq.tail s1) s2 in
      (is_vertex_set_cons (Seq.head s1) rest;
       // Prove membership equivalence
       let aux (x: vertex_id) : Lemma (Seq.mem x (Seq.cons (Seq.head s1) rest)
                                       <==> Seq.mem x s1 \/ Seq.mem x s2) =
         mem_cons_lemma x (Seq.head s1) rest;
         mem_cons_lemma x (Seq.head s1) (Seq.tail s1)
       in
       FStar.Classical.forall_intro aux;
       // subset_vertices follows from aux and the facts that s1 and s2 are subsets
       assert (subset_vertices (Seq.cons (Seq.head s1) rest) g.vertices);
       Seq.cons (Seq.head s1) rest)

/// ---------------------------------------------------------------------------
/// Set Utility Lemmas
/// ---------------------------------------------------------------------------

/// Membership after insert
let insert_to_vertex_set_mem_lemma (g: graph_state) 
                                   (x: vertex_id{mem_graph_vertex g x})
                                   (s: vertex_set{subset_vertices s g.vertices})
                                   (y: vertex_id)
  : Lemma (let s' = insert_to_vertex_set g x s in
           Seq.mem y s' <==> (Seq.mem y s \/ y = x))
  = ()

/// Length after insert
let insert_to_vertex_set_length_lemma (g: graph_state)
                                      (x: vertex_id{mem_graph_vertex g x})
                                      (s: vertex_set{subset_vertices s g.vertices})
  : Lemma (let s' = insert_to_vertex_set g x s in
           if Seq.mem x s then Seq.length s' = Seq.length s
           else Seq.length s' = Seq.length s + 1)
  = if Seq.mem x s then () else is_vertex_set_cons x s

/// Subset after remove
let remove_lemma_subset (s: vertex_set) (x: vertex_id{Seq.mem x s}) (s': vertex_set)
  : Lemma (requires s' == remove s x)
          (ensures subset_vertices s' s)
  = () // Follows from remove postcondition: forall y. y <> x ==> (Seq.mem y s' <==> Seq.mem y s)

/// Membership in union
let union_vertex_sets_mem_lemma (g: graph_state)
                                (s1: vertex_set{subset_vertices s1 g.vertices})
                                (s2: vertex_set{subset_vertices s2 g.vertices})
                                (x: vertex_id)
  : Lemma (let u = union_vertex_sets g s1 s2 in
           Seq.mem x u <==> (Seq.mem x s1 \/ Seq.mem x s2))
  = () // Follows from union postcondition

/// ---------------------------------------------------------------------------
/// DFS Spanning Tree (Ghost State for Proofs)
/// ---------------------------------------------------------------------------

/// DFS spanning tree - captures provenance of visited vertices
/// Each node records which vertex discovered its children
noeq type dfs_tree : Type =
  | Leaf : dfs_tree
  | Node : (v: vertex_id) -> (children: list dfs_tree) -> dfs_tree

/// DFS forest for multiple roots
type dfs_forest = list dfs_tree

/// Membership in a single tree - using explicit recursion for termination
let rec mem_tree (x: vertex_id) (t: dfs_tree) : Tot bool (decreases t) =
  match t with
  | Leaf -> false
  | Node v children -> x = v || mem_tree_list x children

and mem_tree_list (x: vertex_id) (ts: list dfs_tree) : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: rest -> mem_tree x t || mem_tree_list x rest

/// Membership in a forest
let mem_forest (x: vertex_id) (f: dfs_forest) : bool =
  mem_tree_list x f

/// Flatten tree to vertex set (for connecting to visited set)
let rec tree_vertices (t: dfs_tree) : Tot (list vertex_id) (decreases t) =
  match t with
  | Leaf -> []
  | Node v children -> v :: tree_vertices_list children

and tree_vertices_list (ts: list dfs_tree) : Tot (list vertex_id) (decreases ts) =
  match ts with
  | [] -> []
  | t :: rest -> tree_vertices t @ tree_vertices_list rest

/// Flatten forest to vertex set
let forest_vertices (f: dfs_forest) : list vertex_id =
  tree_vertices_list f

/// Check if child is immediate successor of a node
let is_immediate_child (child: vertex_id) (t: dfs_tree) : bool =
  match t with
  | Leaf -> false
  | Node _ _ -> child = (match t with Node c _ -> c)

/// Parent-child relationship in tree - explicit recursion for termination
let rec is_parent_of (parent: vertex_id) (child: vertex_id) (t: dfs_tree) : Tot bool (decreases t) =
  match t with
  | Leaf -> false
  | Node v children ->
    // parent is v and child is root of some subtree
    (v = parent && is_parent_of_list_imm child children) ||
    // Or recurse into children
    is_parent_of_list parent child children

and is_parent_of_list_imm (child: vertex_id) (ts: list dfs_tree) : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: rest -> 
    (match t with 
     | Leaf -> false 
     | Node c _ -> c = child) || is_parent_of_list_imm child rest

and is_parent_of_list (parent: vertex_id) (child: vertex_id) (ts: list dfs_tree) 
  : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | t :: rest -> is_parent_of parent child t || is_parent_of_list parent child rest

/// Key invariant: if parent discovered child, there's an edge parent -> child
/// This is the property we'll maintain during DFS construction
let tree_edge_property (g: graph_state) (t: dfs_tree) : prop =
  forall parent child. is_parent_of parent child t ==> mem_graph_edge g parent child

/// Edge property for entire forest
let rec forest_edge_property (g: graph_state) (f: dfs_forest) : prop =
  match f with
  | [] -> True
  | t :: rest -> tree_edge_property g t /\ forest_edge_property g rest

/// Key lemma: in a tree with edge property, successors of tree members are also in tree
/// This is the inversion of tree_edge_property
/// If x is in tree and y is a successor of x (edge x->y), then either:
/// 1. y is a child of x in the tree (y was unvisited when x was processed)
/// 2. y is elsewhere in the tree (y was already visited)
/// Both cases mean y is in the tree.
///
/// For DFS trees built from empty_set: the tree covers all processed vertices,
/// and the edge property ensures successors are captured.

/// Successor closure for a tree: all successors of members are also members
let tree_successor_closed (g: graph_state) (t: dfs_tree) : prop =
  forall x y. mem_tree x t /\ mem_graph_edge g x y /\ mem_graph_vertex g y ==> mem_tree y t

/// Successor closure for a forest
let forest_successor_closed (g: graph_state) (f: dfs_forest) : prop =
  forall x y. mem_forest x f /\ mem_graph_edge g x y /\ mem_graph_vertex g y ==> mem_forest y f

/// Weaker version: successors are in forest OR in initial visited set
/// This is what we can actually prove for dfs_aux
let forest_successor_closed_wrt (g: graph_state) (f: dfs_forest) (visited: vertex_set) : prop =
  forall x y. mem_forest x f /\ mem_graph_edge g x y /\ mem_graph_vertex g y ==> 
              mem_forest y f \/ Seq.mem y visited

/// When visited is empty, the two notions coincide
let forest_successor_closed_wrt_empty (g: graph_state) (f: dfs_forest)
  : Lemma (requires forest_successor_closed_wrt g f empty_set)
          (ensures forest_successor_closed g f)
  = ()

/// ---------------------------------------------------------------------------
/// Successors Bridge Lemmas
/// ---------------------------------------------------------------------------

/// successors_aux distributes over cons
val successors_aux_cons : (hd: edge) -> (tl: edge_list) -> (v: vertex_id) ->
  Lemma (ensures successors_aux (Seq.cons hd tl) v ==
                 (let (src, dst) = hd in
                  if src = v then Seq.cons dst (successors_aux tl v)
                  else successors_aux tl v))

#push-options "--fuel 2 --ifuel 1"
let successors_aux_cons hd tl v =
  assert (Seq.length (Seq.cons hd tl) > 0);
  assert (Seq.head (Seq.cons hd tl) == hd);
  assert (Seq.equal (Seq.tail (Seq.cons hd tl)) tl)
#pop-options
