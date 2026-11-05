/// ---------------------------------------------------------------------------
/// GC.Spec.Graph.Within - reachability through vertices satisfying a predicate
/// ---------------------------------------------------------------------------
///
/// `reach_within e p x y`: there is a path from `x` to `y` along the edge
/// relation `e` whose every vertex, both ends included, satisfies `p`.
///
/// The relation and the predicate are parameters, so the module serves any
/// graph: `GC.Spec.Graph`'s `graph_state` (with `mem_graph_edge`) or a relation
/// read directly off the heap.  Incremental marking uses it with `p` = "a grey
/// or white block" (`GC.Spec.MarkPhase.marker_will_reach`).
///
/// The lemmas are the ones a colour change or an edge change needs:
///   * a path survives a larger predicate and more edges (`reach_within_mono`);
///   * the part of a path from any vertex on it is a path (`reach_within_suffix`);
///   * taking one vertex `u` out of the predicate breaks only paths through `u`,
///     and each such path restarts, after its last visit to `u`, at a
///     successor of `u` (`reach_within_without`);
///   * deleting one edge `u -> v` breaks only paths through it, and each
///     restarts at `v` (`reach_within_edge_removed`).

module GC.Spec.Graph.Within

/// A path from `x` to `y` through `l` (the vertices after `x`, in order): each
/// vertex satisfies `p` and consecutive vertices are joined by `e`.
let rec path_within (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y: a) (l: list a)
  : Tot prop (decreases l)
  = p x /\
    (match l with
     | [] -> x == y
     | z :: rest -> e x z /\ path_within e p z y rest)

/// `y` is reachable from `x` through vertices satisfying `p`.
let reach_within (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y: a) : prop =
  exists (l: list a). path_within e p x y l

/// The predicate `p` with the vertex `u` taken out.
let without (#a: eqtype) (p: a -> prop) (u: a) : a -> prop = fun v -> p v /\ v <> u

/// ---------------------------------------------------------------------------
/// Building paths
/// ---------------------------------------------------------------------------

val reach_within_refl (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x: a)
  : Lemma (requires p x) (ensures reach_within e p x x)

/// Prepend an edge.
val reach_within_cons (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x z y: a)
  : Lemma (requires p x /\ e x z /\ reach_within e p z y)
          (ensures reach_within e p x y)

/// A single edge between two vertices satisfying `p`.
val reach_within_edge (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y: a)
  : Lemma (requires p x /\ p y /\ e x y)
          (ensures reach_within e p x y)

val reach_within_trans (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y z: a)
  : Lemma (requires reach_within e p x y /\ reach_within e p y z)
          (ensures reach_within e p x z)

/// Both ends satisfy `p`.
val reach_within_ends (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y: a)
  : Lemma (requires reach_within e p x y)
          (ensures p x /\ p y)

/// ---------------------------------------------------------------------------
/// Paths on a path
/// ---------------------------------------------------------------------------

/// `m` is a vertex of the path from `x` through `l`.
let on_path (#a: eqtype) (x: a) (l: list a) (m: a) : prop = m == x \/ FStar.List.Tot.memP m l

/// The part of a path from any vertex on it is a path.
val reach_within_suffix (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y: a) (l: list a) (m: a)
  : Lemma (requires path_within e p x y l /\ on_path x l m)
          (ensures reach_within e p m y)

/// ---------------------------------------------------------------------------
/// Changes to the predicate and to the edges
/// ---------------------------------------------------------------------------

/// A larger predicate and more edges (between vertices satisfying `p`) keep
/// every path.
val reach_within_mono (#a: eqtype) (e e': a -> a -> prop) (p p': a -> prop) (x y: a)
  : Lemma (requires reach_within e p x y /\
                    (forall (v: a). p v ==> p' v) /\
                    (forall (u v: a). p u /\ p v /\ e u v ==> e' u v))
          (ensures reach_within e' p' x y)

/// Taking `u` out of the predicate: a path either avoids `u`, or ends at `u`,
/// or -- from its last visit to `u` -- continues at a successor `s` of `u`
/// along a path that avoids `u`.
val reach_within_without (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (u x y: a)
  : Lemma (requires reach_within e p x y)
          (ensures reach_within e (without p u) x y \/ y == u \/
                   (exists (s: a). e u s /\ reach_within e (without p u) s y))

/// Deleting the edge `u -> v` (and keeping every other one): a path either
/// survives, or -- from its last use of that edge -- restarts at `v`.
val reach_within_edge_removed (#a: eqtype) (e e': a -> a -> prop) (p: a -> prop) (u v x y: a)
  : Lemma (requires reach_within e p x y /\
                    (forall (s t: a). e s t /\ ~(s == u /\ t == v) ==> e' s t))
          (ensures reach_within e' p x y \/ reach_within e' p v y)

/// The general form of the last two: when every edge of a path either
/// survives the change or ends at a vertex satisfying `q` (and every vertex
/// still satisfies the new predicate), a path either survives, or -- from the
/// last broken edge on -- restarts at a vertex satisfying `q`.  A colour
/// change that greys the target of every edge it breaks is the use case.
val reach_within_restart (#a: eqtype) (e e': a -> a -> prop) (p p' q: a -> prop) (x y: a)
  : Lemma (requires reach_within e p x y /\
                    (forall (v: a). p v ==> p' v) /\
                    (forall (s t: a). p s /\ p t /\ e s t ==> e' s t \/ q t))
          (ensures reach_within e' p' x y \/
                   (exists (t: a). q t /\ p t /\ reach_within e' p' t y))
