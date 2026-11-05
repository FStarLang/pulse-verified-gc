module GC.Spec.Graph.Within

open FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

let intro (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y: a) (l: list a)
  : Lemma (requires path_within e p x y l) (ensures reach_within e p x y)
  = FStar.Classical.exists_intro (fun l -> path_within e p x y l) l

let reach_within_refl #a e p x = intro e p x x []

let reach_within_cons #a e p x z y =
  FStar.Classical.exists_elim (reach_within e p x y) #_ #(fun l -> path_within e p z y l) ()
    (fun l -> intro e p x y (z :: l))

let reach_within_edge #a e p x y =
  reach_within_refl e p y;
  reach_within_cons e p x y y

let rec path_ends (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y: a) (l: list a)
  : Lemma (requires path_within e p x y l) (ensures p x /\ p y) (decreases l)
  = match l with
    | [] -> ()
    | z :: rest -> path_ends e p z y rest

let rec path_trans (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (x y z: a) (l1 l2: list a)
  : Lemma (requires path_within e p x y l1 /\ path_within e p y z l2)
          (ensures path_within e p x z (l1 @ l2))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | w :: rest -> path_trans e p w y z rest l2

let reach_within_trans #a e p x y z =
  FStar.Classical.exists_elim (reach_within e p x z) #_ #(fun l -> path_within e p x y l) ()
    (fun l1 ->
      FStar.Classical.exists_elim (reach_within e p x z) #_ #(fun l -> path_within e p y z l) ()
        (fun l2 -> path_trans e p x y z l1 l2; intro e p x z (l1 @ l2)))

let reach_within_ends #a e p x y =
  FStar.Classical.exists_elim (p x /\ p y) #_ #(fun l -> path_within e p x y l) ()
    (fun l -> path_ends e p x y l)

let rec reach_within_suffix #a e p x y l m : Lemma (requires path_within e p x y l /\ on_path x l m) (ensures reach_within e p m y) (decreases l) =
  if m = x then intro e p x y l
  else match l with
    | z :: rest -> reach_within_suffix e p z y rest m

let rec path_mono (#a: eqtype) (e e': a -> a -> prop) (p p': a -> prop) (x y: a) (l: list a)
  : Lemma (requires path_within e p x y l /\
                    (forall (v: a). p v ==> p' v) /\
                    (forall (u v: a). p u /\ p v /\ e u v ==> e' u v))
          (ensures path_within e' p' x y l)
          (decreases l)
  = match l with
    | [] -> ()
    | z :: rest -> path_ends e p z y rest; path_mono e e' p p' z y rest

let reach_within_mono #a e e' p p' x y =
  FStar.Classical.exists_elim (reach_within e' p' x y) #_ #(fun l -> path_within e p x y l) ()
    (fun l -> path_mono e e' p p' x y l; intro e' p' x y l)

let rec path_without (#a: eqtype) (e: a -> a -> prop) (p: a -> prop) (u x y: a) (l: list a)
  : Lemma (requires path_within e p x y l)
          (ensures reach_within e (without p u) x y \/ y == u \/
                   (exists (s: a). e u s /\ reach_within e (without p u) s y))
          (decreases l)
  = match l with
    | [] -> if x = u then () else reach_within_refl e (without p u) x
    | z :: rest ->
      path_without e p u z y rest;
      if x = u then ()
      else FStar.Classical.move_requires (reach_within_cons e (without p u) x z) y

let reach_within_without #a e p u x y =
  FStar.Classical.exists_elim
    (reach_within e (without p u) x y \/ y == u \/
     (exists (s: a). e u s /\ reach_within e (without p u) s y))
    #_ #(fun l -> path_within e p x y l) ()
    (fun l -> path_without e p u x y l)

let rec path_edge_removed (#a: eqtype) (e e': a -> a -> prop) (p: a -> prop) (u v x y: a) (l: list a)
  : Lemma (requires path_within e p x y l /\
                    (forall (s t: a). e s t /\ ~(s == u /\ t == v) ==> e' s t))
          (ensures reach_within e' p x y \/ reach_within e' p v y)
          (decreases l)
  = match l with
    | [] -> reach_within_refl e' p x
    | z :: rest ->
      path_edge_removed e e' p u v z y rest;
      if x = u && z = v then ()
      else FStar.Classical.move_requires (reach_within_cons e' p x z) y

let reach_within_edge_removed #a e e' p u v x y =
  FStar.Classical.exists_elim (reach_within e' p x y \/ reach_within e' p v y)
    #_ #(fun l -> path_within e p x y l) ()
    (fun l -> path_edge_removed e e' p u v x y l)

let rec path_restart (#a: eqtype) (e e': a -> a -> prop) (p p' q: a -> prop) (x y: a) (l: list a)
  : Lemma (requires path_within e p x y l /\
                    (forall (v: a). p v ==> p' v) /\
                    (forall (s t: a). p s /\ p t /\ e s t ==> e' s t \/ q t))
          (ensures reach_within e' p' x y \/
                   (exists (t: a). q t /\ p t /\ reach_within e' p' t y))
          (decreases l)
  = match l with
    | [] -> reach_within_refl e' p' x
    | z :: rest ->
      path_ends e p z y rest;
      path_restart e e' p p' q z y rest;
      FStar.Classical.move_requires (reach_within_cons e' p' x z) y

let reach_within_restart #a e e' p p' q x y =
  FStar.Classical.exists_elim
    (reach_within e' p' x y \/ (exists (t: a). q t /\ p t /\ reach_within e' p' t y))
    #_ #(fun l -> path_within e p x y l) ()
    (fun l -> path_restart e e' p p' q x y l)
