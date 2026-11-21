/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ToyRep - the toy's representation: the model itself
/// ---------------------------------------------------------------------------
///
/// The toy collector works on model heaps; its representation relation is
/// equality, its reads are the model's, and every word is storable.  Its
/// nursery allocates at the first place with room (`yfind`, a search the
/// runs of GC.Spec.Top.Vacuity compute).  `toy_rep_faithful`: it meets
/// every faithfulness condition of GC.Spec.Top.Rep.

module GC.Spec.Top.ToyRep

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.IdRep
module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The nursery's allocation: the first place with room
/// ---------------------------------------------------------------------------

let rec ex_below (n: nat) (f: nat -> bool) : bool =
  if n = 0 then false else f (n - 1) || ex_below (n - 1) f

let rec ex_below_iff (n: nat) (f: nat -> bool)
  : Lemma (ex_below n f == true <==> (exists (i: nat). i < n /\ f i == true))
  = if n > 0 then ex_below_iff (n - 1) f

let cov_at (y: mheap) (w: nat) (x: nat) : bool = covers y x w

/// Some block covers word `o + j`.
let hit (y: mheap) (o: nat) (j: nat) : bool = ex_below (o + j + 1) (cov_at y (o + j))

let yfree_b (y: mheap) (o: nat) (sz: size_t) : bool =
  o + sz < y.size && not (ex_below (sz + 1) (hit y o))

let hit_iff (y: mheap) (o j: nat)
  : Lemma (hit y o j == true <==> (exists (x: nat). covers y x (o + j)))
  = ex_below_iff (o + j + 1) (cov_at y (o + j))

let yfree_b_iff (y: mheap) (o: nat) (sz: size_t)
  : Lemma (yfree_b y o sz == true <==> young_free y o sz)
  = ex_below_iff (sz + 1) (hit y o);
    FStar.Classical.forall_intro (hit_iff y o);
    let aux (x w: nat) : Lemma (covers y x w /\ o <= w /\ w <= o + sz ==> hit y o (w - o) == true)
      = if covers y x w && o <= w && w <= o + sz then hit_iff y o (w - o) in
    FStar.Classical.forall_intro_2 aux

let rec yfind (y: mheap) (sz: size_t) (o: nat) (fuel: nat) : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else if yfree_b y o sz then Some o
  else yfind y sz (o + 1) (fuel - 1)

let rec yfind_some (y: mheap) (sz: size_t) (o fuel p: nat)
  : Lemma (requires yfind y sz o fuel == Some p) (ensures yfree_b y p sz == true) (decreases fuel)
  = if fuel > 0 && not (yfree_b y o sz) then yfind_some y sz (o + 1) (fuel - 1) p

let rec yfind_none (y: mheap) (sz: size_t) (o fuel q: nat)
  : Lemma (requires yfind y sz o fuel == None /\ o <= q /\ q < o + fuel)
          (ensures yfree_b y q sz == false) (decreases fuel)
  = if q > o then yfind_none y sz (o + 1) (fuel - 1) q

let tyalloc (y: mheap) (sz: size_t) (tag: tag_t) (vs: list value) : GTot (option (nat & mheap)) =
  match yfind y sz 0 y.size with
  | Some o -> Some (o, young_alloc y o sz tag vs)
  | None -> None

/// ---------------------------------------------------------------------------
/// The representation
/// ---------------------------------------------------------------------------

let trepr (m h: mheap) : prop = m == h
let tall (_: nat) : bool = true
let tstore (_: value) : bool = true
let tsize (h: mheap) : GTot nat = h.size
let thd (h: mheap) (o: nat) : GTot (option header) = h.hd o
let tread (h: mheap) (o i: nat) : GTot value = field h o i
let tyreset (y: mheap) : GTot mheap = empty_heap y.size
let tyinit (n: nat) : GTot mheap = empty_heap n
let tywrite (y: mheap) (o i: nat) (v: value) : GTot mheap = set_field y o i v

let toy_rep : rep mheap mheap = {
  repr = trepr; size_ok = tall; storable = tstore; rsize = tsize; rhd = thd; read = tread;
  yrepr = trepr; ysize_ok = tall; ymax = 1; ysize = tsize; yhd = thd; yread = tread;
  yinit = tyinit; yalloc = tyalloc; ywrite = tywrite; yreset = tyreset;
}

let toy_rep_id () : Lemma (is_id toy_rep)
  = reveal_opaque (`%is_id) (is_id toy_rep)

let toy_rich () : Lemma (rich toy_rep)
  = assert (toy_rep.size_ok 2); assert (toy_rep.ysize_ok 2)

let toy_major () : Lemma (faithful_major toy_rep)
  = let s (m: mheap) : Lemma (representable toy_rep m ==> (exists (h: mheap). toy_rep.repr m h))
      = assert (toy_rep.repr m m) in
    FStar.Classical.forall_intro s

let toy_yalloc (y: mheap) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (yalloc_ok toy_rep y sz tag vs)
  = match yfind y sz 0 y.size with
    | Some o -> yfind_some y sz 0 y.size o; yfree_b_iff y o sz
    | None ->
      let aux (q: nat) : Lemma (~(young_free y q sz))
        = yfree_b_iff y q sz;
          if q < y.size then yfind_none y sz 0 y.size q in
      FStar.Classical.forall_intro aux

let toy_young () : Lemma (faithful_young toy_rep)
  = FStar.Classical.forall_intro_4 toy_yalloc

let toy_rep_faithful () : Lemma (faithful toy_rep)
  = toy_rich (); toy_major (); toy_young ()
