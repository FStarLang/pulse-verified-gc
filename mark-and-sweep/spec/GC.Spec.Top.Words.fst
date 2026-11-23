/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Words - tiling, words, and what a step keeps
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 3).  Facts about one model heap, or a heap and
/// the next one, that every step lemma uses:
///   - tiling: each word below `size` is covered by exactly one block, so a
///     word is free or in use, not both (`word_xor`);
///   - the Fill and a store change only the fields of their block
///     (`fill_other`, `set_field_other`);
///   - a pointer that resolves to a block keeps resolving to it in a heap
///     where that block keeps its size, tag and fields (`resolve_keep`);
///   - reachability stays inside any set that holds the outside refs and is
///     closed under edges (`reach_within`, as `ToyComps.reach_within`).

module GC.Spec.Top.Words

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Tiling
/// ---------------------------------------------------------------------------

let cover_unique (m: mheap) (o1 o2 w: nat)
  : Lemma (requires well_formed m /\ covers m o1 w /\ covers m o2 w) (ensures o1 == o2)
  = ()

let cover_exists (m: mheap) (w: nat)
  : Lemma (requires well_formed m /\ w < m.size) (ensures exists (o: nat). covers m o w)
  = ()

/// A block's own header word is covered by it alone.
let cover_self (m: mheap) (o x: nat)
  : Lemma (requires well_formed m /\ is_block m o /\ covers m x o) (ensures x == o)
  = assert (covers m o o)

/// No word is covered by two blocks (the major heap's tiling, the
/// nursery's `young_ok`).
let unique_cover (m: mheap) : prop =
  forall (o1 o2 w: nat). covers m o1 w /\ covers m o2 w ==> o1 == o2

let unique_wf (m: mheap) : Lemma (requires well_formed m) (ensures unique_cover m) = ()

let unique_young (m: mheap) : Lemma (requires young_ok m) (ensures unique_cover m) = ()

/// A field word of a block is not the start of a block.
let field_not_block (m: mheap) (o w: nat)
  : Lemma (requires unique_cover m /\ covers m o w /\ o < w) (ensures ~(is_block m w))
  = if is_block m w then assert (covers m w w)

/// **A word below `size` is free or in use, exactly one.**
let word_xor (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap) (w: nat)
  : Lemma (requires well_formed m /\ w < m.size)
          (ensures (free_word a st h m w <==> ~(in_use_word a st h m w)) /\
                   (in_use_word a st h m w \/ free_word a st h m w))
  = cover_exists m w;
    let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> covers m o w) in
    C.forall_intro (C.move_requires (cover_unique m o w))

/// A block in use covers no free word, and a free block no in-use word.
let in_use_not_free (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap) (o w: nat)
  : Lemma (requires well_formed m /\ covers m o w /\ in_use a st h m o)
          (ensures in_use_word a st h m w /\ ~(free_word a st h m w))
  = C.forall_intro (C.move_requires (cover_unique m o w))

let free_not_in_use (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap) (o w: nat)
  : Lemma (requires well_formed m /\ covers m o w /\ a.free st h o == true)
          (ensures free_word a st h m w /\ ~(in_use_word a st h m w))
  = C.forall_intro (C.move_requires (cover_unique m o w))

/// The words of a block, through the block covering it.
let in_use_word_block (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m: mheap) (w: nat)
  : Lemma (requires in_use_word a st h m w)
          (ensures exists (o: nat). covers m o w /\ in_use a st h m o)
  = ()

/// ---------------------------------------------------------------------------
/// The Fill and a store
/// ---------------------------------------------------------------------------

let fill_hd (m: mheap) (o: nat) (vs: list value)
  : Lemma (ensures (fill m o vs).size == m.size /\ (forall (x: nat). (fill m o vs).hd x == m.hd x))
  = ()

let fill_field (m: mheap) (o: nat) (vs: list value) (i: nat)
  : Lemma (requires i < L.length vs) (ensures field (fill m o vs) o i == L.index vs i)
  = ()

/// The Fill of a block leaves every other block's fields.
let fill_other (m: mheap) (o: nat) (vs: list value) (x i: nat)
  : Lemma (requires unique_cover m /\ is_block m o /\ L.length vs <= wz_of m o /\ x <> o /\
                    is_block m x /\ i < wz_of m x)
          (ensures field (fill m o vs) x i == field m x i)
  = let w = x + 1 + i in
    if o < w && w - o - 1 < L.length vs then begin
      assert (covers m o w); assert (covers m x w)
    end

/// The words a Fill touches are fields of its block.
let fill_body (m: mheap) (o: nat) (vs: list value) (w: nat)
  : Lemma (requires is_block m o /\ L.length vs <= wz_of m o)
          (ensures (fill m o vs).body w == m.body w \/ (covers m o w /\ o < w))
  = ()

let set_field_other (m: mheap) (o i x j: nat) (v: value)
  : Lemma (requires unique_cover m /\ is_block m o /\ i < wz_of m o /\ is_block m x /\ j < wz_of m x /\
                    ~(x == o /\ j == i))
          (ensures field (set_field m o i v) x j == field m x j)
  = let w = x + 1 + j in
    if w = o + 1 + i then begin
      assert (covers m o w); assert (covers m x w)
    end

/// ---------------------------------------------------------------------------
/// Resolution kept
/// ---------------------------------------------------------------------------

/// `m'` keeps block `o`: a block, same size, tag and fields.
let keeps (m m': mheap) (o: nat) : prop =
  is_block m o /\ is_block m' o /\ wz_of m' o == wz_of m o /\ tag_of m' o == tag_of m o /\
  (forall (i: nat). i < wz_of m o ==> field m' o i == field m o i)

/// What resolving through an infix header says.
let resolve_infix (m: mheap) (a o: nat)
  : Lemma (requires resolve m a == Some o /\ a <> o)
          (ensures ~(is_block m a) /\ o < a /\ infix_hdr (m.body a) == Some (a - o) /\ a - o >= 2 /\
                   is_block m o /\ tag_of m o == closure_tag /\ a - o < wz_of m o)
  = ()

let resolve_infix_intro (m: mheap) (a o: nat)
  : Lemma (requires ~(is_block m a) /\ o < a /\ infix_hdr (m.body a) == Some (a - o) /\ a - o >= 2 /\
                    is_block m o /\ tag_of m o == closure_tag /\ a - o < wz_of m o)
          (ensures resolve m a == Some o)
  = ()

let body_of_field (m m': mheap) (o a: nat)
  : Lemma (requires o < a /\ field m' o (a - o - 1) == field m o (a - o - 1)) (ensures m'.body a == m.body a)
  = ()

/// **A pointer resolving to a block that the next heap keeps resolves to it
/// there.**
let resolve_keep (m m': mheap) (a o: nat)
  : Lemma (requires resolve m a == Some o /\ keeps m m' o /\ unique_cover m')
          (ensures resolve m' a == Some o)
  = if a = o then ()
    else begin
      resolve_infix m a o;
      assert (field m' o (a - o - 1) == field m o (a - o - 1));
      body_of_field m m' o a;
      assert (covers m' o a);
      field_not_block m' o a;
      resolve_infix_intro m' a o
    end

/// A resolved pointer resolves to a block.
let resolve_block (m: mheap) (a o: nat)
  : Lemma (requires resolve m a == Some o) (ensures is_block m o /\ covers m o a)
  = ()

/// ---------------------------------------------------------------------------
/// Reachability within a set
/// ---------------------------------------------------------------------------

let rec reach_within (w: world) (s: nat -> prop) (o: nat) (r: reach w o)
  : Lemma (requires (forall (x: nat). outside_ref w x ==> s x) /\
                    (forall (x x': nat). s x /\ major_edge w.maj x x' ==> s x'))
          (ensures s o)
          (decreases r)
  = match r with
    | RBase _ _ -> ()
    | RStep x _ r' _ -> reach_within w s x r'

let reachable_within (w: world) (s: nat -> prop) (o: nat)
  : Lemma (requires (forall (x: nat). outside_ref w x ==> s x) /\
                    (forall (x x': nat). s x /\ major_edge w.maj x x' ==> s x') /\ reachable w o)
          (ensures s o)
  = let aux (r: reach w o) : Lemma (s o) = reach_within w s o r in
    C.forall_intro aux

/// One edge from a reachable object.
let reach_edge (w: world) (o o': nat)
  : Lemma (requires reachable w o /\ major_edge w.maj o o') (ensures reachable w o')
  = let aux (r: reach w o) : Lemma (reachable w o') = let r' : reach w o' = RStep o o' r () in () in
    C.forall_intro aux

let reach_outside (w: world) (o: nat)
  : Lemma (requires outside_ref w o) (ensures reachable w o)
  = let r : reach w o = RBase o () in ()

let reach_root (w: world) (a o: nat)
  : Lemma (requires L.memP (VPtr (Major a)) w.roots /\ resolve w.maj a == Some o) (ensures reachable w o)
  = reach_outside w o

let reach_young (w: world) (y i a o: nat)
  : Lemma (requires ptr_field w.yng y i /\ field w.yng y i == VPtr (Major a) /\ resolve w.maj a == Some o)
          (ensures reachable w o)
  = reach_outside w o

let reach_field (w: world) (o i a o': nat)
  : Lemma (requires reachable w o /\ ptr_field w.maj o i /\ field w.maj o i == VPtr (Major a) /\
                    resolve w.maj a == Some o')
          (ensures reachable w o')
  = reach_edge w o o'

/// ---------------------------------------------------------------------------
/// The nursery's operations
/// ---------------------------------------------------------------------------

let yalloc_covers (y: mheap) (n: nat) (sz: size_t) (tag: tag_t) (vs: list value) (x w: nat)
  : Lemma (requires young_free y n sz)
          (ensures covers (young_alloc y n sz tag vs) x w <==>
                   ((x == n /\ n <= w /\ w <= n + sz) \/ (x <> n /\ covers y x w)))
  = if is_block y n then assert (covers y n n)

let yalloc_young_ok (y: mheap) (n: nat) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires young_ok y /\ young_free y n sz /\ tag <> infix_tag)
          (ensures young_ok (young_alloc y n sz tag vs))
  = C.forall_intro_2 (yalloc_covers y n sz tag vs);
    if is_block y n then assert (covers y n n)

/// The allocation keeps every block of the nursery.
let yalloc_keeps (y: mheap) (n: nat) (sz: size_t) (tag: tag_t) (vs: list value) (o: nat)
  : Lemma (requires young_ok y /\ young_free y n sz /\ L.length vs == sz /\ is_block y o)
          (ensures keeps y (young_alloc y n sz tag vs) o /\ o <> n)
  = assert (covers y o o);
    let aux (i: nat) : Lemma (i < wz_of y o ==> field (young_alloc y n sz tag vs) o i == field y o i)
      = if i < wz_of y o then assert (covers y o (o + 1 + i)) in
    C.forall_intro aux

let yalloc_resolve (y: mheap) (n: nat) (sz: size_t) (tag: tag_t) (vs: list value) (b o: nat)
  : Lemma (requires young_ok y /\ young_free y n sz /\ L.length vs == sz /\ tag <> infix_tag /\
                    resolve y b == Some o)
          (ensures resolve (young_alloc y n sz tag vs) b == Some o)
  = yalloc_keeps y n sz tag vs o;
    yalloc_young_ok y n sz tag vs;
    resolve_keep y (young_alloc y n sz tag vs) b o

let yalloc_new_field (y: mheap) (n: nat) (sz: size_t) (tag: tag_t) (vs: list value) (i: nat)
  : Lemma (requires L.length vs == sz /\ i < sz)
          (ensures is_block (young_alloc y n sz tag vs) n == (n < y.size) /\
                   wz_of (young_alloc y n sz tag vs) n == sz /\ tag_of (young_alloc y n sz tag vs) n == tag /\
                   field (young_alloc y n sz tag vs) n i == L.index vs i)
  = ()

/// A store into a field of a block that is not a closure resolves as before.
let set_field_resolve (m: mheap) (o i: nat) (v: value) (b: nat)
  : Lemma (requires unique_cover m /\ is_block m o /\ i < wz_of m o /\ tag_of m o <> closure_tag)
          (ensures resolve (set_field m o i v) b == resolve m b)
  = let m' = set_field m o i v in
    if is_block m b then ()
    else if b = o + 1 + i then begin
      assert (covers m o b);
      (match infix_hdr (m.body b) with
       | Some k -> if k >= 2 && k <= b && is_block m (b - k) && tag_of m (b - k) = closure_tag && k < wz_of m (b - k)
                  then assert (covers m (b - k) b)
       | None -> ());
      (match infix_hdr (m'.body b) with
       | Some k -> if k >= 2 && k <= b && is_block m (b - k) && tag_of m (b - k) = closure_tag && k < wz_of m (b - k)
                  then assert (covers m (b - k) b)
       | None -> ())
    end

let set_field_young_ok (m: mheap) (o i: nat) (v: value)
  : Lemma (requires young_ok m) (ensures young_ok (set_field m o i v))
  = let m' = set_field m o i v in
    assert (forall (x: nat). is_block m' x == is_block m x /\ wz_of m' x == wz_of m x /\ tag_of m' x == tag_of m x);
    assert (forall (x w: nat). covers m' x w == covers m x w)
