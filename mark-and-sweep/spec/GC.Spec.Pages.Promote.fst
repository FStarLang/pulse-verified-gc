/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote - the minor collection over any allocator with a tag
/// ---------------------------------------------------------------------------
///
/// Plan §27.2.  akhil's minor collection (`GC.Gen.Promote.promote_object`,
/// `GC.Gen.Cheney.cheney_promote`, `cheney_collect_spec_with`) allocates
/// every promoted copy from his free list (`AP.alloc_at`).  This is the same
/// collection, statement for statement, with the allocation a parameter:
///
///   * `promote_object`: allocate `wz` words with the nursery object's tag
///     (`GC.Gen.Promote.promoted_tag`), then copy its fields
///     (`GC.Gen.WriteBodyLemmas.copy_fields`); on failure nothing changes;
///   * `forward_normal`, `forward_one`, `forward_fields`, `forward_roots`,
///     `scan`, `promote`: akhil's Cheney loop (`GC.Gen.Cheney`), with the
///     allocator's state in place of the free-list head;
///   * `collect`: promotion, then akhil's pointer update over the blocks in
///     use (`GC.Gen.Promote.update_pointers_with`), the roots rewritten
///     (`rewrite_roots`), the nursery reset.
///
/// The allocator is a `tal s`: its state type `s`, the invariant it keeps,
/// what counts as free, the colour of a new block at an address (the
/// first-fit allocator colours by the side of the sweep's cursor), and the
/// allocation.
/// `contract` is what the collection needs of it (plan §27.2): from the
/// invariant, an allocation either changes nothing, or returns a block that
/// was not in use, of the size, tag and colour asked, brings no other block
/// into use, leaves every block in use as it was, and leaves the invariant
/// to the caller's writes of its fields (`AT.fields_written_away`); the
/// invariant gives well-formedness, and survives akhil's pointer update.
/// The page allocator meets it while marking and while sweeping
/// (`GC.Spec.Pages.PromoteInst`).

module GC.Spec.Pages.Promote

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator
/// ---------------------------------------------------------------------------

/// An allocator with a tag, over states of type `s`.
noeq type tal (s: Type0) = {
  inv: heap -> s -> prop;
  alloc: heap -> s -> nat -> AT.tag_t -> GTot (heap & s & U64.t);
  free: free_def;
  col: U64.t -> color;
}

/// What one allocation of `wz > 0` words with tag `tag` guarantees.
let alloc_ok (#s: Type0) (a: tal s) (g: heap) (st: s) (wz: pos) (tag: AT.tag_t) : prop =
  let (g', st', o) = a.alloc g st wz tag in
  (o == 0UL ==> g' == g /\ st' == st) /\
  (o =!= 0UL ==>
     U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
     (let x : obj_addr = o in
      U64.v x + wz * 8 <= heap_size /\
      Seq.mem x (objects zero_addr g') /\
      U64.v (wosize_of_object x g') == wz /\
      tag_of_object x g' == tag /\
      color_of_object x g' == a.col o /\
      ~(in_use a.free g x) /\
      (forall (y: obj_addr). in_use a.free g' y == (in_use a.free g y || y = x)) /\
      (forall (g'': heap). AT.fields_written_away a.free g' g'' x ==> a.inv g'' st')) /\
     I.others_unchanged g g')

/// **What the minor collection needs of the allocator.**
let contract (#s: Type0) (a: tal s) : prop =
  free_def_ok a.free /\
  (forall (g: heap) (st: s). a.inv g st ==> well_formed_heap_with a.free g) /\
  (forall (g: heap) (st: s) (wz: pos) (tag: AT.tag_t).
     a.inv g st /\ U64.v tag <> 249 ==> alloc_ok a g st wz tag) /\
  (forall (g: heap) (st: s) (upd: obj_addr -> GTot bool) (fwd: forwarding_map).
     a.inv g st /\ walk_ok g upd /\ well_formed_heap_with a.free (update_walk g upd fwd) ==>
     a.inv (update_walk g upd fwd) st)

let contract_wf (#s: Type0) (a: tal s) (g: heap) (st: s)
  : Lemma (requires contract a /\ a.inv g st)
          (ensures free_def_ok a.free /\ well_formed_heap_with a.free g)
  = ()

let contract_alloc (#s: Type0) (a: tal s) (g: heap) (st: s) (wz: pos) (tag: AT.tag_t)
  : Lemma (requires contract a /\ a.inv g st /\ U64.v tag <> 249)
          (ensures alloc_ok a g st wz tag)
  = ()

let contract_update (#s: Type0) (a: tal s) (g: heap) (st: s) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
  : Lemma (requires contract a /\ a.inv g st /\ walk_ok g upd /\
                    well_formed_heap_with a.free (update_walk g upd fwd))
          (ensures a.inv (update_walk g upd fwd) st)
  = ()

/// ---------------------------------------------------------------------------
/// Promoting one object (akhil's `promote_object`)
/// ---------------------------------------------------------------------------

/// Allocate with the nursery object's wosize and tag, then copy its fields;
/// on failure nothing changes.
let promote_object (#s: Type0) (a: tal s) (minor: minor_state) (major: heap) (obj: U64.t)
                   (st: s) (wz: nat{wz > 0})
  : GTot (heap & s & U64.t) =
  let (g1, s1, o) = a.alloc major st wz (promoted_tag minor obj) in
  if o = 0UL then (major, st, 0UL)
  else (copy_fields minor g1 obj o 0 wz, s1, o)

/// ---------------------------------------------------------------------------
/// The Cheney loop (akhil's `GC.Gen.Cheney`)
/// ---------------------------------------------------------------------------

/// The loop's state: the major heap, the allocator's state, the forwarding
/// map, the queue of forwarded nursery objects.
noeq type gstate (s: Type0) = {
  major: heap;
  st: s;
  fwd: forwarding_map;
  queue: seq U64.t;
}

/// Forward a nursery object that is not infix: promote it and queue it.
let forward_normal (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : GTot (gstate s) =
  if not (Seq.mem addr (minor_objects minor)) || cs.fwd addr <> 0UL then cs
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then cs
    else
      let (g', s', o) = promote_object a minor cs.major addr cs.st wz in
      if o = 0UL then cs
      else { major = g'; st = s'; fwd = extend_forwarding cs.fwd addr o;
             queue = Seq.append cs.queue (Seq.create 1 addr) }

/// Forward an address: an infix one through its parent closure.
let forward_one (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (addr: U64.t)
  : GTot (gstate s) =
  if cs.fwd addr <> 0UL then cs
  else if is_infix_in_minor minor addr then
    let parent = infix_parent minor addr in
    let cs' = forward_normal a minor cs parent in
    if cs'.fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      let delta = U64.v addr - U64.v parent in
      { cs' with fwd = extend_forwarding cs'.fwd addr (U64.uint_to_t (U64.v (cs'.fwd parent) + delta)) }
    else cs'
  else forward_normal a minor cs addr

/// Forward the children in fields `idx ..` of `parent`.
let rec forward_fields (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s)
                       (parent: U64.t) (idx: nat) (wz: nat)
  : GTot (gstate s) (decreases (if idx >= wz then 0 else wz - idx)) =
  if idx >= wz then cs
  else
    let fv = to_minor_offset (minor_read_field minor parent idx) in
    forward_fields a minor (forward_one a minor cs fv) parent (idx + 1) wz

/// Forward the roots `idx ..`.
let rec forward_roots (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s)
                      (roots: seq U64.t) (idx: nat)
  : GTot (gstate s) (decreases (if idx >= Seq.length roots then 0 else Seq.length roots - idx)) =
  if idx >= Seq.length roots then cs
  else forward_roots a minor (forward_one a minor cs (Seq.index roots idx)) roots (idx + 1)

/// Scan the queue from `sc`.
let rec scan (#s: Type0) (a: tal s) (minor: minor_state) (cs: gstate s) (sc: nat) (fuel: nat)
  : GTot (gstate s) (decreases fuel) =
  if fuel = 0 || sc >= Seq.length cs.queue then cs
  else
    let obj = Seq.index cs.queue sc in
    let cs' = forward_fields a minor cs obj 0 (minor_scan_wosize minor obj) in
    scan a minor cs' (sc + 1) (fuel - 1)

/// **Promotion**: forward the roots, then scan.
let promote (#s: Type0) (a: tal s) (minor: minor_state) (major: heap) (st: s) (roots: seq U64.t)
  : GTot (gstate s) =
  let cs0 = { major = major; st = st; fwd = empty_forwarding; queue = Seq.empty } in
  let cs1 = forward_roots a minor cs0 roots 0 in
  scan a minor cs1 0 (Seq.length (minor_objects minor))

/// The result of a minor collection.
noeq type gresult (s: Type0) = {
  rmajor: heap;
  rst: s;
  rminor: minor_state;
  rroots: seq U64.t;
  rfwd: forwarding_map;
}

/// **The minor collection**: promotion, akhil's pointer update over the
/// blocks in use, the roots rewritten, the nursery reset.
let collect (#s: Type0) (a: tal s) (minor: minor_state) (major: heap) (st: s) (roots: seq U64.t)
  : GTot (gresult s) =
  let cs = promote a minor major st roots in
  { rmajor = update_pointers_with a.free cs.major cs.fwd;
    rst = cs.st;
    rminor = minor_reset minor;
    rroots = rewrite_roots roots cs.fwd;
    rfwd = cs.fwd }
