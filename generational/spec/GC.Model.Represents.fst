/// ---------------------------------------------------------------------------
/// GC.Model.Represents - the real memory represents the ideal one
/// ---------------------------------------------------------------------------
///
/// The relation between the real execution (`GC.Gen.Run.Step`) and the
/// ideal one (`GC.Model.Ideal`).
/// It lives with the generational spec because the real memory is the
/// nursery and the major heap.
///
/// `allocated_block_id` (a `block_id_map`) names, for each allocated block of
/// the real memory, the ideal object it holds: `Some id` exactly at the
/// allocated blocks (`keyed`), and injective.  It exists only in the proof.
/// It starts empty and changes one event at a time (`update_block_ids`,
/// the plan's table): an allocation adds its new block with the next id; a
/// minor collection moves a live nursery block's entry to its promoted copy
/// (the forwarding map) and drops the dead ones; every other event drops the
/// entries of blocks that stopped being allocated (a sweep slice's freed
/// blocks) and keeps the rest.  Along a run it is `ids_along`; from the
/// initial state, `ids_of_run`.
///
/// `represents r h ideal ids` holds when
///   1. **`covers_reachable`**: every object reachable in the ideal memory is
///      the id of some block;
///   2. **`copies_faithful`**: a block with an id has that object's tag and
///      size, and, if it is a nursery block or a kept major block
///      (`faithful_block`: the snapshot and what was allocated since), its
///      fields hold the object's fields translated: a word is itself, a
///      pointer `Ptr { head; k }` is the address of `head`'s block plus `k`
///      words (`value_rep`), a no-scan word is itself.  A major block that was
///      garbage when the cycle started is only required to keep its tag and
///      size: the sweep may free what it points at before freeing it, so its
///      fields may name blocks that are gone.  This loses nothing: the
///      blocks of reachable objects are kept (`Simulation.reachable_in_kept`),
///      kept blocks and the nursery point only at kept blocks (B1), and idle
///      every allocated major block is kept;
///   3. **`retains_snapshot`**: when the collector is idle, the major heap's
///      blocks with an id are exactly the cycle's snapshot and the blocks
///      allocated since (`GC.Gen.Run.History.kept`): the memory half.
/// and `ids` is `keyed`.  The plan's clause 3, **`roots_represented`** (the
/// roots handed to `minor_collect` and `start_cycle` are the ideal roots,
/// translated), is a property of those calls, not of a state: it is defined
/// here and assumed at those two calls only (trusted).
///
/// `translates ids e pe`: the real program event `e` is the ideal `pe` with
/// its objects and values translated by `ids`.  This is how compiled code
/// carries out the program (trusted boundary).

module GC.Model.Represents

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Run.Step
open GC.Gen.Run.History

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal
module ID = FStar.IndefiniteDescription
module Promote = GC.Gen.Promote

/// ---------------------------------------------------------------------------
/// The map from blocks to ideal objects
/// ---------------------------------------------------------------------------

/// An `allocated_block_id`: the ideal object each block holds, if any.
let block_id_map = block_addr -> GTot (option I.obj_id)

/// Nothing allocated.
let empty_ids : block_id_map = fun _ -> None

/// `Some` exactly at the allocated blocks, and injective.
let keyed (m: real_memory) (ids: block_id_map) : prop =
  (forall (b: block_addr). Some? (ids b) <==> is_allocated m b) /\
  (forall (b1 b2: block_addr). Some? (ids b1) /\ ids b1 == ids b2 ==> b1 == b2)

/// The derived inverse: the block holding `id`, if any.
let block_of (ids: block_id_map) (id: I.obj_id) : GTot (option block_addr) =
  if ID.strong_excluded_middle (exists (b: block_addr). ids b == Some id)
  then Some (ID.indefinite_description_ghost block_addr (fun b -> ids b == Some id))
  else None

/// ---------------------------------------------------------------------------
/// Translating values
/// ---------------------------------------------------------------------------

/// The word `w` holds the value `v`: a word is itself; a pointer to `head`,
/// `k` words in, is the address of `head`'s block plus `k` words.
///
/// **A word lies outside both heaps** (`outside_heaps`): it is neither a
/// major-heap pointer (`is_pointer_field`) nor a nursery address
/// (`is_young`).  Trusted, as part of the boundary (`translates`,
/// `roots_represented`): an OCaml integer is tagged (odd), and static data
/// and code pointers lie outside both heaps.  (Otherwise the collector would
/// treat the word as a pointer: mark through it, or rewrite it when it
/// promotes what it seems to point at.)
let outside_heaps (w: U64.t) : prop =
  ~(GC.Spec.Fields.is_pointer_field w) /\ ~(is_young w)

let value_rep (ids: block_id_map) (v: I.value) (w: U64.t) : prop =
  match v with
  | I.Word w' -> w == w' /\ outside_heaps w'
  | I.Ptr { head; infix_offset } -> exists (b: block_addr). ids b == Some head /\ w == ptr_value b infix_offset

/// The word `w` holds the field content `c` (a raw word is itself).
let content_rep (ids: block_id_map) (c: I.field_content) (w: U64.t) : prop =
  match c with
  | I.FValue v -> value_rep ids v w
  | I.FRaw w' -> w == w'

/// The words `ws` hold the fields `f`.
let fields_rep (ids: block_id_map) (f: I.ideal_fields) (ws: seq U64.t) : prop =
  Seq.length ws == I.fields_length f /\
  (match f with
   | I.Scannable vs -> forall (i: nat). i < Seq.length vs ==> value_rep ids (Seq.index vs i) (Seq.index ws i)
   | I.NoScan ws' -> forall (i: nat). i < Seq.length ws' ==> Seq.index ws i == Seq.index ws' i)

/// The block `b` has the tag and size of the object `o`.
let block_header_rep (m: real_memory) (b: block_addr) (o: I.ideal_object) : prop =
  block_tag m b == U64.v o.I.tag /\ block_size m b == o.I.size

/// The block `b` holds the object `o`: same tag, same size, fields
/// translated.
let block_rep (m: real_memory) (ids: block_id_map) (b: block_addr) (o: I.ideal_object) : prop =
  block_tag m b == U64.v o.I.tag /\ block_size m b == o.I.size /\
  (forall (i: nat). i < o.I.size ==> content_rep ids (I.field_at o i) (block_field m b i))

/// The pointers among the values `vs`, in order: what the collector is
/// handed of the program's roots (the runtime's root scan records only the
/// roots that are blocks; an integer root is never passed).
let rec ptr_values (vs: seq I.value) : Tot (seq I.value) (decreases Seq.length vs) =
  if Seq.length vs = 0 then Seq.empty
  else
    let rest = ptr_values (Seq.tail vs) in
    if I.Ptr? (Seq.head vs) then Seq.cons (Seq.head vs) rest else rest

/// **The values `vs`, translated, are the words `rs`.**
let roots_represented (ids: block_id_map) (vs: seq I.value) (rs: seq U64.t) : prop =
  Seq.length rs == Seq.length vs /\
  (forall (i: nat). i < Seq.length vs ==> value_rep ids (Seq.index vs i) (Seq.index rs i))

/// ---------------------------------------------------------------------------
/// The clauses
/// ---------------------------------------------------------------------------

/// 1. Every reachable ideal object is held by some block.
let covers_reachable (im: I.ideal_memory) (ids: block_id_map) : prop =
  forall (id: I.obj_id). I.reachable im id ==> (exists (b: block_addr). ids b == Some id)

/// The blocks whose fields must be faithful: the nursery's, and the kept
/// major blocks.
let faithful_block (h: cycle_history) (b: block_addr) : prop =
  match b with
  | Major x -> kept h x
  | Nursery _ -> True

/// 2. A block with an id has that object's tag and size, and, if it is a
/// nursery block or kept, holds a faithful copy of it.
let copies_faithful (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) : prop =
  forall (b: block_addr) (id: I.obj_id).
    ids b == Some id ==>
      I.valid_id im id /\ block_header_rep m b (Seq.index im.I.objects id) /\
      (faithful_block h b ==> block_rep m ids b (Seq.index im.I.objects id))

/// 4. Idle, the major blocks with an id are exactly the snapshot and what was
/// allocated since.
let retains_snapshot (r: real_state) (h: cycle_history) (ids: block_id_map) : prop =
  r.phase == Ph.Idle ==> (forall (x: obj_addr). Some? (ids (Major x)) <==> kept h x)

/// **The real state represents the ideal memory**, through `ids`, relative
/// to the cycle's history `h`.
let represents (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) : prop =
  keyed r.memory ids /\ copies_faithful r.memory h im ids /\ covers_reachable im ids /\
  retains_snapshot r h ids

/// ---------------------------------------------------------------------------
/// The real events that carry out the program's
/// ---------------------------------------------------------------------------

/// **`e` carries out `pe`** in the real memory `m`: the same event with the
/// objects and values translated by `ids` (the allocation site is the
/// runtime's choice).  A write into a no-scan block stores the word itself
/// (raw bytes, a float), as an allocation's no-scan fields do
/// (`fields_rep`); into a scannable block, the value translated
/// (`value_rep`).  Where the word of a pointer to a nursery block lies (an
/// offset in the nursery, not a major-heap address) is not part of this:
/// it follows from `value_rep`, the map being injective (`ids_injective_on_allocated`) and the nursery's
/// shape (`GC.Gen.Run.Simulation.Enabled.word_layout_holds`).
let translates (m: real_memory) (ids: block_id_map) (e: event) (pe: I.program_event) : prop =
  match e, pe with
  | Alloc _ tag size init, I.Alloc tag' size' f ->
      tag == tag' /\ size == size' /\ fields_rep ids f init
  | Write b i v, I.Write obj i' v' ->
      ids b == Some obj /\ i == i' /\
      (if block_tag m b < 251 then value_rep ids v' v
       else (match v' with I.Word w -> v == w | I.Ptr _ -> False))
  | Read b i, I.Read obj i' -> ids b == Some obj /\ i == i'
  | SetRoots rs, I.SetRoots vs -> roots_represented ids vs rs
  | _, _ -> False

/// The collector calls that take roots take the ideal roots that are
/// pointers, translated (`ptr_values`: integer roots are not passed).
let collector_roots_represented (ids: block_id_map) (vs: seq I.value) (e: event) : prop =
  match e with
  | Minor rs | StartCycle rs -> roots_represented ids (ptr_values vs) rs
  | _ -> True

/// ---------------------------------------------------------------------------
/// How the map follows a step
/// ---------------------------------------------------------------------------

/// Keep the entries of the blocks still allocated in `m`.
let restrict (m: real_memory) (ids: block_id_map) (b: block_addr) : GTot (option I.obj_id) =
  if ID.strong_excluded_middle (is_allocated m b) then ids b else None

/// An allocation: the new block gets `next`.
let with_new_block (r r': real_state) (ids: block_id_map) (next: I.obj_id) (b: block_addr)
  : GTot (option I.obj_id) =
  if ID.strong_excluded_middle (is_allocated r'.memory b /\ ~(is_allocated r.memory b)) then Some next
  else restrict r'.memory ids b

/// A nursery object of `r` forwarded to `x` by `fwd`.
let forwarded_to (r: real_state) (fwd: Promote.forwarding_map) (x: obj_addr) (o: U64.t) : prop =
  is_allocated r.memory (Nursery o) /\ fwd o == (x <: U64.t)

/// A minor collection: a promoted copy takes its original's entry; the
/// nursery's entries go; the other major blocks keep theirs.
let forwarded (r r': real_state) (fwd: Promote.forwarding_map) (ids: block_id_map) (b: block_addr)
  : GTot (option I.obj_id) =
  match b with
  | Nursery _ -> None
  | Major x ->
      if ID.strong_excluded_middle (exists (o: U64.t). forwarded_to r fwd x o)
      then ids (Nursery (ID.indefinite_description_ghost U64.t (forwarded_to r fwd x)))
      else restrict r'.memory ids b

/// **The map after a step** from `r` to `r'` over `e`, `next` the id the
/// next allocation gets (the plan's table).
let update_block_ids (ids: block_id_map) (next: I.obj_id) (r: real_state) (e: event) (r': real_state)
  : block_id_map =
  match e with
  | Alloc _ _ _ _ -> with_new_block r r' ids next
  | Minor roots -> forwarded r r' (minor_result r roots).Promote.mc_fwd ids
  | _ -> restrict r'.memory ids

/// The map along a run, from `ids0` with `n0` objects already allocated.
let rec ids_along (ids0: block_id_map) (n0: nat) (#r0: real_state) (#es: list event) (#r1: real_state)
                  (rn: run r0 es r1)
  : GTot block_id_map (decreases rn) =
  match rn with
  | Done _ -> ids0
  | Step #_ #es' #r1' rn' e r2 _ ->
      update_block_ids (ids_along ids0 n0 rn') (n0 + alloc_count es') r1' e r2

/// The map of a run from the initial state.
let ids_of_run (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r) : GTot block_id_map =
  ids_along empty_ids 0 rn
