/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Step - the real execution: its state, its events, its runs
/// ---------------------------------------------------------------------------
///
/// The real execution of the program on our runtime, one event at a time.
///
///   * **The state** (`real_state`): the memory -- the nursery and the major
///     heap -- and the collector's bookkeeping: the free list, the phase, the
///     mark slice's scan position, and the remembered set (`ref_table`: the
///     major-heap slots that may hold nursery pointers).  It is what
///     `GC.Gen.Impl.gc_state` describes.  The roots are the program's; the
///     collector sees them only at the calls that take them.
///   * **The events** (`event`): the program's -- an allocation with every
///     initialising write, in the nursery or the major heap (`Alloc`, the
///     runtime's choice is part of the event), a field write, a read, a new
///     set of roots -- and the collector's: a minor collection, the start of a
///     major cycle, a major slice.  `full_gc` is the composite of these
///     (`full_gc_events`), not an event of its own.  A program event here is
///     *real*: its fields hold machine words; how it corresponds to the
///     program's abstract event is `GC.Model.Represents.translates`.
///   * **A step** (`step r e r'`) is a relation: from `r`, the event `e` can
///     lead to `r'`.  It holds only where the event is legal (its
///     precondition: the precondition of the Pulse contract, or for the
///     program's events the obligation the runtime owes), and then relates the
///     state to the states the event may leave:
///       - **major allocation** is relational (`major_alloc_step`): a block at
///         *some* address that (1) was free memory, (2) is afterwards a block
///         of the requested tag, size and initial fields, (3) leaves every
///         other block unchanged, and (4) leaves the collector's state
///         (`GI.phase_shape`, the colour the phase gives a new object).  The
///         allocator's policy is not part of it; that `alloc_phase` meets it
///         is `GC.Gen.Run.Invariant.alloc_phase_major_alloc_step`;
///       - **nursery allocation** and **nursery writes** are modelled steps
///         (the trusted boundary: compiled code bumps the nursery pointer and
///         stores into young objects without a barrier);
///       - **a major write** into a scannable block is the barrier
///         (`GB.modify_heap`, darkening the old value while marking) with the
///         slot remembered when `GB.modify_records` says so; into a no-scan
///         block it is a raw store;
///       - **the collector's events** are the specs the Pulse contracts
///         state: `Cheney.cheney_collect_spec_with` at the phase (with the
///         remembered slots' targets among the roots, as the bridge passes
///         them), `MStart.darkened`, `GI.major_slice_post`.
///   * **A run** (`run r0 es r1`) is a sequence of steps from `r0` over the
///     events `es` to `r1`.  The legal interleavings are exactly the runs.

module GC.Gen.Run.Step

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module SPI = GC.Spec.SweepPhase.Intrinsic
module SPM = GC.Spec.SweepPhase.Mutator
module SA = GC.Spec.Allocator
module GI = GC.Gen.Incremental
module GB = GC.Gen.Barrier
module GBase = GC.Gen.Base
module GMM = GC.Gen.MarkPhase.Minor
module MStart = GC.Gen.MarkPhase.Start
module MBP = GC.Impl.MarkBoundedPrecondition
module Cheney = GC.Gen.Cheney
module CheneyBFS = GC.Gen.CheneyBFS
module MinorFwd = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module Promote = GC.Gen.Promote
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module GenInv = GC.Gen.HeapInvariant
module I = GC.Model.Ideal
module Header = GC.Lib.Header

/// ---------------------------------------------------------------------------
/// The state
/// ---------------------------------------------------------------------------

/// The real memory: the nursery and the major heap.
noeq type real_memory = {
  nursery: minor_state;
  major: heap;
}

/// **The real state**: the memory and the collector's bookkeeping.
noeq type real_state = {
  memory: real_memory;
  free_list: U64.t;          // the major heap's free-list head
  phase: Ph.gc_phase;
  scan_pos: MP.scan_pos;     // the mark slice's position (matters only while marking)
  ref_table: seq U64.t;      // the remembered set, `caml_ref_table`
}

/// ---------------------------------------------------------------------------
/// Blocks of the real memory
/// ---------------------------------------------------------------------------

/// A block of the real memory, by its object address: a major-heap object
/// address, or a nursery object's offset.
type block_addr =
  | Major : obj_addr -> block_addr
  | Nursery : U64.t -> block_addr

/// **An allocated block**: one holding an object, live or dead.  In the
/// major heap, a block of the walk that is not blue -- the stop-the-world
/// sense, whatever the phase counts as free; in the nursery, an object
/// below the bump pointer.
let is_allocated (m: real_memory) (b: block_addr) : prop =
  match b with
  | Major x -> Seq.mem x (objects zero_addr m.major) /\ ~(is_blue x m.major)
  | Nursery o -> Seq.mem o (minor_objects m.nursery)

/// Its tag, its size, and its `i`-th field.
let block_tag (m: real_memory) (b: block_addr) : GTot nat =
  match b with
  | Major x -> U64.v (tag_of_object x m.major)
  | Nursery o -> minor_tag m.nursery o

let block_size (m: real_memory) (b: block_addr) : GTot nat =
  match b with
  | Major x -> U64.v (wosize_of_object x m.major)
  | Nursery o -> minor_wosize m.nursery o

/// The `i`-th field of the major object `x`.
let major_field (g: heap) (x: obj_addr) (i: nat) : GTot U64.t =
  let p = U64.v x + i * 8 in
  if p + 8 <= heap_size then read_word g (U64.uint_to_t p) else 0UL

let block_field (m: real_memory) (b: block_addr) (i: nat) : GTot U64.t =
  match b with
  | Major x -> major_field m.major x i
  | Nursery o -> minor_read_field m.nursery o i

/// The word a pointer to `b`, `k` words in, holds: the object address in
/// the major heap; the nursery's base address plus the offset in the
/// nursery (`GC.Gen.Base.to_minor_offset` is its inverse).
let ptr_value (b: block_addr) (k: nat) : U64.t =
  match b with
  | Major x -> U64.uint_to_t ((U64.v x + 8 * k) % pow2 64)
  | Nursery o -> U64.add_mod GBase.minor_base_addr (U64.uint_to_t ((U64.v o + 8 * k) % pow2 64))

/// The slot of field `i` of `x` in the major heap, and of `o` in the nursery.
let major_slot (x: obj_addr) (i: nat) : U64.t = U64.uint_to_t ((U64.v x + 8 * i) % pow2 64)
let nursery_slot (o: U64.t) (i: nat) : U64.t = U64.uint_to_t ((U64.v o + 8 * i) % pow2 64)

/// ---------------------------------------------------------------------------
/// Events
/// ---------------------------------------------------------------------------

/// Where an allocation happens: the runtime's choice.
type alloc_site =
  | InNursery
  | InMajor

/// **The real events.**  The program's: `Alloc site tag size init` (the
/// allocation and every initialising write), `Write b i v`, `Read b i`,
/// `SetRoots rs`; the collector's: `Minor rs` and `StartCycle rs` (with the
/// program's roots `rs`), `Slice budget`.
noeq type event =
  | Alloc : site: alloc_site -> tag: I.tag_t -> size: nat -> init: seq U64.t -> event
  | Write : target: block_addr -> field: nat -> v: U64.t -> event
  | Read : target: block_addr -> field: nat -> event
  | SetRoots : roots: seq U64.t -> event
  | Minor : roots: seq U64.t -> event
  | StartCycle : roots: seq U64.t -> event
  | Slice : budget: nat -> event

let is_program_event (e: event) : bool =
  Alloc? e || Write? e || Read? e || SetRoots? e

/// The budget `full_gc` and the bridge pass to finish a phase
/// (`UINT64_MAX`; `GI.unbounded`).
let unbounded_budget : nat = pow2 64 - 1

/// `full_gc` as events: a minor collection from the roots `rs`, the start of
/// a cycle from the rewritten roots `rs'`, and two unbounded slices (marking
/// to the end, then the sweep to the end).
let full_gc_events (rs rs': seq U64.t) : list event =
  [Minor rs; StartCycle rs'; Slice unbounded_budget; Slice unbounded_budget]

/// ---------------------------------------------------------------------------
/// What the program owes when it stores a value
/// ---------------------------------------------------------------------------

/// Whether `v` is a nursery pointer (4.14's `Is_young`).
let is_young (v: U64.t) : GTot bool = GB.is_young v

/// **A value the program may store** in the state `r`: a major pointer
/// points (resolved) at a block not free at the phase; a nursery pointer at
/// an object of the nursery; and while marking, a white target is one the
/// marker will reach (the program holds it: the roots obligation).  These
/// are obligations of the runtime today; for the program's events they
/// follow from the program's well-formedness and `represents`
/// (`GC.Gen.Run.Simulation.program_step_enabled`).
let storable_value (r: real_state) (v: U64.t) : prop =
  SPI.storable (GI.phase_free r.phase) r.memory.major v /\
  (is_young v ==>
     Seq.mem (resolve_minor r.memory.nursery (GBase.to_minor_offset v)) (minor_objects r.memory.nursery)) /\
  (Ph.Marking? r.phase ==> MM.target_ok r.memory.major (fun _ -> False) r.scan_pos v)

/// The initial words of a new object: storable, if the tag is scannable.
let init_storable (r: real_state) (tag: I.tag_t) (init: seq U64.t) : prop =
  I.tag_scannable tag ==> (forall (i: nat). i < Seq.length init ==> storable_value r (Seq.index init i))

/// ---------------------------------------------------------------------------
/// Program steps
/// ---------------------------------------------------------------------------

/// The slots of the new major object `a` whose initial value is young: what
/// `caml_initialize` appends to the remembered set.
let rec young_slots_from (a: obj_addr) (init: seq U64.t) (i: nat)
  : GTot (seq U64.t) (decreases (Seq.length init - i)) =
  if i >= Seq.length init then Seq.empty
  else let rest = young_slots_from a init (i + 1) in
       if is_young (Seq.index init i) then Seq.cons (major_slot a i) rest else rest

let young_slots (a: obj_addr) (init: seq U64.t) : GTot (seq U64.t) = young_slots_from a init 0

/// Every word of `a`'s block in `g'` was in a free (blue) block of `g`.
let was_free (g g': heap) (a: obj_addr) : prop =
  forall (p: nat). LL.in_extent g' a p ==> LL.blue_covered g p

/// A block keeps its header and its fields.
let same_block (g g': heap) (x: obj_addr) : prop =
  read_word g' (hd_address x) == read_word g (hd_address x) /\
  (forall (i: nat). i < U64.v (wosize_of_object x g) ==>
     major_field g' x i == major_field g x i)

/// **Direct major allocation, relational** (properties (1)-(4)): the new block is at some address `a` such that
///   (1) its words were free memory;
///   (2) afterwards it is an allocated block of the requested tag and size,
///       with the initial fields, and the colour the phase gives it;
///   (3) every other block is unchanged, and no other block became or
///       stopped being allocated;
///   (4) the collector's state holds afterwards (`GI.phase_shape`).
/// The nursery, phase and scan position are untouched; for a scannable tag
/// the slots of the young initial values are appended to the remembered set
/// (`caml_initialize`; a no-scan block's words are raw, and
/// `caml_alloc_string` remembers nothing); the walk ends where it did.  The
/// free list afterwards is any that (4) admits.
let major_alloc_step (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state) : prop =
  size >= 1 /\ Seq.length init == size /\ tag <> infix_tag /\ init_storable r tag init /\
  r'.memory.nursery == r.memory.nursery /\ r'.phase == r.phase /\ r'.scan_pos == r.scan_pos /\
  (exists (a: obj_addr).
     // (1)
     was_free r.memory.major r'.memory.major a /\
     // (2)
     is_allocated r'.memory (Major a) /\
     tag_of_object a r'.memory.major == tag /\ U64.v (wosize_of_object a r'.memory.major) == size /\
     color_of_object a r'.memory.major == Ph.allocation_color r.phase (hd_address a) /\
     (forall (i: nat). i < size ==> block_field r'.memory (Major a) i == Seq.index init i) /\
     // (3)
     (forall (x: obj_addr). x <> a ==>
        (is_allocated r.memory (Major x) <==> is_allocated r'.memory (Major x)) /\
        (is_allocated r.memory (Major x) ==> same_block r.memory.major r'.memory.major x)) /\
     r'.ref_table == (if I.tag_scannable tag then Seq.append r.ref_table (young_slots a init)
                      else r.ref_table)) /\
  // the walk ends where it did (the new block is carved out of free memory)
  W.walk_end r'.memory.major zero_addr == W.walk_end r.memory.major zero_addr /\
  // (4)
  GI.phase_shape r'.memory.nursery r'.memory.major r'.free_list r'.phase r'.scan_pos

/// ---------------------------------------------------------------------------
/// The nursery after a program store (trusted)
/// ---------------------------------------------------------------------------

/// **A value the program may store into the nursery**: a storable value
/// (`storable_value`).  A major pointer may be an interior (infix) pointer, to
/// one of several mutually recursive closures, as real OCaml stores into a
/// young object: the nursery clauses of `GC.Gen.HeapInvariant`
/// (`minor_major_fields_not_free`, `minor_major_fields_no_blue`) are stated on
/// the resolved target, exactly as `storable_value` is (Phase H.4 of
/// `docs/minor-infix-support-plan.md`).
let nursery_storable (r: real_state) (v: U64.t) : prop =
  storable_value r v

/// What a store of `v` into field `i` of the nursery object `o` leaves: the
/// nursery keeps its shape (`GenInv.minor_heap_shape`), its objects, their
/// headers, and every other field.  The shape is the **trusted mutator
/// obligation** of `GC.Gen.MinorHeap` (a stored word must not read as a
/// nursery header, which the guards and infix clauses of the shape forbid
/// for anything that is not an object); the rest is what a body store does.
let nursery_store_frame (ms ms': minor_state) (o: U64.t) (i: nat) (v: U64.t) : prop =
  GenInv.minor_heap_shape ms' /\
  minor_objects ms' == minor_objects ms /\
  (forall (y: U64.t). Seq.mem y (minor_objects ms) ==>
     minor_wosize ms' y == minor_wosize ms y /\ minor_tag ms' y == minor_tag ms y /\
     (forall (j: nat). j < minor_wosize ms y ==>
        minor_read_field ms' y j == (if y = o && j = i then v else minor_read_field ms y j)))

/// What a nursery allocation of `a` with tag `tag` and fields `init` leaves:
/// the shape (trusted, as above), the objects and `a`, `a`'s header and
/// fields, and every other object's header and fields.
let nursery_alloc_frame (ms ms': minor_state) (a: U64.t) (tag: nat) (init: seq U64.t) : prop =
  GenInv.minor_heap_shape ms' /\
  (forall (y: U64.t). Seq.mem y (minor_objects ms') <==> Seq.mem y (minor_objects ms) \/ y == a) /\
  minor_tag ms' a == tag /\ minor_wosize ms' a == Seq.length init /\
  (forall (j: nat). j < Seq.length init ==> minor_read_field ms' a j == Seq.index init j) /\
  (forall (y: U64.t). Seq.mem y (minor_objects ms) ==>
     y <> a /\ minor_wosize ms' y == minor_wosize ms y /\ minor_tag ms' y == minor_tag ms y /\
     (forall (j: nat). j < minor_wosize ms y ==> minor_read_field ms' y j == minor_read_field ms y j))

/// Write the initial words of the nursery object `o`.
let rec write_nursery_fields (d: GBase.minor_heap) (o: U64.t) (init: seq U64.t) (i: nat)
  : Tot GBase.minor_heap (decreases (Seq.length init - i)) =
  if i >= Seq.length init then d
  else write_nursery_fields (minor_write_word_t d (nursery_slot o i) (Seq.index init i)) o init (i + 1)

/// **Nursery allocation** (modelled): bump-allocate (`minor_alloc_spec`),
/// then write the initial words.  The object must fit in the nursery (no
/// out of memory: a full nursery is a minor collection first).  The initial
/// values, if the tag is scannable, are ones the program may store into the
/// nursery (`nursery_storable`), and the nursery after is the frame
/// (`nursery_alloc_frame`, the trusted shape).
let nursery_alloc_step (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) (r': real_state) : prop =
  size >= 1 /\ size <= GBase.max_young_wosize /\ U64.v tag <> 249 /\
  Seq.length init == size /\ init_storable r tag init /\
  (I.tag_scannable tag ==> (forall (j: nat). j < Seq.length init ==> nursery_storable r (Seq.index init j))) /\
  minor_can_alloc r.memory.nursery size /\
  (let res = minor_alloc_spec r.memory.nursery size (U64.v tag) in
   r' == { r with memory = { r.memory with nursery =
             { res.ms_out with data = write_nursery_fields res.ms_out.data res.obj_addr init 0 } } } /\
   nursery_alloc_frame r.memory.nursery r'.memory.nursery res.obj_addr (U64.v tag) init)

/// **A major write**: into a scannable block, `caml_modify` -- what the
/// program owes (`GB.modify_ok`, with a young value naming a nursery
/// object), then the barrier (`GB.modify_heap`) and the slot remembered when
/// `GB.modify_records` says so; into a no-scan block, a raw store into the
/// body of a block not free at the phase.
let major_write_step (r: real_state) (x: obj_addr) (i: nat) (v: U64.t) (r': real_state) : prop =
  let g = r.memory.major in
  exists (a: hp_addr). U64.v a == U64.v x + 8 * i /\
    (if scannable g x then
       GB.modify_ok r.phase r.memory.nursery g r.scan_pos x a v /\
       (is_young v ==> storable_value r v) /\
       r' == { r with memory = { r.memory with major = GB.modify_heap r.phase g a v };
                      ref_table = if GB.modify_records g a v then Seq.snoc r.ref_table (a <: U64.t)
                                  else r.ref_table }
     else
       in_use (GI.phase_free r.phase) g x /\ SPM.in_body g x a /\
       r' == { r with memory = { r.memory with major = write_word g a v } })

/// **A nursery write** (modelled): a plain store into field `i` of a
/// nursery object that is not a closure; the value is one the program may
/// store into the nursery (`nursery_storable`), if the object is scannable;
/// the nursery after is the frame (`nursery_store_frame`, the trusted shape).
let nursery_write_step (r: real_state) (o: U64.t) (i: nat) (v: U64.t) (r': real_state) : prop =
  let ms = r.memory.nursery in
  Seq.mem o (minor_objects ms) /\ i < minor_wosize ms o /\ minor_tag ms o <> 247 /\
  (minor_tag ms o < 251 ==> nursery_storable r v) /\
  r' == { r with memory = { r.memory with nursery =
            { ms with data = minor_write_word_t ms.data (nursery_slot o i) v } } } /\
  nursery_store_frame ms r'.memory.nursery o i v

/// ---------------------------------------------------------------------------
/// Collector steps
/// ---------------------------------------------------------------------------

/// The roots the minor collection is handed: the program's, and the targets
/// of the remembered slots (the bridge passes both, as 4.14 scans the ref
/// table).
let collector_roots (r: real_state) (roots: seq U64.t) : GTot (seq U64.t) =
  Seq.append roots (MCFH.remembered_slot_targets r.memory.major r.ref_table (Seq.length r.ref_table))

/// The minor collection's result, at the phase (`Cheney.cheney_collect_spec_with`).
let minor_result (r: real_state) (roots: seq U64.t) : GTot Promote.minor_collect_result =
  Cheney.cheney_collect_spec_with r.phase (GI.phase_free r.phase)
    r.memory.nursery r.memory.major r.free_list (collector_roots r roots)

/// **A minor collection** from the program's roots: they are valid and not
/// free (`MinorFwd.roots_valid_with`); while marking, the white ones are
/// ones the marker will reach; promotion does not run out of memory.  The
/// nursery is emptied, the remembered set too.
let minor_step (r: real_state) (roots: seq U64.t) (r': real_state) : prop =
  let rs = collector_roots r roots in
  MinorFwd.roots_valid_with (GI.phase_free r.phase) r.memory.nursery r.memory.major rs /\
  (Ph.Marking? r.phase ==> MP.outside_refs_reached r.memory.major r.scan_pos (GMM.root_refs r.memory.major rs)) /\
  CheneyBFS.cheney_no_oom r.phase r.memory.nursery r.memory.major r.free_list rs /\
  (let res = minor_result r roots in
   r' == { memory = { nursery = res.Promote.mc_minor; major = res.Promote.mc_major };
           free_list = res.Promote.mc_fp; phase = r.phase; scan_pos = r.scan_pos;
           ref_table = Seq.empty })

/// **The start of a cycle**: idle, the nursery empty (right after a minor
/// collection), every root a darkenable object; the roots are darkened and
/// the collector is marking.
let start_step (r: real_state) (roots: seq U64.t) (r': real_state) : prop =
  r.phase == Ph.Idle /\ r.memory.nursery == minor_reset r.memory.nursery /\
  (forall (i: nat). i < Seq.length roots ==> MBP.root_valid_for_darkening r.memory.major (Seq.index roots i)) /\
  r' == { r with memory = { r.memory with major = MStart.darkened r.memory.major roots };
                 phase = Ph.Marking; scan_pos = MP.scan_none }

/// **A major slice** at any phase (`GI.major_slice_post`): a no-op when
/// idle, mark moves while marking (handing over to the sweep when nothing is
/// grey), a slice of the sweep mid-sweep.
let slice_step (r: real_state) (budget: nat) (r': real_state) : prop =
  GI.major_slice_post r.memory.major r.scan_pos r.free_list r.phase budget
    r'.memory.major r'.scan_pos r'.free_list r'.phase /\
  r'.memory.nursery == r.memory.nursery /\ r'.ref_table == r.ref_table

/// ---------------------------------------------------------------------------
/// The step relation, and runs
/// ---------------------------------------------------------------------------

/// **One step**: from `r`, the event `e` can lead to `r'`.
let step (r: real_state) (e: event) (r': real_state) : prop =
  match e with
  | Alloc InNursery tag size init -> nursery_alloc_step r tag size init r'
  | Alloc InMajor tag size init -> major_alloc_step r tag size init r'
  | Write (Major x) i v -> major_write_step r x i v r'
  | Write (Nursery o) i v -> nursery_write_step r o i v r'
  | Read b i -> is_allocated r.memory b /\ i < block_size r.memory b /\ r' == r
  | SetRoots _ -> r' == r
  | Minor roots -> minor_step r roots r'
  | StartCycle roots -> start_step r roots r'
  | Slice budget -> slice_step r budget r'

/// **A run**: from `r0`, over the events `es`, to `r1`, every consecutive
/// pair related by `step`.
noeq type run : real_state -> list event -> real_state -> Type =
  | Done : r: real_state -> run r [] r
  | Step : #r0: real_state -> #es: list event -> #r1: real_state ->
           run r0 es r1 -> e: event -> r2: real_state ->
           squash (step r1 e r2) -> run r0 (es @ [e]) r2

/// The number of allocations among `es`: the id the next one gets.
let rec alloc_count (es: list event) : nat =
  match es with
  | [] -> 0
  | e :: rest -> (if Alloc? e then 1 else 0) + alloc_count rest

/// ---------------------------------------------------------------------------
/// The initial state
/// ---------------------------------------------------------------------------

/// The major heap at start-up: one free (blue) block from `zero_addr` to
/// the end of the heap, its free-list link (its first field) 0, and the
/// free list that block.  (`SA.init_heap_spec` places the block at address
/// 0, below `zero_addr`; this is the same heap at `zero_addr`.)
let initial_major (_: unit) : GTot (heap & U64.t) =
  let wz = (heap_size - U64.v zero_addr) / 8 - 1 in
  assert_norm (pow2 57 / 8 == pow2 54);
  FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8;
  let hdr = SA.make_header (U64.uint_to_t wz) Header.Blue 0UL in
  let g1 = write_word (Seq.create heap_size 0uy) zero_addr hdr in
  FStar.Math.Lemmas.lemma_mod_plus (U64.v zero_addr) 1 8;
  let fp : hp_addr = U64.uint_to_t (U64.v zero_addr + 8) in
  (write_word g1 fp 0UL, fp)

/// The runtime's heap at start-up: the nursery empty, the major heap one free
/// block (`initial_major`), idle, the remembered set empty.
let initial_state (_: unit) : GTot real_state =
  let (g, fp) = initial_major () in
  { memory = { nursery = minor_init (Seq.create GBase.minor_heap_size 0uy); major = g };
    free_list = fp; phase = Ph.Idle; scan_pos = MP.scan_none; ref_table = Seq.empty }

/// ---------------------------------------------------------------------------
/// Schedules
/// ---------------------------------------------------------------------------

/// The kind of an event: what the schedule fixes, without the words it
/// carries (which depend on where the blocks are).
type kind =
  | KAlloc : alloc_site -> kind
  | KWrite | KRead | KSetRoots | KMinor | KStart
  | KSlice : nat -> kind

let kind_of (e: event) : kind =
  match e with
  | Alloc site _ _ _ -> KAlloc site
  | Write _ _ _ -> KWrite
  | Read _ _ -> KRead
  | SetRoots _ -> KSetRoots
  | Minor _ -> KMinor
  | StartCycle _ -> KStart
  | Slice b -> KSlice b

let kinds (es: list event) : list kind = map kind_of es

/// **The hoisted schedule**: every cycle's slices moved to right after its
/// `start_cycle`, as one stop-the-world collection (two unbounded slices:
/// marking to the end, then the sweep to the end); the program's events and
/// the minor collections stay where they were.  (A slice outside a cycle is a
/// no-op, `GI.major_slice_spec`, and is dropped.)
let rec hoist (ks: list kind) : list kind =
  match ks with
  | [] -> []
  | KSlice _ :: rest -> hoist rest
  | KStart :: rest -> KStart :: KSlice unbounded_budget :: KSlice unbounded_budget :: hoist rest
  | k :: rest -> k :: hoist rest
