/// ---------------------------------------------------------------------------
/// GC.Gen.Barrier - the write barrier (`caml_modify`, `caml_initialize`) at
/// the collector's phase
/// ---------------------------------------------------------------------------
///
/// OCaml 4.14's `caml_modify (fp, val)` (runtime/memory.c), for a slot `fp`
/// in the major heap: `old = *fp; *fp = val;` while marking, darken `old` (the
/// deletion barrier, `caml_darken`); if `val` is a nursery block and `old` was
/// not, add `fp` to the remembered set (the ref table).  `caml_initialize`
/// writes the first value of a field of a fresh block: no darkening (the old
/// value is garbage), and the slot is remembered when the value is young.
///
///   * **What the program owes** (`modify_ok`, trusted): the slot is a body
///     word of a non-free, scannable block that is not a closure, and the
///     value is storable there (`SPM.program_write` for the phase's
///     definition of free).  While marking, the value is one the program
///     holds, so if it is white the marker will reach it (`MM.target_ok`; the
///     plan's roots obligation, option (a)).
///   * **What the barrier does** (`modify_heap`, `modify_records`): the heap
///     after, and whether the slot must be remembered.  A nursery pointer is
///     never a major pointer (nursery offsets lie below `zero_addr`), so the
///     major heap sees a young value as an immediate.
///   * **It keeps the collector's state at every phase**
///     (`modify_phase_shape`): idle the stop-the-world shape, mid-sweep the
///     sweep phase (`SPM.write_sweep_phase`), while marking the marking
///     invariant (`MM.marking_write_barrier`) and the minor collection's
///     shape at `free_stw`.
///   * **It keeps the remembered set** (`modify_ref_table`): if the table
///     covered every nursery pointer of a non-free block and named only
///     fields of non-free scannable blocks before the write, and the slot is
///     appended exactly when the barrier says so, the same holds after.  The
///     table is the stock C one (`add_to_ref_table`); appending is the
///     bridge's part.  `initialize_ref_table` is the same for
///     `caml_initialize`, which appends whenever the value is young.

module GC.Gen.Barrier

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module GenInv = GC.Gen.HeapInvariant
module GI = GC.Gen.Incremental
module GMM = GC.Gen.MarkPhase.Minor
module MM = GC.Spec.MarkPhase.Mutator
module SPM = GC.Spec.SweepPhase.Mutator
module RT = GC.Gen.RefTable
module Promote = GC.Gen.Promote
module GB = GC.Gen.Base
module SPI = GC.Spec.SweepPhase.Intrinsic
module MS = GC.Gen.MarkState

/// A nursery pointer (4.14's `Is_block (v) && Is_young (v)`).
let is_young (v: U64.t) : GTot bool = Promote.is_minor_pointer (GB.to_minor_offset v)

/// ---------------------------------------------------------------------------
/// The barrier
/// ---------------------------------------------------------------------------

/// **What the program owes at a `caml_modify`** of the slot `a`, a body word
/// of the block `x`, with the value `v`, at the phase `ph`.
let modify_ok (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  : prop =
  SPM.program_write (GI.phase_free ph) g x a v /\ scannable g x /\
  (Ph.Marking? ph ==> MM.target_ok g (GMM.nursery_held minor) v)

/// The heap after the barrier: while marking, the old value darkened
/// (`MM.darken`, 4.14's `caml_darken`) and then the write; at any other
/// phase just the write.
let modify_heap (ph: Ph.gc_phase) (g: heap) (a: hp_addr) (v: U64.t) : GTot heap =
  if Ph.Marking? ph then write_word (MM.darken g (read_word g a)) a v
  else write_word g a v

/// Whether the slot must be remembered: the new value is young and the old
/// one was not (when it was, the slot is in the table already).
let modify_records (g: heap) (a: hp_addr) (v: U64.t) : GTot bool =
  is_young v && not (is_young (read_word g a))

/// **The barrier keeps the collector's state**, at every phase.
val modify_phase_shape (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t)
  (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape minor g fp ph /\ modify_ok ph minor g x a v)
          (ensures GI.phase_shape minor (modify_heap ph g a v) fp ph)

/// What the implementation needs of the barrier besides: the definition of
/// free is admissible, the slot's block is non-free, the old value is
/// storable there (a major pointer to a non-free block, or not a major
/// pointer), and outside marking the write keeps the walk and every header
/// (so the sweep's derived caches).
val modify_heap_facts (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t)
  (x: obj_addr) (a: hp_addr) (v: U64.t)
  : Lemma (requires GI.phase_shape minor g fp ph /\ modify_ok ph minor g x a v)
          (ensures free_def_ok (GI.phase_free ph) /\ in_use (GI.phase_free ph) g x /\
                   SPI.storable (GI.phase_free ph) g (read_word g a) /\
                   (~(Ph.Marking? ph) ==> SPI.same_heads g (modify_heap ph g a v)))

/// **The barrier keeps the mark cache** (`GC.Gen.MarkState`): while
/// marking, the block it darkens is pushed, or the overflow flag raised when
/// the stack is full, and a write into a field of the partly scanned object
/// that the mark slice has scanned restarts its scan (`MS.reset_cur`); at
/// any other phase nothing changes.
val modify_mark_cache (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t)
  (x: obj_addr) (a: hp_addr) (v: U64.t) (st: seq obj_addr) (ov: bool) (p: MS.mark_pos) (cap: nat)
  : Lemma (requires GI.phase_shape minor g fp ph /\ modify_ok ph minor g x a v /\
                    MS.mark_cache_ok g ph st ov p /\ Seq.length st <= cap)
          (ensures (let old = read_word g a in
                    let push = Ph.Marking? ph && MS.darken_target g old && Seq.length st < cap in
                    let st' = if push then Seq.cons (resolve_object (old <: obj_addr) g) st else st in
                    let ov' = ov || (Ph.Marking? ph && Seq.length st = cap) in
                    let p' = if Ph.Marking? ph then MS.reset_cur p a else p in
                    MS.mark_cache_ok (modify_heap ph g a v) ph st' ov' p'))

/// ---------------------------------------------------------------------------
/// The remembered set
/// ---------------------------------------------------------------------------

/// The table `sl'[0..n')` is `sl[0..n)` with `a` appended exactly when
/// `b` holds.
let appended (b: bool) (a: U64.t) (sl: seq U64.t) (n: nat) (sl': seq U64.t) (n': nat) : prop =
  n <= Seq.length sl /\ n' <= Seq.length sl' /\
  (if b then n' == n + 1 else n' == n) /\
  (forall (i: nat). i < n ==> Seq.index sl' i == Seq.index sl i) /\
  (b ==> Seq.index sl' n == a)

/// **A write keeps the remembered set**, the general form of `caml_modify`
/// and `caml_initialize` below: a write into a body word of a non-free
/// scannable block keeps the table when the slot is appended if the new
/// value is young, unless the old value was young too.
val write_ref_table (free: free_def) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t) (b: bool)
  (sl sl': seq U64.t) (n n': nat)
  : Lemma (requires free_def_ok free /\ in_use free g x /\ scannable g x /\ SPM.in_body g x a /\
                    RT.ref_table_covers_with free g sl n /\
                    RT.ref_table_sound_with free g sl n /\
                    appended b a sl n sl' n' /\
                    (is_young v ==> b \/ is_young (read_word g a)))
          (ensures RT.ref_table_covers_with free (write_word g a v) sl' n' /\
                   RT.ref_table_sound_with free (write_word g a v) sl' n')

/// **`caml_modify` keeps the remembered set**: with the slot appended iff
/// `modify_records`, the table still covers every nursery pointer of a
/// non-free scannable block, and still names only fields of such blocks, for
/// the phase's definition of free.
val modify_ref_table (ph: Ph.gc_phase) (minor: minor_state) (g: heap) (fp: U64.t)
  (x: obj_addr) (a: hp_addr) (v: U64.t) (sl sl': seq U64.t) (n n': nat)
  : Lemma (requires GI.phase_shape minor g fp ph /\ modify_ok ph minor g x a v /\
                    RT.ref_table_covers_with (GI.phase_free ph) g sl n /\
                    RT.ref_table_sound_with (GI.phase_free ph) g sl n /\
                    appended (modify_records g a v) a sl n sl' n')
          (ensures RT.ref_table_covers_with (GI.phase_free ph) (modify_heap ph g a v) sl' n' /\
                   RT.ref_table_sound_with (GI.phase_free ph) (modify_heap ph g a v) sl' n')

/// ---------------------------------------------------------------------------
/// Initialising a field
/// ---------------------------------------------------------------------------

/// `caml_initialize` remembers the slot whenever the value is young.
let initialize_records (v: U64.t) : GTot bool = is_young v

/// **`caml_initialize` keeps the remembered set**, for any admissible
/// definition of free under which the block is non-free.  For a block just
/// allocated mid-sweep or while marking, its fields are garbage until
/// initialised; a write into it keeps it *fresh* (`SPM.fresh_write`,
/// `GC.Spec.MarkPhase.Alloc.marking_fresh_write`).  This lemma is about
/// the table only: whatever the other fields hold, the written one is
/// covered after.
val initialize_ref_table (free: free_def) (g: heap) (x: obj_addr) (a: hp_addr) (v: U64.t)
  (sl sl': seq U64.t) (n n': nat)
  : Lemma (requires free_def_ok free /\ in_use free g x /\ scannable g x /\ SPM.in_body g x a /\
                    RT.ref_table_covers_with free g sl n /\
                    RT.ref_table_sound_with free g sl n /\
                    appended (initialize_records v) a sl n sl' n')
          (ensures RT.ref_table_covers_with free (write_word g a v) sl' n' /\
                   RT.ref_table_sound_with free (write_word g a v) sl' n')
