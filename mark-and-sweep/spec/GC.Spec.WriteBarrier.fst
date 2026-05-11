/// ---------------------------------------------------------------------------
/// GC.Spec.WriteBarrier - Pure spec for the intergenerational write barrier
/// ---------------------------------------------------------------------------
///
/// Stage 2 of the generational extension. Specifies `modify_spec`: writes
/// a single 64-bit field of a major-heap object, then conditionally appends
/// an entry to the remembered set when the new value is a minor-heap
/// pointer and the holder's tag does not exclude intergenerational edges.
///
/// The "is this value a minor-heap pointer?" decision is a CALLER concern
/// (Stage 4's `GC.Impl.Gen.gen_modify`). This module takes the discrimination
/// result as a plain `bool` parameter, keeping the spec free of any
/// address-representation choice.

module GC.Spec.WriteBarrier

open FStar.Seq

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.RememberedSet

/// ---------------------------------------------------------------------------
/// Excluded tags
/// ---------------------------------------------------------------------------
///
/// Holders carrying these tags never participate in major→minor edges
/// (per `docs/gen-gc-design/02-remembered-set-scope.md`):
///   249 `Infix_tag`        — out of scope (precondition elsewhere)
///   250 `Forward_tag`      — collides with Blue-color forwarding encoding
///   254 `Double_array_tag` — unboxed floats, no pointers
///   255 `Custom_tag`       — opaque to GC, fields not scanned

let is_excluded_tag (tag: U64.t) : bool =
  U64.eq tag 249UL || U64.eq tag 250UL ||
  U64.eq tag 254UL || U64.eq tag 255UL

/// Should this write be recorded as a major→minor edge?
let should_record (target_is_minor: bool) (holder_tag: U64.t) : bool =
  target_is_minor && not (is_excluded_tag holder_tag)

/// ---------------------------------------------------------------------------
/// Field address validity
/// ---------------------------------------------------------------------------
///
/// `field_address holder idx == holder + idx * mword`. The result is a
/// valid `hp_addr` when:
///   - U64.v idx < pow2 61 (precondition of `field_address`)
///   - U64.v (field_address holder idx) + mword <= heap_size
///   - U64.v (field_address holder idx) % mword == 0
///
/// The first follows from the spec parameter refinement; the second
/// follows from `idx < wosize(holder)` (caller's responsibility); the
/// third follows from `holder % mword == 0` (since holder is obj_addr)
/// and `idx * mword % mword == 0`.

let field_addr_valid (holder: obj_addr) (idx: U64.t{U64.v idx < pow2 61}) : bool =
  let f = field_address_raw holder idx in
  U64.v f + U64.v mword <= heap_size && U64.v f % U64.v mword = 0

/// Refined field address when validity holds; usable inside specifications
/// where the validity precondition is established by the caller.
let field_addr_of (holder: obj_addr) (idx: U64.t{U64.v idx < pow2 61})
  : Pure hp_addr
    (requires field_addr_valid holder idx)
    (ensures fun r ->
      U64.v r == U64.v (field_address_raw holder idx))
  = field_address_raw holder idx

/// ---------------------------------------------------------------------------
/// The transition: write the field, conditionally record
/// ---------------------------------------------------------------------------
///
/// On an invalid field address the spec returns the heap unchanged
/// (a no-op). The Pulse implementation gates the call so this branch
/// is unreachable in practice — it's there only to make `modify_spec`
/// total in F* without an effect annotation.

let modify_spec
  (g: heap)
  (rt: ref_table)
  (holder: obj_addr)
  (idx: U64.t{U64.v idx < pow2 61})
  (new_val: U64.t)
  (target_is_minor: bool)
  : (heap & ref_table)
  = if not (field_addr_valid holder idx) then (g, rt)
    else
      let f_raw = field_address_raw holder idx in
      let f_addr : hp_addr = f_raw in
      // hd_address holder = holder - mword (header location)
      let hdr = read_word g (hd_address holder) in
      let holder_tag = getTag hdr in
      let g' = write_word g f_addr new_val in
      let rt' =
        if should_record target_is_minor holder_tag
        then add_ref rt ({ holder = holder; field_idx = idx })
        else rt in
      (g', rt')

/// ---------------------------------------------------------------------------
/// Structural lemmas
/// ---------------------------------------------------------------------------

/// The remembered set grows by at most one entry.
let modify_spec_length
  (g: heap) (rt: ref_table) (holder: obj_addr)
  (idx: U64.t{U64.v idx < pow2 61}) (new_val: U64.t) (target_is_minor: bool)
  : Lemma (
      let _, rt' = modify_spec g rt holder idx new_val target_is_minor in
      Seq.length rt' <= Seq.length rt + 1)
  = ()

/// The heap's byte length is preserved.
let modify_spec_preserves_heap_size
  (g: heap) (rt: ref_table) (holder: obj_addr)
  (idx: U64.t{U64.v idx < pow2 61}) (new_val: U64.t) (target_is_minor: bool)
  : Lemma (
      let g', _ = modify_spec g rt holder idx new_val target_is_minor in
      Seq.length g' == heap_size)
  = ()

/// If the holder's tag is excluded, the remembered set is unchanged.
let modify_spec_no_excluded
  (g: heap) (rt: ref_table) (holder: obj_addr)
  (idx: U64.t{U64.v idx < pow2 61}) (new_val: U64.t) (target_is_minor: bool)
  : Lemma
      (requires
        field_addr_valid holder idx /\
        is_excluded_tag (getTag (read_word g (hd_address holder))))
      (ensures
        snd (modify_spec g rt holder idx new_val target_is_minor) == rt)
  = ()

/// If the target is not in the minor heap, the remembered set is unchanged.
let modify_spec_no_minor
  (g: heap) (rt: ref_table) (holder: obj_addr)
  (idx: U64.t{U64.v idx < pow2 61}) (new_val: U64.t)
  : Lemma (
      snd (modify_spec g rt holder idx new_val false) == rt)
  = ()

/// When recording happens, the entry is exactly `(holder, idx)`.
let modify_spec_records
  (g: heap) (rt: ref_table) (holder: obj_addr)
  (idx: U64.t{U64.v idx < pow2 61}) (new_val: U64.t)
  : Lemma
      (requires
        field_addr_valid holder idx /\
        not (is_excluded_tag (getTag (read_word g (hd_address holder)))))
      (ensures
        snd (modify_spec g rt holder idx new_val true) ==
        add_ref rt ({ holder = holder; field_idx = idx }))
  = ()
