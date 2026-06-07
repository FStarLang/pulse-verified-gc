/// ---------------------------------------------------------------------------
/// GC.Gen.CombinedGraph -- Implementation
/// ---------------------------------------------------------------------------

module GC.Gen.CombinedGraph

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SeqMem = GC.Spec.SeqMemLemmas
module SpecMajorAlloc = GC.Spec.MajorAllocator

/// ---------------------------------------------------------------------------
/// Decidable equality for combined_vertex
/// ---------------------------------------------------------------------------

let cv_eqtype : squash (hasEq combined_vertex) = ()

/// ---------------------------------------------------------------------------
/// Field Classification
/// ---------------------------------------------------------------------------

/// From a minor object's field: normalize potential minor pointers first,
/// matching Cheney scanning and pointer updates.
let classify_minor_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)
  = let vo = to_minor_offset v in
    if is_minor_addr vo && Seq.mem vo (minor_objects ms) then
      Some (MinorV vo)
    else if is_val_addr v && Seq.mem v (objects zero_addr major) then
      Some (MajorV v)
    else
      None

let classify_minor_field_minor (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires (
             let vo = to_minor_offset v in
             is_minor_addr vo /\ Seq.mem vo (minor_objects ms)))
          (ensures classify_minor_field ms major v == Some (MinorV (to_minor_offset v)))
  = ()

let classify_minor_field_major (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires is_val_addr v /\ Seq.mem v (objects zero_addr major) /\
                    (let vo = to_minor_offset v in
                     ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms))))
          (ensures classify_minor_field ms major v == Some (MajorV v))
  = ()

/// From a major object's field: normalize potential minor pointers first,
/// matching remembered-set scanning and pointer updates.
let classify_major_field (ms: minor_state) (major: heap) (v: U64.t)
  : GTot (option combined_vertex)
  = let vo = to_minor_offset v in
    if is_minor_pointer vo && Seq.mem vo (minor_objects ms) then
      Some (MinorV vo)
    else if is_val_addr v && Seq.mem v (objects zero_addr major) then
      Some (MajorV v)
    else
      None

let classify_major_field_major (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires is_val_addr v /\ Seq.mem v (objects zero_addr major) /\
                    (let vo = to_minor_offset v in
                     ~(is_minor_pointer vo /\ Seq.mem vo (minor_objects ms))))
          (ensures classify_major_field ms major v == Some (MajorV v))
  = ()

let classify_major_field_is_minor (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires (
             let vo = to_minor_offset v in
             is_minor_pointer vo /\ Seq.mem vo (minor_objects ms)))
          (ensures classify_major_field ms major v == Some (MinorV (to_minor_offset v)))
  = ()

let chunked_classify_minor_field (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : GTot (option combined_vertex)
  = let vo = to_minor_offset v in
    if is_minor_addr vo && Seq.mem vo (minor_objects ms) then
      Some (MinorV vo)
    else if is_val_addr v && Seq.mem (v <: obj_addr) (MH.major_objects mh) then
      Some (MajorV v)
    else
      None

let chunked_classify_minor_field_minor (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : Lemma (requires (
             let vo = to_minor_offset v in
             is_minor_addr vo /\ Seq.mem vo (minor_objects ms)))
          (ensures
             chunked_classify_minor_field ms mh v ==
             Some (MinorV (to_minor_offset v)))
  = ()

let chunked_classify_major_field (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : GTot (option combined_vertex)
  = let vo = to_minor_offset v in
    if is_minor_pointer vo && Seq.mem vo (minor_objects ms) then
      Some (MinorV vo)
    else if is_val_addr v && Seq.mem (v <: obj_addr) (MH.major_objects mh) then
      Some (MajorV v)
    else
      None

let chunked_major_member_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (v: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        Seq.mem v
          (MH.major_objects
            (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out) ==
        Seq.mem v (MH.major_objects mh))
  =
  SpecMajorAlloc.expand_major_heap_objects mh fresh fp;
  if Seq.mem v (MH.major_objects mh) then
    SeqMem.seq_mem_cons_tail
      (SpecMajorAlloc.fresh_chunk_object fresh)
      v
      (MH.major_objects mh)
  else if
    Seq.mem v
      (MH.major_objects
        (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out)
  then begin
    SeqMem.seq_mem_cons_not_mem_implies_eq
      (SpecMajorAlloc.fresh_chunk_object fresh)
      v
      (MH.major_objects mh);
    SpecMajorAlloc.fresh_chunk_object_in_chunk fresh;
    assert (v == SpecMajorAlloc.fresh_chunk_object fresh);
    assert (MH.pointer_in_chunk fresh v);
    assert False
  end

let chunked_classify_minor_field_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (v: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        chunked_classify_minor_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        chunked_classify_minor_field ms mh v)
  =
  let vo = to_minor_offset v in
  if is_minor_addr vo && Seq.mem vo (minor_objects ms) then ()
  else if is_val_addr v then
    chunked_major_member_preserved_by_expansion mh fresh fp (v <: obj_addr)
  else ()

let chunked_classify_major_field_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (v: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.pointer_in_chunk fresh v))
      (ensures
        chunked_classify_major_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        chunked_classify_major_field ms mh v)
  =
  let vo = to_minor_offset v in
  if is_minor_pointer vo && Seq.mem vo (minor_objects ms) then ()
  else if is_val_addr v then
    chunked_major_member_preserved_by_expansion mh fresh fp (v <: obj_addr)
  else ()

let chunked_classify_minor_field_preserved_by_expansion_guarded
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (v: U64.t)
  : Lemma
      (requires
        MH.chunk_disjoint_from_all fresh mh /\
        (let vo = to_minor_offset v in
         ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms)) ==>
           ~(MH.pointer_in_chunk fresh v)))
      (ensures
        chunked_classify_minor_field ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out v ==
        chunked_classify_minor_field ms mh v)
  =
  let vo = to_minor_offset v in
  if is_minor_addr vo && Seq.mem vo (minor_objects ms) then ()
  else if is_val_addr v then begin
    assert (~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms)));
    assert (~(MH.pointer_in_chunk fresh v));
    chunked_major_member_preserved_by_expansion mh fresh fp (v <: obj_addr)
  end
  else ()

let rec chunked_minor_field_edges (ms: minor_state) (mh: MH.major_heap)
                                   (src: U64.t) (wz: nat) (i: nat)
  : GTot (seq combined_edge) (decreases (wz - i))
  = if i >= wz then Seq.empty
    else
      let v = minor_read_field ms src i in
      let rest = chunked_minor_field_edges ms mh src wz (i + 1) in
      match chunked_classify_minor_field ms mh v with
      | Some dst -> Seq.cons (MinorV src, dst) rest
      | None -> rest

let chunked_minor_field_expansion_safe
  (ms: minor_state) (fresh: MH.heap_chunk) (src: U64.t) (wz: nat) (i: nat)
  : Tot prop =
  forall (j:nat).
    i <= j /\ j < wz ==> (
      let v = minor_read_field ms src j in
      let vo = to_minor_offset v in
      ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms)) ==>
        ~(MH.pointer_in_chunk fresh v))

let chunked_minor_field_expansion_safe_intro
  (ms: minor_state) (fresh: MH.heap_chunk) (src: U64.t) (wz: nat) (i: nat)
  : Lemma
      (requires
        (forall (j:nat).
          i <= j /\ j < wz ==> (
            let v = minor_read_field ms src j in
            let vo = to_minor_offset v in
            ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms)) ==>
              ~(MH.pointer_in_chunk fresh v))))
      (ensures chunked_minor_field_expansion_safe ms fresh src wz i)
  = ()

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_minor_field_expansion_safe_at
  (ms: minor_state) (fresh: MH.heap_chunk) (src: U64.t)
  (wz i j: nat)
  : Lemma
      (requires chunked_minor_field_expansion_safe ms fresh src wz i /\
                i <= j /\ j < wz)
      (ensures (
        let v = minor_read_field ms src j in
        let vo = to_minor_offset v in
        ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms)) ==>
          ~(MH.pointer_in_chunk fresh v)))
  = ()
#pop-options

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_minor_field_expansion_safe_tail
  (ms: minor_state) (fresh: MH.heap_chunk) (src: U64.t) (wz: nat) (i: nat)
  : Lemma
      (requires i < wz /\
                chunked_minor_field_expansion_safe ms fresh src wz i)
      (ensures chunked_minor_field_expansion_safe ms fresh src wz (i + 1))
  =
  assert (i <= i + 1);
  assert (forall (j:nat).
    i + 1 <= j /\ j < wz ==> i <= j /\ j < wz)
#pop-options

let rec chunked_minor_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (src: U64.t) (wz: nat) (i: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_minor_field_expansion_safe ms fresh src wz i)
      (ensures
        chunked_minor_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        chunked_minor_field_edges ms mh src wz i)
      (decreases (wz - i))
  =
  if i >= wz then ()
  else begin
    chunked_minor_field_expansion_safe_tail ms fresh src wz i;
    chunked_minor_field_edges_preserved_by_expansion
      ms mh fresh fp src wz (i + 1);
    assert (i <= i);
    assert (i < wz);
    chunked_minor_field_expansion_safe_at ms fresh src wz i i;
    chunked_classify_minor_field_preserved_by_expansion_guarded
      ms mh fresh fp (minor_read_field ms src i)
  end

let chunked_minor_object_edges
  (ms: minor_state) (mh: MH.major_heap) (obj: U64.t)
  : GTot (seq combined_edge)
  = chunked_minor_field_edges ms mh obj (minor_wosize ms obj) 0

let chunked_minor_object_expansion_safe
  (ms: minor_state) (fresh: MH.heap_chunk) (obj: U64.t)
  : Tot prop =
  chunked_minor_field_expansion_safe ms fresh obj (minor_wosize ms obj) 0

let chunked_minor_object_expansion_safe_intro
  (ms: minor_state) (fresh: MH.heap_chunk) (obj: U64.t)
  : Lemma
      (requires
        chunked_minor_field_expansion_safe
          ms fresh obj (minor_wosize ms obj) 0)
      (ensures chunked_minor_object_expansion_safe ms fresh obj)
  = ()

let chunked_minor_object_expansion_safe_fields
  (ms: minor_state) (fresh: MH.heap_chunk) (obj: U64.t)
  : Lemma
      (requires chunked_minor_object_expansion_safe ms fresh obj)
      (ensures
        chunked_minor_field_expansion_safe
          ms fresh obj (minor_wosize ms obj) 0)
  = ()

let chunked_minor_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_minor_object_expansion_safe ms fresh obj)
      (ensures
        chunked_minor_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_minor_object_edges ms mh obj)
  =
  chunked_minor_object_expansion_safe_fields ms fresh obj;
  chunked_minor_field_edges_preserved_by_expansion
    ms mh fresh fp obj (minor_wosize ms obj) 0

let rec chunked_all_minor_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: seq U64.t) (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else
      let obj = Seq.index objs idx in
      Seq.append
        (chunked_minor_object_edges ms mh obj)
        (chunked_all_minor_edges ms mh objs (idx + 1))

let chunked_all_minor_expansion_safe
  (ms: minor_state) (fresh: MH.heap_chunk) (objs: seq U64.t) (idx: nat)
  : Tot prop =
  forall (k:nat).
    idx <= k /\ k < Seq.length objs ==>
      chunked_minor_object_expansion_safe ms fresh (Seq.index objs k)

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_all_minor_expansion_safe_at
  (ms: minor_state) (fresh: MH.heap_chunk) (objs: seq U64.t) (idx k: nat)
  : Lemma
      (requires chunked_all_minor_expansion_safe ms fresh objs idx /\
                idx <= k /\ k < Seq.length objs)
      (ensures
        chunked_minor_object_expansion_safe ms fresh (Seq.index objs k))
  = ()
#pop-options

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_all_minor_expansion_safe_tail
  (ms: minor_state) (fresh: MH.heap_chunk) (objs: seq U64.t) (idx: nat)
  : Lemma
      (requires idx < Seq.length objs /\
                chunked_all_minor_expansion_safe ms fresh objs idx)
      (ensures chunked_all_minor_expansion_safe ms fresh objs (idx + 1))
  =
  assert (idx <= idx + 1);
  assert (forall (k:nat).
    idx + 1 <= k /\ k < Seq.length objs ==> idx <= k /\ k < Seq.length objs)
#pop-options

let rec chunked_all_minor_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: seq U64.t) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_all_minor_expansion_safe ms fresh objs idx)
      (ensures
        chunked_all_minor_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs idx ==
        chunked_all_minor_edges ms mh objs idx)
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    chunked_all_minor_expansion_safe_at ms fresh objs idx idx;
    chunked_minor_object_edges_preserved_by_expansion ms mh fresh fp obj;
    chunked_all_minor_expansion_safe_tail ms fresh objs idx;
    chunked_all_minor_edges_preserved_by_expansion
      ms mh fresh fp objs (idx + 1)
  end

let chunked_header_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option U64.t)
  = MH.read_word_in_major mh (hd_address obj)

let chunked_wosize_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option U64.t)
  = match chunked_header_of_object mh obj with
    | Some hdr -> Some (getWosize hdr)
    | None -> None

let chunked_wosize_nat_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot nat
  = match chunked_wosize_of_object mh obj with
    | Some wz -> U64.v wz
    | None -> 0

let chunked_wosize_nat_header
  (mh: MH.major_heap) (obj: obj_addr) (hdr: U64.t)
  : Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures chunked_wosize_nat_of_object mh obj == U64.v (getWosize hdr))
  = ()

let chunked_tag_of_object (mh: MH.major_heap) (obj: obj_addr)
  : GTot (option U64.t)
  = match chunked_header_of_object mh obj with
    | Some hdr -> Some (getTag hdr)
    | None -> None

let chunked_is_no_scan (mh: MH.major_heap) (obj: obj_addr)
  : GTot bool
  = match chunked_tag_of_object mh obj with
    | Some tag -> U64.v tag >= U64.v no_scan_tag
    | None -> false

let chunked_is_no_scan_header
  (mh: MH.major_heap) (obj: obj_addr) (hdr: U64.t)
  : Lemma
      (requires MH.read_word_in_major mh (hd_address obj) == Some hdr)
      (ensures
        chunked_is_no_scan mh obj ==
        (U64.v (getTag hdr) >= U64.v no_scan_tag))
  = ()

let chunked_header_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        chunked_header_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_header_of_object mh obj)
  = SpecMajorAlloc.expand_major_heap_old_read mh fresh fp (hd_address obj)

let chunked_wosize_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        chunked_wosize_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_wosize_of_object mh obj)
  = chunked_header_of_object_preserved_by_expansion mh fresh fp obj

let chunked_wosize_nat_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        chunked_wosize_nat_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_wosize_nat_of_object mh obj)
  = chunked_wosize_of_object_preserved_by_expansion mh fresh fp obj

let chunked_tag_of_object_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        chunked_tag_of_object
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_tag_of_object mh obj)
  = chunked_header_of_object_preserved_by_expansion mh fresh fp obj

let chunked_is_no_scan_preserved_by_expansion
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t) (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                ~(MH.chunk_contains_addr fresh (hd_address obj)))
      (ensures
        chunked_is_no_scan
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_is_no_scan mh obj)
  = chunked_tag_of_object_preserved_by_expansion mh fresh fp obj

let chunked_major_field_slot (src: obj_addr) (i: nat)
  : GTot (option hp_addr)
  = let field_offset = U64.v src + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then
      None
    else
      Some (U64.uint_to_t field_offset <: hp_addr)

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0"
let chunked_major_field_slot_intro
  (src: obj_addr) (i: nat) (field_addr: hp_addr)
  : Lemma
      (requires
        U64.v field_addr == U64.v src + i * U64.v mword /\
        U64.v field_addr + U64.v mword <= heap_size)
      (ensures chunked_major_field_slot src i == Some field_addr)
  =
  assert_norm (U64.v mword == 8);
  let field_offset = U64.v src + i * 8 in
  assert (field_offset == U64.v field_addr);
  assert (field_offset + 8 <= heap_size);
  assert (field_offset % 8 == 0);
  let slot_addr : hp_addr = U64.uint_to_t field_offset in
  U64.v_inj slot_addr field_addr;
  assert (slot_addr == field_addr)

let chunked_major_field_slot_elim
  (src: obj_addr) (i: nat) (field_addr: hp_addr)
  : Lemma
      (requires chunked_major_field_slot src i == Some field_addr)
      (ensures
        U64.v field_addr == U64.v src + i * U64.v mword /\
        U64.v field_addr + U64.v mword <= heap_size)
  =
  assert_norm (U64.v mword == 8);
  let field_offset = U64.v src + i * 8 in
  if field_offset + 8 > heap_size || field_offset % 8 <> 0 then
    assert False
  else begin
    let slot_addr : hp_addr = U64.uint_to_t field_offset in
    assert (chunked_major_field_slot src i == Some slot_addr);
    assert (slot_addr == field_addr);
    U64.v_inj slot_addr field_addr;
    assert (U64.v field_addr == field_offset);
    assert (field_offset == U64.v src + i * U64.v mword);
    assert (U64.v field_addr + U64.v mword <= heap_size)
  end
#pop-options

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
let chunked_major_field_slot_of_object_header
  (mh: MH.major_heap) (src: obj_addr) (hdr: U64.t) (i: nat)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        Seq.mem src (MH.major_objects mh) /\
        MH.read_word_in_major mh (hd_address src) == Some hdr /\
        i < U64.v (getWosize hdr))
      (ensures chunked_major_field_slot src i <> None)
  =
  MH.read_word_in_major_lookup_index mh (hd_address src) hdr;
  let idx = MH.lookup_chunk_index_value mh (hd_address src) in
  let c = Seq.index mh idx in
  assert (MH.lookup_chunk_index mh (hd_address src) == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk c (hd_address src));
  assert (MH.read_word_in_chunk c (hd_address src) == hdr);
  MH.major_objects_member_in_lookup_chunk mh idx src;
  assert (Seq.mem src (MH.objects_in_chunk c));
  MH.objects_in_chunk_member_header_fits c src;
  assert (MH.object_header_size_fits_in_chunk c src);
  assert (MH.object_wosize_in_chunk c src == U64.v (getWosize hdr));
  hd_address_spec src;
  assert_norm (U64.v mword == 8);
  assert (U64.v (hd_address src) + U64.v mword == U64.v src);
  let wz = U64.v (getWosize hdr) in
  assert (i + 1 <= wz);
  FStar.Math.Lemmas.lemma_mult_le_right (U64.v mword) (i + 1) wz;
  assert ((i + 1) * U64.v mword <= wz * U64.v mword);
  FStar.Math.Lemmas.distributivity_add_left i 1 (U64.v mword);
  assert (i * U64.v mword + U64.v mword == (i + 1) * U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v src) (i * U64.v mword) (U64.v mword);
  assert (U64.v src + i * U64.v mword + U64.v mword ==
          U64.v src + (i + 1) * U64.v mword);
  FStar.Math.Lemmas.distributivity_add_left 1 wz (U64.v mword);
  assert ((1 + wz) * U64.v mword == U64.v mword + wz * U64.v mword);
  FStar.Math.Lemmas.paren_add_right
    (U64.v (hd_address src)) (U64.v mword) (wz * U64.v mword);
  assert (U64.v src + wz * U64.v mword ==
          U64.v (hd_address src) + (1 + wz) * U64.v mword);
  assert (U64.v src + i * U64.v mword + U64.v mword <=
          U64.v (hd_address src) + (1 + wz) * U64.v mword);
  assert (U64.v (hd_address src) + (1 + wz) * U64.v mword <=
          MH.chunk_end c);
  assert (MH.chunk_end c <= heap_size);
  let field_offset = U64.v src + i * U64.v mword in
  assert (field_offset + U64.v mword <= heap_size);
  SpecMajorAlloc.aligned_plus_word_product (U64.v src) i;
  assert (field_offset % U64.v mword == 0);
  match chunked_major_field_slot src i with
  | None -> assert False
  | Some _ -> ()
#pop-options

let rec chunked_major_field_edges (ms: minor_state) (mh: MH.major_heap)
                                  (src: obj_addr) (wz: nat) (i: nat)
  : GTot (seq combined_edge) (decreases (wz - i))
  = if i >= wz then Seq.empty
    else
      let rest = chunked_major_field_edges ms mh src wz (i + 1) in
      match chunked_major_field_slot src i with
      | None -> rest
      | Some field_addr ->
        match MH.read_word_in_major mh field_addr with
        | None -> rest
        | Some v ->
          match chunked_classify_major_field ms mh v with
          | Some dst -> Seq.cons (MajorV src, dst) rest
          | None -> rest

let chunked_major_field_slots_miss_fresh
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (src: obj_addr) (wz: nat) (i: nat)
  : Tot prop =
  forall (j:nat) (field_addr:hp_addr).
    i <= j /\ j < wz /\
    chunked_major_field_slot src j == Some field_addr ==>
      ~(MH.chunk_contains_addr fresh field_addr)

let chunked_major_field_values_miss_fresh
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (src: obj_addr) (wz: nat) (i: nat)
  : Tot prop =
  forall (j:nat) (field_addr:hp_addr) (v:U64.t).
    i <= j /\ j < wz /\
    chunked_major_field_slot src j == Some field_addr /\
    MH.read_word_in_major mh field_addr == Some v ==>
      ~(MH.pointer_in_chunk fresh v)

let chunked_major_field_expansion_safe
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (src: obj_addr) (wz: nat) (i: nat)
  : Tot prop =
  chunked_major_field_slots_miss_fresh mh fresh src wz i /\
  chunked_major_field_values_miss_fresh mh fresh src wz i

let chunked_major_field_expansion_safe_intro
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (src: obj_addr) (wz: nat) (i: nat)
  : Lemma
      (requires
        (forall (j:nat) (field_addr:hp_addr).
          i <= j /\ j < wz /\
          chunked_major_field_slot src j == Some field_addr ==>
            ~(MH.chunk_contains_addr fresh field_addr)) /\
        (forall (j:nat) (field_addr:hp_addr) (v:U64.t).
          i <= j /\ j < wz /\
          chunked_major_field_slot src j == Some field_addr /\
          MH.read_word_in_major mh field_addr == Some v ==>
            ~(MH.pointer_in_chunk fresh v)))
      (ensures chunked_major_field_expansion_safe mh fresh src wz i)
  = ()

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_major_field_expansion_safe_at
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (src: obj_addr)
  (wz i j: nat) (field_addr: hp_addr) (v: U64.t)
  : Lemma
      (requires chunked_major_field_expansion_safe mh fresh src wz i /\
                i <= j /\ j < wz /\
                chunked_major_field_slot src j == Some field_addr)
      (ensures
        ~(MH.chunk_contains_addr fresh field_addr) /\
        (MH.read_word_in_major mh field_addr == Some v ==>
         ~(MH.pointer_in_chunk fresh v)))
  =
  assert (chunked_major_field_slots_miss_fresh mh fresh src wz i);
  assert (chunked_major_field_values_miss_fresh mh fresh src wz i)
#pop-options

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_major_field_expansion_safe_tail
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (src: obj_addr) (wz: nat) (i: nat)
  : Lemma
      (requires i < wz /\
                chunked_major_field_expansion_safe mh fresh src wz i)
      (ensures chunked_major_field_expansion_safe mh fresh src wz (i + 1))
  =
  assert (i <= i + 1);
  assert (forall (j:nat) (field_addr:hp_addr) (v:U64.t).
    i + 1 <= j /\ j < wz /\
    chunked_major_field_slot src j == Some field_addr ==>
      i <= j /\ j < wz /\
      chunked_major_field_slot src j == Some field_addr)
#pop-options

let rec chunked_major_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (src: obj_addr) (wz: nat) (i: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_major_field_expansion_safe mh fresh src wz i)
      (ensures
        chunked_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out src wz i ==
        chunked_major_field_edges ms mh src wz i)
      (decreases (wz - i))
  =
  if i >= wz then ()
  else begin
    chunked_major_field_expansion_safe_tail mh fresh src wz i;
    chunked_major_field_edges_preserved_by_expansion ms mh fresh fp src wz (i + 1);
    match chunked_major_field_slot src i with
    | None -> ()
    | Some field_addr ->
      assert (i <= i);
      assert (i < wz);
      assert (chunked_major_field_slot src i == Some field_addr);
      chunked_major_field_expansion_safe_at mh fresh src wz i i field_addr 0UL;
      SpecMajorAlloc.expand_major_heap_old_read mh fresh fp field_addr;
      match MH.read_word_in_major mh field_addr with
      | None -> ()
      | Some v ->
        chunked_major_field_expansion_safe_at mh fresh src wz i i field_addr v;
        chunked_classify_major_field_preserved_by_expansion ms mh fresh fp v
    end

let chunked_major_object_edges (ms: minor_state) (mh: MH.major_heap) (obj: obj_addr)
  : GTot (seq combined_edge)
  = if chunked_is_no_scan mh obj then Seq.empty
    else chunked_major_field_edges
      ms mh obj (chunked_wosize_nat_of_object mh obj) 0

let chunked_major_object_expansion_safe
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (obj: obj_addr)
  : Tot prop =
  ~(MH.chunk_contains_addr fresh (hd_address obj)) /\
  chunked_major_field_expansion_safe
    mh fresh obj (chunked_wosize_nat_of_object mh obj) 0

let chunked_major_object_expansion_safe_header
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (obj: obj_addr)
  : Lemma
      (requires chunked_major_object_expansion_safe mh fresh obj)
      (ensures ~(MH.chunk_contains_addr fresh (hd_address obj)))
  = ()

let chunked_major_object_expansion_safe_fields
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (obj: obj_addr)
  : Lemma
      (requires chunked_major_object_expansion_safe mh fresh obj)
      (ensures
        chunked_major_field_expansion_safe
          mh fresh obj (chunked_wosize_nat_of_object mh obj) 0)
  = ()

let chunked_major_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (obj: obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_major_object_expansion_safe mh fresh obj)
      (ensures
        chunked_major_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out obj ==
        chunked_major_object_edges ms mh obj)
  =
  chunked_major_object_expansion_safe_header mh fresh obj;
  chunked_is_no_scan_preserved_by_expansion mh fresh fp obj;
  if chunked_is_no_scan mh obj then ()
  else begin
    chunked_wosize_nat_of_object_preserved_by_expansion mh fresh fp obj;
    chunked_major_object_expansion_safe_fields mh fresh obj;
    chunked_major_field_edges_preserved_by_expansion
      ms mh fresh fp obj (chunked_wosize_nat_of_object mh obj) 0
  end

let rec chunked_all_major_object_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: seq obj_addr) (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else
      let obj = Seq.index objs idx in
      Seq.append
        (chunked_major_object_edges ms mh obj)
        (chunked_all_major_object_edges ms mh objs (idx + 1))

let chunked_all_major_object_expansion_safe
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (objs: seq obj_addr) (idx: nat)
  : Tot prop =
  forall (k:nat).
    idx <= k /\ k < Seq.length objs ==>
      chunked_major_object_expansion_safe mh fresh (Seq.index objs k)

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_all_major_object_expansion_safe_at
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (objs: seq obj_addr) (idx k: nat)
  : Lemma
      (requires chunked_all_major_object_expansion_safe mh fresh objs idx /\
                idx <= k /\ k < Seq.length objs)
      (ensures
        chunked_major_object_expansion_safe mh fresh (Seq.index objs k))
  = ()
#pop-options

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_all_major_object_expansion_safe_tail
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (objs: seq obj_addr) (idx: nat)
  : Lemma
      (requires idx < Seq.length objs /\
                chunked_all_major_object_expansion_safe mh fresh objs idx)
      (ensures chunked_all_major_object_expansion_safe mh fresh objs (idx + 1))
  =
  assert (idx <= idx + 1);
  assert (forall (k:nat).
    idx + 1 <= k /\ k < Seq.length objs ==> idx <= k /\ k < Seq.length objs)
#pop-options

let rec chunked_all_major_object_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: seq obj_addr) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_all_major_object_expansion_safe mh fresh objs idx)
      (ensures
        chunked_all_major_object_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs idx ==
        chunked_all_major_object_edges ms mh objs idx)
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    chunked_all_major_object_expansion_safe_at mh fresh objs idx idx;
    chunked_major_object_edges_preserved_by_expansion ms mh fresh fp obj;
    chunked_all_major_object_expansion_safe_tail mh fresh objs idx;
    chunked_all_major_object_edges_preserved_by_expansion
      ms mh fresh fp objs (idx + 1)
  end

let rec chunked_all_major_field_edges
  (ms: minor_state) (mh: MH.major_heap) (objs: seq obj_addr)
  (wz_of: obj_addr -> GTot nat) (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else
      let obj = Seq.index objs idx in
      Seq.append
        (chunked_major_field_edges ms mh obj (wz_of obj) 0)
        (chunked_all_major_field_edges ms mh objs wz_of (idx + 1))

let chunked_all_major_field_expansion_safe
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (objs: seq obj_addr)
  (wz_of: obj_addr -> GTot nat) (idx: nat)
  : Tot prop =
  forall (k:nat).
    idx <= k /\ k < Seq.length objs ==>
      chunked_major_field_expansion_safe
        mh fresh (Seq.index objs k) (wz_of (Seq.index objs k)) 0

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_all_major_field_expansion_safe_at
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (objs: seq obj_addr)
  (wz_of: obj_addr -> GTot nat) (idx k: nat)
  : Lemma
      (requires chunked_all_major_field_expansion_safe mh fresh objs wz_of idx /\
                idx <= k /\ k < Seq.length objs)
      (ensures
        chunked_major_field_expansion_safe
          mh fresh (Seq.index objs k) (wz_of (Seq.index objs k)) 0)
  = ()
#pop-options

#push-options "--split_queries always --fuel 0 --ifuel 0 --z3rlimit 1"
let chunked_all_major_field_expansion_safe_tail
  (mh: MH.major_heap) (fresh: MH.heap_chunk) (objs: seq obj_addr)
  (wz_of: obj_addr -> GTot nat) (idx: nat)
  : Lemma
      (requires idx < Seq.length objs /\
                chunked_all_major_field_expansion_safe mh fresh objs wz_of idx)
      (ensures
        chunked_all_major_field_expansion_safe mh fresh objs wz_of (idx + 1))
  =
  assert (idx <= idx + 1);
  assert (forall (k:nat).
    idx + 1 <= k /\ k < Seq.length objs ==> idx <= k /\ k < Seq.length objs)
#pop-options

let rec chunked_all_major_field_edges_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (objs: seq obj_addr) (wz_of: obj_addr -> GTot nat) (idx: nat)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_all_major_field_expansion_safe mh fresh objs wz_of idx)
      (ensures
        chunked_all_major_field_edges ms
          (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out objs wz_of idx ==
        chunked_all_major_field_edges ms mh objs wz_of idx)
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    chunked_all_major_field_expansion_safe_at mh fresh objs wz_of idx idx;
    chunked_major_field_edges_preserved_by_expansion
      ms mh fresh fp obj (wz_of obj) 0;
    chunked_all_major_field_expansion_safe_tail mh fresh objs wz_of idx;
    chunked_all_major_field_edges_preserved_by_expansion
      ms mh fresh fp objs wz_of (idx + 1)
  end

/// ---------------------------------------------------------------------------
/// Classification Inversion Lemmas
/// ---------------------------------------------------------------------------

let classify_minor_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MinorV x))
          (ensures to_minor_offset v == x /\ is_minor_addr x /\ Seq.mem x (minor_objects ms))
  = ()

#push-options "--z3rlimit 10"
let classify_minor_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_minor_field ms major v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) /\
                   (let vo = to_minor_offset v in
                    ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms))))
  = is_val_addr_spec v
#pop-options

let classify_major_field_inv_minor (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MinorV x))
          (ensures to_minor_offset v == x /\ is_minor_pointer x /\ Seq.mem x (minor_objects ms))
  = ()

#push-options "--z3rlimit 10"
let classify_major_field_inv_major (ms: minor_state) (major: heap) (v: U64.t) (x: U64.t)
  : Lemma (requires classify_major_field ms major v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\ Seq.mem (v <: obj_addr) (objects zero_addr major) /\
                   (let vo = to_minor_offset v in
                    ~(is_minor_pointer vo /\ Seq.mem vo (minor_objects ms))))
  = is_val_addr_spec v
#pop-options

#push-options "--z3rlimit 10"
let chunked_classify_major_field_major (ms: minor_state) (mh: MH.major_heap) (v: U64.t)
  : Lemma (requires is_val_addr v /\ Seq.mem (v <: obj_addr) (MH.major_objects mh) /\
                    (let vo = to_minor_offset v in
                     ~(is_minor_pointer vo /\ Seq.mem vo (minor_objects ms))))
          (ensures chunked_classify_major_field ms mh v == Some (MajorV v))
  = is_val_addr_spec v

let chunked_classify_minor_field_inv_minor
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t) (x: U64.t)
  : Lemma (requires chunked_classify_minor_field ms mh v == Some (MinorV x))
          (ensures to_minor_offset v == x /\
                   is_minor_addr x /\
                   Seq.mem x (minor_objects ms))
  = ()

let chunked_classify_minor_field_inv_major
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t) (x: U64.t)
  : Lemma (requires chunked_classify_minor_field ms mh v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\
                   Seq.mem (v <: obj_addr) (MH.major_objects mh) /\
                   (let vo = to_minor_offset v in
                    ~(is_minor_addr vo /\ Seq.mem vo (minor_objects ms))))
  = is_val_addr_spec v

let chunked_classify_major_field_inv_minor
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t) (x: U64.t)
  : Lemma (requires chunked_classify_major_field ms mh v == Some (MinorV x))
          (ensures to_minor_offset v == x /\
                   is_minor_pointer x /\
                   Seq.mem x (minor_objects ms))
  = ()

let chunked_classify_major_field_inv_major
  (ms: minor_state) (mh: MH.major_heap) (v: U64.t) (x: U64.t)
  : Lemma (requires chunked_classify_major_field ms mh v == Some (MajorV x))
          (ensures v == x /\ is_val_addr v /\
                   Seq.mem (v <: obj_addr) (MH.major_objects mh) /\
                   (let vo = to_minor_offset v in
                    ~(is_minor_pointer vo /\ Seq.mem vo (minor_objects ms))))
  = is_val_addr_spec v
#pop-options

/// ---------------------------------------------------------------------------
/// Edge Construction Helpers
/// ---------------------------------------------------------------------------

/// Build edges from a single minor object's fields
let rec minor_field_edges (ms: minor_state) (major: heap) (src: U64.t)
                          (wz: nat) (i: nat)
  : GTot (seq combined_edge) (decreases (wz - i))
  = if i >= wz then Seq.empty
    else
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some dst -> Seq.cons (MinorV src, dst) rest
      | None -> rest

/// Build edges from a single minor object
let minor_object_edges (ms: minor_state) (major: heap) (obj: U64.t)
  : GTot (seq combined_edge)
  = let wz = minor_wosize ms obj in
    minor_field_edges ms major obj wz 0

/// Build edges from a single major object's fields
let rec major_field_edges (ms: minor_state) (major: heap) (src: obj_addr)
                          (wz: nat) (i: nat)
  : GTot (seq combined_edge) (decreases (wz - i))
  = if i >= wz then Seq.empty
    else
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then
        Seq.empty
      else
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some dst -> Seq.cons (MajorV src, dst) rest
        | None -> rest

/// Build edges from a single major object
let major_object_edges (ms: minor_state) (major: heap) (obj: obj_addr)
  : GTot (seq combined_edge)
  = if is_no_scan obj major then Seq.empty
    else
      let wz = U64.v (wosize_of_object obj major) in
      major_field_edges ms major obj wz 0

/// ---------------------------------------------------------------------------
/// Collecting edges from all objects
/// ---------------------------------------------------------------------------

let rec all_minor_edges (ms: minor_state) (major: heap) (objs: seq U64.t)
                        (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else
      let obj = Seq.index objs idx in
      Seq.append (minor_object_edges ms major obj)
                 (all_minor_edges ms major objs (idx + 1))

let rec all_major_edges (ms: minor_state) (major: heap) (objs: seq obj_addr)
                        (idx: nat)
  : GTot (seq combined_edge) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else
      let obj = Seq.index objs idx in
      Seq.append (major_object_edges ms major obj)
                 (all_major_edges ms major objs (idx + 1))

/// ---------------------------------------------------------------------------
/// Vertex Construction
/// ---------------------------------------------------------------------------

let rec tag_minor (objs: seq U64.t) (idx: nat)
  : GTot (seq combined_vertex) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else Seq.cons (MinorV (Seq.index objs idx)) (tag_minor objs (idx + 1))

let rec tag_major (objs: seq obj_addr) (idx: nat)
  : GTot (seq combined_vertex) (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then Seq.empty
    else Seq.cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1))

let build_chunked_combined_graph_from_major_objects
  (ms: minor_state) (mh: MH.major_heap) (major_objs: seq obj_addr)
  : GTot combined_graph
  = let minor_objs = minor_objects ms in
    let verts = Seq.append (tag_minor minor_objs 0) (tag_major major_objs 0) in
    let edges = Seq.append (chunked_all_minor_edges ms mh minor_objs 0)
                           (chunked_all_major_object_edges ms mh major_objs 0) in
    { cg_vertices = verts; cg_edges = edges }

let build_chunked_combined_graph (ms: minor_state) (mh: MH.major_heap)
  : GTot combined_graph
  = build_chunked_combined_graph_from_major_objects ms mh (MH.major_objects mh)

#push-options "--z3rlimit 5"
let chunked_combined_graph_old_view_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (major_objs: seq obj_addr)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                chunked_all_major_object_expansion_safe
                  mh fresh major_objs 0)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        let g' =
          build_chunked_combined_graph_from_major_objects ms mh' major_objs in
        let g = build_chunked_combined_graph_from_major_objects ms mh major_objs in
        g'.cg_vertices == g.cg_vertices /\ g'.cg_edges == g.cg_edges))
  =
  let minor_objs = minor_objects ms in
  let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  chunked_all_minor_edges_preserved_by_expansion ms mh fresh fp minor_objs 0;
  chunked_all_major_object_edges_preserved_by_expansion
    ms mh fresh fp major_objs 0
#pop-options

#push-options "--z3rlimit 5"
let chunked_build_combined_graph_old_view_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        let g' =
          build_chunked_combined_graph_from_major_objects
            ms mh' (MH.major_objects mh) in
        let g = build_chunked_combined_graph ms mh in
        g'.cg_vertices == g.cg_vertices /\ g'.cg_edges == g.cg_edges))
  =
  chunked_combined_graph_old_view_preserved_by_expansion
    ms mh fresh fp (MH.major_objects mh)
#pop-options

/// ---------------------------------------------------------------------------
/// Graph Construction
/// ---------------------------------------------------------------------------

let build_combined_graph (ms: minor_state) (major: heap)
  : GTot combined_graph
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let verts = Seq.append (tag_minor minor_objs 0) (tag_major major_objs 0) in
    let edges = Seq.append (all_minor_edges ms major minor_objs 0)
                           (all_major_edges ms major major_objs 0) in
    { cg_vertices = verts; cg_edges = edges }

/// ---------------------------------------------------------------------------
/// Tag membership lemmas
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec tag_minor_mem (objs: seq U64.t) (idx: nat) (a: U64.t)
  : Lemma (ensures Seq.mem (MinorV a) (tag_minor objs idx) <==>
                   (exists (k:nat). idx <= k /\ k < Seq.length objs /\
                                    Seq.index objs k == a))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      tag_minor_mem objs (idx + 1) a;
      Seq.mem_cons (MinorV (Seq.index objs idx)) (tag_minor objs (idx + 1))
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec tag_major_mem (objs: seq obj_addr) (idx: nat) (a: obj_addr)
  : Lemma (ensures Seq.mem (MajorV a) (tag_major objs idx) <==>
                   (exists (k:nat). idx <= k /\ k < Seq.length objs /\
                                    Seq.index objs k == a))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      tag_major_mem objs (idx + 1) a;
      Seq.mem_cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1))
    end
#pop-options

/// MinorV never appears in tag_major
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec tag_major_no_minor (objs: seq obj_addr) (idx: nat) (a: U64.t)
  : Lemma (ensures ~(Seq.mem (MinorV a) (tag_major objs idx)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.mem_cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1));
      tag_major_no_minor objs (idx + 1) a
    end
#pop-options

/// MajorV never appears in tag_minor
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec tag_minor_no_major (objs: seq U64.t) (idx: nat) (a: U64.t)
  : Lemma (ensures ~(Seq.mem (MajorV a) (tag_minor objs idx)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.mem_cons (MinorV (Seq.index objs idx)) (tag_minor objs (idx + 1));
      tag_minor_no_major objs (idx + 1) a
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Vertex Membership Characterization
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let minor_vertex_char (ms: minor_state) (major: heap) (a: U64.t)
  : Lemma (ensures
      mem_cv (MinorV a) (build_combined_graph ms major) <==>
      Seq.mem a (minor_objects ms))
  = let g = build_combined_graph ms major in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    tag_minor_mem minor_objs 0 a;
    tag_major_no_minor major_objs 0 a;
    Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0);
    // Forward: Seq.mem a minor_objs ==> exists k. ...
    Classical.move_requires (Seq.mem_index a) minor_objs;
    // Backward: (exists k. ...) ==> Seq.mem a minor_objs (via SMTPat on Seq.index)
    ()
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let major_vertex_char (ms: minor_state) (major: heap) (a: obj_addr)
  : Lemma (ensures
      mem_cv (MajorV a) (build_combined_graph ms major) <==>
      Seq.mem a (objects zero_addr major))
  = let g = build_combined_graph ms major in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    tag_major_mem major_objs 0 a;
    tag_minor_no_major minor_objs 0 a;
    Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0);
    Classical.move_requires (Seq.mem_index a) major_objs
#pop-options

/// major_vertex_valid: if MajorV v is a vertex, extract obj_addr refinement.
/// The proof uses graph well-formedness + edge structure to derive that v
/// equals some obj_addr in the objects sequence.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec tag_major_valid (objs: seq obj_addr) (idx: nat) (v: U64.t)
  : Lemma (requires Seq.mem (MajorV v) (tag_major objs idx))
          (ensures U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
                   Seq.mem (v <: obj_addr) objs)
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.mem_cons (MajorV (Seq.index objs idx)) (tag_major objs (idx + 1));
      if MajorV (Seq.index objs idx) = MajorV v then begin
        // v == Seq.index objs idx, which is obj_addr
        let a : obj_addr = Seq.index objs idx in
        assert (v == a);
        Seq.mem_index a objs
      end
      else
        tag_major_valid objs (idx + 1) v
    end
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 15"
let major_vertex_valid (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (requires mem_cv (MajorV v) (build_combined_graph ms major))
          (ensures U64.v v >= U64.v mword /\ U64.v v < heap_size /\ U64.v v % U64.v mword == 0 /\
                   Seq.mem (v <: obj_addr) (objects zero_addr major))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    tag_minor_no_major minor_objs 0 v;
    Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0);
    tag_major_valid major_objs 0 v
#pop-options

/// ---------------------------------------------------------------------------
/// Well-Formedness Helpers
/// ---------------------------------------------------------------------------

/// Any classified vertex is in the combined graph's vertex set
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let classify_minor_in_graph (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (ensures (
      let g = build_combined_graph ms major in
      match classify_minor_field ms major v with
      | Some cv -> mem_cv cv g
      | None -> True))
  = let vo = to_minor_offset v in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    if is_minor_addr vo && Seq.mem vo minor_objs then begin
      Classical.move_requires (Seq.mem_index vo) minor_objs;
      tag_minor_mem minor_objs 0 vo;
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else if is_val_addr v && Seq.mem v major_objs then begin
      // classify returns MajorV v; is_val_addr gives us obj_addr refinement
      is_val_addr_spec v;
      let v' : obj_addr = v in
      Classical.move_requires (Seq.mem_index v') major_objs;
      tag_major_mem major_objs 0 v';
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else ()
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let classify_major_in_graph (ms: minor_state) (major: heap) (v: U64.t)
  : Lemma (ensures (
      let g = build_combined_graph ms major in
      match classify_major_field ms major v with
      | Some cv -> mem_cv cv g
      | None -> True))
  = let vo = to_minor_offset v in
    let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    if is_minor_pointer vo && Seq.mem vo minor_objs then begin
      Classical.move_requires (Seq.mem_index vo) minor_objs;
      tag_minor_mem minor_objs 0 vo;
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else if is_val_addr v && Seq.mem v major_objs then begin
      is_val_addr_spec v;
      let v' : obj_addr = v in
      Classical.move_requires (Seq.mem_index v') major_objs;
      tag_major_mem major_objs 0 v';
      Seq.lemma_mem_append (tag_minor minor_objs 0) (tag_major major_objs 0)
    end
    else ()
#pop-options

/// Every edge from minor_field_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec minor_field_edges_wf (ms: minor_state) (major: heap)
  (src: U64.t) (wz: nat) (i: nat) (e: combined_edge)
  : Lemma (requires Seq.mem src (minor_objects ms))
          (ensures Seq.mem e (minor_field_edges ms major src wz i) ==>
                   (let g = build_combined_graph ms major in
                    mem_cv (fst e) g /\ mem_cv (snd e) g))
          (decreases (wz - i))
  = if i >= wz then ()
    else begin
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some dst ->
        Seq.mem_cons (MinorV src, dst) rest;
        if Seq.mem e rest then
          minor_field_edges_wf ms major src wz (i + 1) e
        else begin
          // e = (MinorV src, dst)
          minor_vertex_char ms major src;
          classify_minor_in_graph ms major v
        end
      | None -> minor_field_edges_wf ms major src wz (i + 1) e
    end
#pop-options

/// Every edge from major_field_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec major_field_edges_wf (ms: minor_state) (major: heap)
  (src: obj_addr) (wz: nat) (i: nat) (e: combined_edge)
  : Lemma (requires Seq.mem src (objects zero_addr major))
          (ensures Seq.mem e (major_field_edges ms major src wz i) ==>
                   (let g = build_combined_graph ms major in
                    mem_cv (fst e) g /\ mem_cv (snd e) g))
          (decreases (wz - i))
  = if i >= wz then ()
    else begin
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else begin
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some dst ->
          Seq.mem_cons (MajorV src, dst) rest;
          if Seq.mem e rest then
            major_field_edges_wf ms major src wz (i + 1) e
          else begin
            major_vertex_char ms major src;
            classify_major_in_graph ms major v
          end
        | None -> major_field_edges_wf ms major src wz (i + 1) e
      end
    end
#pop-options

/// Every edge from all_minor_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec all_minor_edges_wf (ms: minor_state) (major: heap)
  (objs: seq U64.t) (idx: nat) (e: combined_edge)
  : Lemma (requires objs == minor_objects ms)
          (ensures Seq.mem e (all_minor_edges ms major objs idx) ==>
                   (let g = build_combined_graph ms major in
                    mem_cv (fst e) g /\ mem_cv (snd e) g))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      Seq.lemma_mem_append (minor_object_edges ms major obj)
                           (all_minor_edges ms major objs (idx + 1));
      if Seq.mem e (minor_object_edges ms major obj) then begin
        assert (Seq.mem obj objs);
        minor_field_edges_wf ms major obj (minor_wosize ms obj) 0 e
      end
      else
        all_minor_edges_wf ms major objs (idx + 1) e
    end
#pop-options

/// Every edge from all_major_edges has endpoints in the combined graph
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec all_major_edges_wf (ms: minor_state) (major: heap)
  (objs: seq obj_addr) (idx: nat) (e: combined_edge)
  : Lemma (requires objs == objects zero_addr major)
          (ensures Seq.mem e (all_major_edges ms major objs idx) ==>
                   (let g = build_combined_graph ms major in
                    mem_cv (fst e) g /\ mem_cv (snd e) g))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      let obj = Seq.index objs idx in
      let me = major_object_edges ms major obj in
      Seq.lemma_mem_append me (all_major_edges ms major objs (idx + 1));
      if Seq.mem e me then begin
        assert (Seq.mem obj objs);
        if is_no_scan obj major then ()
        else begin
          let wz = U64.v (wosize_of_object obj major) in
          major_field_edges_wf ms major obj wz 0 e
        end
      end
      else
        all_major_edges_wf ms major objs (idx + 1) e
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Well-Formedness Proof
/// ---------------------------------------------------------------------------

#push-options "--fuel 0 --ifuel 1 --z3rlimit 20"
let build_combined_graph_wf (ms: minor_state) (major: heap)
  : Lemma (requires well_formed_heap major /\ minor_wf ms)
          (ensures combined_graph_wf (build_combined_graph ms major))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let g = build_combined_graph ms major in
    let aux (e: combined_edge)
      : Lemma (requires mem_ce e g)
              (ensures mem_cv (fst e) g /\ mem_cv (snd e) g)
      = // e is in either all_minor_edges or all_major_edges
        Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                             (all_major_edges ms major major_objs 0);
        all_minor_edges_wf ms major minor_objs 0 e;
        all_major_edges_wf ms major major_objs 0 e
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Edge Introduction Lemmas
/// ---------------------------------------------------------------------------

/// If classify_minor_field produces a target at index i, the edge is in
/// minor_field_edges from that index onward
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let minor_field_edge_at
  (ms: minor_state) (major: heap) (src: U64.t) (wz: nat) (i: nat)
  (dst: combined_vertex)
  : Lemma (requires i < wz /\
                    classify_minor_field ms major (minor_read_field ms src i) == Some dst)
          (ensures Seq.mem (MinorV src, dst) (minor_field_edges ms major src wz i))
  = let v = minor_read_field ms src i in
    let rest = minor_field_edges ms major src wz (i + 1) in
    // classify_minor_field ms major v == Some dst, so this field matches
    Seq.mem_cons (MinorV src, dst) rest
#pop-options

/// If the edge is in minor_field_edges from a later index, it's also in
/// minor_field_edges from an earlier index
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec minor_field_edge_later
  (ms: minor_state) (major: heap) (src: U64.t) (wz: nat) (start: nat) (target_idx: nat)
  (dst: combined_vertex)
  : Lemma (requires start <= target_idx /\ target_idx < wz /\
                    classify_minor_field ms major (minor_read_field ms src target_idx) == Some dst)
          (ensures Seq.mem (MinorV src, dst) (minor_field_edges ms major src wz start))
          (decreases (wz - start))
  = if start >= wz then ()
    else if start = target_idx then
      minor_field_edge_at ms major src wz start dst
    else begin
      let v = minor_read_field ms src start in
      let rest = minor_field_edges ms major src wz (start + 1) in
      minor_field_edge_later ms major src wz (start + 1) target_idx dst;
      match classify_minor_field ms major v with
      | Some dst' -> Seq.mem_cons (MinorV src, dst') rest
      | None -> ()
    end
#pop-options

/// If src is in objs, then minor_object_edges of src are included in all_minor_edges
/// Helper to find the first occurrence index
private let rec find_index_from (objs: seq U64.t) (src: U64.t) (idx: nat)
  : Ghost nat
    (requires idx <= Seq.length objs /\ (exists (k:nat). idx <= k /\ k < Seq.length objs /\ Seq.index objs k == src))
    (ensures fun r -> idx <= r /\ r < Seq.length objs /\ Seq.index objs r == src)
    (decreases (Seq.length objs - idx))
  = if Seq.index objs idx = src then idx
    else find_index_from objs src (idx + 1)

/// If e is in all_minor_edges from some index k, then e is in all_minor_edges from 0
#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
private let rec all_minor_edges_suffix
  (ms: minor_state) (major: heap) (objs: seq U64.t) (idx: nat) (e: combined_edge)
  : Lemma (requires idx <= Seq.length objs /\
                    Seq.mem e (all_minor_edges ms major objs idx))
          (ensures Seq.mem e (all_minor_edges ms major objs 0))
          (decreases idx)
  = if idx = 0 then ()
    else begin
      let prev : nat = idx - 1 in
      Seq.lemma_mem_append (minor_object_edges ms major (Seq.index objs prev))
                           (all_minor_edges ms major objs idx);
      all_minor_edges_suffix ms major objs prev e
    end
#pop-options

/// Given that src appears at index k in objs, and e is in minor_object_edges of src,
/// then e is in all_minor_edges from 0
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let all_minor_edges_includes_object
  (ms: minor_state) (major: heap) (objs: seq U64.t) (src: U64.t) (k: nat)
  (e: combined_edge)
  : Lemma (requires k < Seq.length objs /\
                    Seq.index objs k == src /\
                    Seq.mem e (minor_object_edges ms major src))
          (ensures Seq.mem e (all_minor_edges ms major objs 0))
  = // e is in minor_object_edges of src = minor_object_edges of index objs k
    // all_minor_edges from k = append (minor_object_edges obj[k]) (all_minor_edges from k+1)
    Seq.lemma_mem_append (minor_object_edges ms major (Seq.index objs k))
                         (all_minor_edges ms major objs (k + 1));
    // So e is in all_minor_edges from k
    all_minor_edges_suffix ms major objs k e
#pop-options

/// Main edge introduction lemma for minor fields
#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let minor_field_edge_intro (ms: minor_state) (major: heap)
  (src: U64.t) (i: nat) (dst: combined_vertex)
  : Lemma (requires Seq.mem src (minor_objects ms) /\
                    i < minor_wosize ms src /\
                    classify_minor_field ms major (minor_read_field ms src i) == Some dst)
          (ensures mem_ce (MinorV src, dst) (build_combined_graph ms major))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let wz = minor_wosize ms src in
    // Step 1: edge is in minor_field_edges from index 0
    minor_field_edge_later ms major src wz 0 i dst;
    // Step 2: minor_field_edges from 0 == minor_object_edges
    assert (minor_object_edges ms major src == minor_field_edges ms major src wz 0);
    // Step 3: find src's index in minor_objs
    Classical.move_requires (Seq.mem_index src) minor_objs;
    let k = find_index_from minor_objs src 0 in
    // Step 4: edge is in all_minor_edges from 0
    all_minor_edges_includes_object ms major minor_objs src k (MinorV src, dst);
    // Step 5: all_minor_edges subset cg_edges
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let chunked_minor_field_edge_at
  (ms: minor_state) (mh: MH.major_heap) (src: U64.t) (wz: nat)
  (i: nat) (dst: combined_vertex)
  : Lemma
      (requires i < wz /\
                chunked_classify_minor_field
                  ms mh (minor_read_field ms src i) == Some dst)
      (ensures
        Seq.mem (MinorV src, dst)
          (chunked_minor_field_edges ms mh src wz i))
  =
  let rest = chunked_minor_field_edges ms mh src wz (i + 1) in
  Seq.mem_cons (MinorV src, dst) rest
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec chunked_minor_field_edge_later
  (ms: minor_state) (mh: MH.major_heap) (src: U64.t) (wz: nat)
  (start target_idx: nat) (dst: combined_vertex)
  : Lemma
      (requires start <= target_idx /\ target_idx < wz /\
                chunked_classify_minor_field
                  ms mh (minor_read_field ms src target_idx) == Some dst)
      (ensures
        Seq.mem (MinorV src, dst)
          (chunked_minor_field_edges ms mh src wz start))
      (decreases (wz - start))
  =
  if start >= wz then ()
  else if start = target_idx then
    chunked_minor_field_edge_at ms mh src wz start dst
  else begin
    let rest = chunked_minor_field_edges ms mh src wz (start + 1) in
    chunked_minor_field_edge_later
      ms mh src wz (start + 1) target_idx dst;
    match chunked_classify_minor_field ms mh (minor_read_field ms src start) with
    | Some dst' -> Seq.mem_cons (MinorV src, dst') rest
    | None -> ()
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec chunked_all_minor_edges_suffix
  (ms: minor_state) (mh: MH.major_heap) (objs: seq U64.t)
  (idx: nat) (e: combined_edge)
  : Lemma
      (requires idx <= Seq.length objs /\
                Seq.mem e (chunked_all_minor_edges ms mh objs idx))
      (ensures Seq.mem e (chunked_all_minor_edges ms mh objs 0))
      (decreases idx)
  =
  if idx = 0 then ()
  else begin
    let prev : nat = idx - 1 in
    Seq.lemma_mem_append
      (chunked_minor_object_edges ms mh (Seq.index objs prev))
      (chunked_all_minor_edges ms mh objs idx);
    chunked_all_minor_edges_suffix ms mh objs prev e
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let chunked_all_minor_edges_includes_object
  (ms: minor_state) (mh: MH.major_heap) (objs: seq U64.t)
  (src: U64.t) (k: nat) (e: combined_edge)
  : Lemma
      (requires k < Seq.length objs /\
                Seq.index objs k == src /\
                Seq.mem e (chunked_minor_object_edges ms mh src))
      (ensures Seq.mem e (chunked_all_minor_edges ms mh objs 0))
  =
  Seq.lemma_mem_append
    (chunked_minor_object_edges ms mh (Seq.index objs k))
    (chunked_all_minor_edges ms mh objs (k + 1));
  chunked_all_minor_edges_suffix ms mh objs k e
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let chunked_minor_field_edge_intro
  (ms: minor_state) (mh: MH.major_heap) (major_objs: seq obj_addr)
  (src: U64.t) (i: nat) (dst: combined_vertex)
  : Lemma (requires Seq.mem src (minor_objects ms) /\
                    i < minor_wosize ms src /\
                    chunked_classify_minor_field
                      ms mh (minor_read_field ms src i) == Some dst)
          (ensures mem_ce (MinorV src, dst)
            (build_chunked_combined_graph_from_major_objects
              ms mh major_objs))
  =
  let minor_objs = minor_objects ms in
  let wz = minor_wosize ms src in
  chunked_minor_field_edge_later ms mh src wz 0 i dst;
  assert (chunked_minor_object_edges ms mh src ==
          chunked_minor_field_edges ms mh src wz 0);
  Classical.move_requires (Seq.mem_index src) minor_objs;
  let k = find_index_from minor_objs src 0 in
  chunked_all_minor_edges_includes_object
    ms mh minor_objs src k (MinorV src, dst);
  Seq.lemma_mem_append
    (chunked_all_minor_edges ms mh minor_objs 0)
    (chunked_all_major_object_edges ms mh major_objs 0)
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 10"
let chunked_minor_field_edge_intro_full
  (ms: minor_state) (mh: MH.major_heap)
  (src: U64.t) (i: nat) (dst: combined_vertex)
  : Lemma (requires Seq.mem src (minor_objects ms) /\
                    i < minor_wosize ms src /\
                    chunked_classify_minor_field
                      ms mh (minor_read_field ms src i) == Some dst)
          (ensures mem_ce (MinorV src, dst)
            (build_chunked_combined_graph ms mh))
  =
  chunked_minor_field_edge_intro ms mh (MH.major_objects mh) src i dst
#pop-options

/// ---------------------------------------------------------------------------
/// Major Edge Introduction Helpers
/// ---------------------------------------------------------------------------

/// If classify produces dst at field i, edge is in major_field_edges from i
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let major_field_edge_at
  (ms: minor_state) (major: heap) (src: obj_addr) (wz: nat) (i: nat)
  (dst: combined_vertex)
  : Lemma (requires i < wz /\
                    (let field_offset = U64.v src + i * 8 in
                     field_offset + 8 <= heap_size /\ field_offset % 8 == 0 /\
                     classify_major_field ms major (read_word major (U64.uint_to_t field_offset)) == Some dst))
          (ensures Seq.mem (MajorV src, dst) (major_field_edges ms major src wz i))
  = let field_offset = U64.v src + i * 8 in
    let v = read_word major (U64.uint_to_t field_offset) in
    let rest = major_field_edges ms major src wz (i + 1) in
    Seq.mem_cons (MajorV src, dst) rest
#pop-options

/// If the edge is in major_field_edges from a later index, it's also in from earlier
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec major_field_edge_later
  (ms: minor_state) (major: heap) (src: obj_addr) (wz: nat) (start: nat) (target_idx: nat)
  (dst: combined_vertex)
  : Lemma (requires start <= target_idx /\ target_idx < wz /\
                    (let field_offset = U64.v src + target_idx * 8 in
                     field_offset + 8 <= heap_size /\ field_offset % 8 == 0 /\
                     classify_major_field ms major (read_word major (U64.uint_to_t field_offset)) == Some dst))
          (ensures Seq.mem (MajorV src, dst) (major_field_edges ms major src wz start))
          (decreases (wz - start))
  = if start >= wz then ()
    else if start = target_idx then
      major_field_edge_at ms major src wz start dst
    else begin
      let field_offset = U64.v src + start * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else begin
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (start + 1) in
        major_field_edge_later ms major src wz (start + 1) target_idx dst;
        match classify_major_field ms major v with
        | Some dst' -> Seq.mem_cons (MajorV src, dst') rest
        | None -> ()
      end
    end
#pop-options

/// Find index of src in a seq obj_addr
private let rec find_index_from_obj (objs: seq obj_addr) (src: obj_addr) (idx: nat)
  : Ghost nat
    (requires idx <= Seq.length objs /\ (exists (k:nat). idx <= k /\ k < Seq.length objs /\ Seq.index objs k == src))
    (ensures fun r -> idx <= r /\ r < Seq.length objs /\ Seq.index objs r == src)
    (decreases (Seq.length objs - idx))
  = if Seq.index objs idx = src then idx
    else find_index_from_obj objs src (idx + 1)

/// If e is in all_major_edges from some index k, then e is in all_major_edges from 0
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
private let rec all_major_edges_suffix
  (ms: minor_state) (major: heap) (objs: seq obj_addr) (idx: nat) (e: combined_edge)
  : Lemma (requires idx <= Seq.length objs /\
                    Seq.mem e (all_major_edges ms major objs idx))
          (ensures Seq.mem e (all_major_edges ms major objs 0))
          (decreases idx)
  = if idx = 0 then ()
    else begin
      let prev : nat = idx - 1 in
      Seq.lemma_mem_append (major_object_edges ms major (Seq.index objs prev))
                           (all_major_edges ms major objs idx);
      all_major_edges_suffix ms major objs prev e
    end
#pop-options

/// Given that src appears at index k in objs, and e is in major_object_edges of src,
/// then e is in all_major_edges from 0
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let all_major_edges_includes_object
  (ms: minor_state) (major: heap) (objs: seq obj_addr) (src: obj_addr) (k: nat)
  (e: combined_edge)
  : Lemma (requires k < Seq.length objs /\
                    Seq.index objs k == src /\
                    Seq.mem e (major_object_edges ms major src))
          (ensures Seq.mem e (all_major_edges ms major objs 0))
  = Seq.lemma_mem_append (major_object_edges ms major (Seq.index objs k))
                         (all_major_edges ms major objs (k + 1));
    all_major_edges_suffix ms major objs k e
#pop-options

/// Main edge introduction lemma for major fields
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let major_field_edge_intro (ms: minor_state) (major: heap)
  (src: obj_addr) (i: nat) (dst: combined_vertex)
  : Lemma (requires Seq.mem src (objects zero_addr major) /\
                    i < U64.v (wosize_of_object src major) /\
                    ~(is_no_scan src major) /\
                    U64.v src + i * 8 + 8 <= heap_size /\
                    (U64.v src + i * 8) % 8 == 0 /\
                    classify_major_field ms major
                      (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some dst)
          (ensures mem_ce (MajorV src, dst) (build_combined_graph ms major))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let wz = U64.v (wosize_of_object src major) in
    // Step 1: edge is in major_field_edges from index 0
    major_field_edge_later ms major src wz 0 i dst;
    // Step 2: major_field_edges from 0 == major_object_edges (since not no_scan)
    assert (major_object_edges ms major src == major_field_edges ms major src wz 0);
    // Step 3: find src's index in major_objs
    Classical.move_requires (Seq.mem_index src) major_objs;
    let k = find_index_from_obj major_objs src 0 in
    // Step 4: edge is in all_major_edges from 0
    all_major_edges_includes_object ms major major_objs src k (MajorV src, dst);
    // Step 5: all_major_edges subset cg_edges (right side of append)
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0)
#pop-options

/// ---------------------------------------------------------------------------
/// Chunked Major Edge Introduction Helpers
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let chunked_major_field_edge_at
  (ms: minor_state) (mh: MH.major_heap) (src: obj_addr) (wz: nat) (i: nat)
  (field_addr: hp_addr) (v: U64.t) (dst: combined_vertex)
  : Lemma
      (requires i < wz /\
                chunked_major_field_slot src i == Some field_addr /\
                MH.read_word_in_major mh field_addr == Some v /\
                chunked_classify_major_field ms mh v == Some dst)
      (ensures
        Seq.mem (MajorV src, dst)
          (chunked_major_field_edges ms mh src wz i))
  =
  let rest = chunked_major_field_edges ms mh src wz (i + 1) in
  Seq.mem_cons (MajorV src, dst) rest
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec chunked_major_field_edge_later
  (ms: minor_state) (mh: MH.major_heap) (src: obj_addr) (wz: nat)
  (start target_idx: nat) (field_addr: hp_addr) (v: U64.t)
  (dst: combined_vertex)
  : Lemma
      (requires start <= target_idx /\ target_idx < wz /\
                chunked_major_field_slot src target_idx == Some field_addr /\
                MH.read_word_in_major mh field_addr == Some v /\
                chunked_classify_major_field ms mh v == Some dst)
      (ensures
        Seq.mem (MajorV src, dst)
          (chunked_major_field_edges ms mh src wz start))
      (decreases (wz - start))
  =
  if start >= wz then ()
  else if start = target_idx then
    chunked_major_field_edge_at ms mh src wz start field_addr v dst
  else begin
    let rest = chunked_major_field_edges ms mh src wz (start + 1) in
    chunked_major_field_edge_later
      ms mh src wz (start + 1) target_idx field_addr v dst;
    match chunked_major_field_slot src start with
    | None -> ()
    | Some fa ->
      match MH.read_word_in_major mh fa with
      | None -> ()
      | Some old ->
        match chunked_classify_major_field ms mh old with
        | Some dst' -> Seq.mem_cons (MajorV src, dst') rest
        | None -> ()
  end
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
private let rec chunked_all_major_object_edges_suffix
  (ms: minor_state) (mh: MH.major_heap) (objs: seq obj_addr)
  (idx: nat) (e: combined_edge)
  : Lemma
      (requires idx <= Seq.length objs /\
                Seq.mem e (chunked_all_major_object_edges ms mh objs idx))
      (ensures Seq.mem e (chunked_all_major_object_edges ms mh objs 0))
      (decreases idx)
  =
  if idx = 0 then ()
  else begin
    let prev : nat = idx - 1 in
    Seq.lemma_mem_append
      (chunked_major_object_edges ms mh (Seq.index objs prev))
      (chunked_all_major_object_edges ms mh objs idx);
    chunked_all_major_object_edges_suffix ms mh objs prev e
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let chunked_all_major_object_edges_includes_object
  (ms: minor_state) (mh: MH.major_heap) (objs: seq obj_addr)
  (src: obj_addr) (k: nat) (e: combined_edge)
  : Lemma
      (requires k < Seq.length objs /\
                Seq.index objs k == src /\
                Seq.mem e (chunked_major_object_edges ms mh src))
      (ensures Seq.mem e (chunked_all_major_object_edges ms mh objs 0))
  =
  Seq.lemma_mem_append
    (chunked_major_object_edges ms mh (Seq.index objs k))
    (chunked_all_major_object_edges ms mh objs (k + 1));
  chunked_all_major_object_edges_suffix ms mh objs k e
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let chunked_major_field_edge_intro
  (ms: minor_state) (mh: MH.major_heap) (major_objs: seq obj_addr)
  (src: obj_addr) (i: nat) (field_addr: hp_addr) (v: U64.t)
  (dst: combined_vertex)
  : Lemma (requires Seq.mem src major_objs /\
                    chunked_is_no_scan mh src == false /\
                    i < chunked_wosize_nat_of_object mh src /\
                    chunked_major_field_slot src i == Some field_addr /\
                    MH.read_word_in_major mh field_addr == Some v /\
                    chunked_classify_major_field ms mh v == Some dst)
          (ensures mem_ce (MajorV src, dst)
            (build_chunked_combined_graph_from_major_objects
              ms mh major_objs))
  =
  let minor_objs = minor_objects ms in
  let wz = chunked_wosize_nat_of_object mh src in
  chunked_major_field_edge_later
    ms mh src wz 0 i field_addr v dst;
  assert (chunked_major_object_edges ms mh src ==
          chunked_major_field_edges ms mh src wz 0);
  Classical.move_requires (Seq.mem_index src) major_objs;
  let k = find_index_from_obj major_objs src 0 in
  chunked_all_major_object_edges_includes_object
    ms mh major_objs src k (MajorV src, dst);
  Seq.lemma_mem_append
    (chunked_all_minor_edges ms mh minor_objs 0)
    (chunked_all_major_object_edges ms mh major_objs 0)
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let chunked_major_field_edge_intro_full
  (ms: minor_state) (mh: MH.major_heap)
  (src: obj_addr) (i: nat) (field_addr: hp_addr) (v: U64.t)
  (dst: combined_vertex)
  : Lemma (requires Seq.mem src (MH.major_objects mh) /\
                    chunked_is_no_scan mh src == false /\
                    i < chunked_wosize_nat_of_object mh src /\
                    chunked_major_field_slot src i == Some field_addr /\
                    MH.read_word_in_major mh field_addr == Some v /\
                    chunked_classify_major_field ms mh v == Some dst)
          (ensures mem_ce (MajorV src, dst)
            (build_chunked_combined_graph ms mh))
  =
  chunked_major_field_edge_intro
    ms mh (MH.major_objects mh) src i field_addr v dst
#pop-options

/// ---------------------------------------------------------------------------
/// Edge Elimination Helpers
/// ---------------------------------------------------------------------------

/// Source characterization: every edge in minor_field_edges has source MinorV src
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec minor_field_edges_source (ms: minor_state) (major: heap)
  (src: U64.t) (wz: nat) (i: nat) (e: combined_edge)
  : Lemma (requires Seq.mem e (minor_field_edges ms major src wz i))
          (ensures fst e == MinorV src /\
                   (exists (k: nat). i <= k /\ k < wz /\
                     classify_minor_field ms major (minor_read_field ms src k) == Some (snd e)))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some dst ->
        Seq.mem_cons (MinorV src, dst) rest;
        if e = (MinorV src, dst) then ()
        else minor_field_edges_source ms major src wz (i + 1) e
      | None -> minor_field_edges_source ms major src wz (i + 1) e
#pop-options

/// Source characterization: every edge in major_field_edges has source MajorV src
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec major_field_edges_source (ms: minor_state) (major: heap)
  (src: obj_addr) (wz: nat) (i: nat) (e: combined_edge)
  : Lemma (requires Seq.mem e (major_field_edges ms major src wz i))
          (ensures fst e == MajorV src /\
                   (exists (k: nat). i <= k /\ k < wz /\
                     (let fo = U64.v src + k * 8 in
                      fo + 8 <= heap_size /\ fo % 8 == 0 /\
                      classify_major_field ms major
                        (read_word major (U64.uint_to_t fo)) == Some (snd e))))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some dst ->
          Seq.mem_cons (MajorV src, dst) rest;
          if e = (MajorV src, dst) then ()
          else major_field_edges_source ms major src wz (i + 1) e
        | None -> major_field_edges_source ms major src wz (i + 1) e
#pop-options

/// Helper: if edge is in minor_field_edges, there exists a field index with classification
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec minor_field_edges_elim (ms: minor_state) (major: heap)
  (src: U64.t) (wz: nat) (i: nat) (dst: combined_vertex)
  : Lemma (requires Seq.mem (MinorV src, dst) (minor_field_edges ms major src wz i))
          (ensures exists (k: nat). i <= k /\ k < wz /\
                    classify_minor_field ms major (minor_read_field ms src k) == Some dst)
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some d ->
        Seq.mem_cons (MinorV src, d) rest;
        if (MinorV src, dst) = (MinorV src, d) then ()
        else minor_field_edges_elim ms major src wz (i + 1) dst
      | None -> minor_field_edges_elim ms major src wz (i + 1) dst
#pop-options

/// Helper: if edge is in major_field_edges, there exists a field index with classification
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let rec major_field_edges_elim (ms: minor_state) (major: heap)
  (src: obj_addr) (wz: nat) (i: nat) (dst: combined_vertex)
  : Lemma (requires Seq.mem (MajorV src, dst) (major_field_edges ms major src wz i))
          (ensures exists (k: nat). i <= k /\ k < wz /\
                    (let field_offset = U64.v src + k * 8 in
                     field_offset + 8 <= heap_size /\
                     field_offset % 8 == 0 /\
                     classify_major_field ms major
                       (read_word major (U64.uint_to_t field_offset)) == Some dst))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some d ->
          Seq.mem_cons (MajorV src, d) rest;
          if (MajorV src, dst) = (MajorV src, d) then ()
          else major_field_edges_elim ms major src wz (i + 1) dst
        | None -> major_field_edges_elim ms major src wz (i + 1) dst
#pop-options

/// Helper: edges from all_minor_edges can be traced to a specific object
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
private let rec all_minor_edges_to_object
  (ms: minor_state) (major: heap) (objs: seq U64.t) (idx: nat) (e: combined_edge)
  : Lemma (requires Seq.mem e (all_minor_edges ms major objs idx))
          (ensures exists (k: nat). idx <= k /\ k < Seq.length objs /\
                    Seq.mem e (minor_object_edges ms major (Seq.index objs k)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.lemma_mem_append (minor_object_edges ms major (Seq.index objs idx))
                           (all_minor_edges ms major objs (idx + 1));
      if Seq.mem e (minor_object_edges ms major (Seq.index objs idx)) then ()
      else all_minor_edges_to_object ms major objs (idx + 1) e
    end
#pop-options

/// Helper: edges from all_major_edges can be traced to a specific object
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
private let rec all_major_edges_to_object
  (ms: minor_state) (major: heap) (objs: seq obj_addr) (idx: nat) (e: combined_edge)
  : Lemma (requires Seq.mem e (all_major_edges ms major objs idx))
          (ensures exists (k: nat). idx <= k /\ k < Seq.length objs /\
                    Seq.mem e (major_object_edges ms major (Seq.index objs k)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      Seq.lemma_mem_append (major_object_edges ms major (Seq.index objs idx))
                           (all_major_edges ms major objs (idx + 1));
      if Seq.mem e (major_object_edges ms major (Seq.index objs idx)) then ()
      else all_major_edges_to_object ms major objs (idx + 1) e
    end
#pop-options

/// Helper: MinorV never appears as first element in major edges
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec major_field_edges_no_minor (ms: minor_state) (major: heap)
  (src: obj_addr) (wz: nat) (i: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MinorV a, dst) (major_field_edges ms major src wz i)))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let field_offset = U64.v src + i * 8 in
      if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
      else
        let v = read_word major (U64.uint_to_t field_offset) in
        let rest = major_field_edges ms major src wz (i + 1) in
        match classify_major_field ms major v with
        | Some d ->
          Seq.mem_cons (MajorV src, d) rest;
          major_field_edges_no_minor ms major src wz (i + 1) a dst
        | None -> major_field_edges_no_minor ms major src wz (i + 1) a dst
#pop-options

/// Helper: major_object_edges never has MinorV source
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let major_object_edges_no_minor (ms: minor_state) (major: heap)
  (obj: obj_addr) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MinorV a, dst) (major_object_edges ms major obj)))
  = if is_no_scan obj major then ()
    else major_field_edges_no_minor ms major obj (U64.v (wosize_of_object obj major)) 0 a dst
#pop-options

/// Helper: all_major_edges never has MinorV source
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
private let rec all_major_edges_no_minor (ms: minor_state) (major: heap)
  (objs: seq obj_addr) (idx: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MinorV a, dst) (all_major_edges ms major objs idx)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      major_object_edges_no_minor ms major (Seq.index objs idx) a dst;
      all_major_edges_no_minor ms major objs (idx + 1) a dst;
      Seq.lemma_mem_append (major_object_edges ms major (Seq.index objs idx))
                           (all_major_edges ms major objs (idx + 1))
    end
#pop-options

/// Helper: MajorV never appears as first element in minor edges
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
private let rec minor_field_edges_no_major (ms: minor_state) (major: heap)
  (src: U64.t) (wz: nat) (i: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MajorV a, dst) (minor_field_edges ms major src wz i)))
          (decreases (wz - i))
  = if i >= wz then ()
    else
      let v = minor_read_field ms src i in
      let rest = minor_field_edges ms major src wz (i + 1) in
      match classify_minor_field ms major v with
      | Some d ->
        Seq.mem_cons (MinorV src, d) rest;
        minor_field_edges_no_major ms major src wz (i + 1) a dst
      | None -> minor_field_edges_no_major ms major src wz (i + 1) a dst
#pop-options

/// Helper: minor_object_edges never has MajorV source
#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
private let minor_object_edges_no_major (ms: minor_state) (major: heap)
  (obj: U64.t) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MajorV a, dst) (minor_object_edges ms major obj)))
  = minor_field_edges_no_major ms major obj (minor_wosize ms obj) 0 a dst
#pop-options

/// Helper: all_minor_edges never has MajorV source
#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
private let rec all_minor_edges_no_major (ms: minor_state) (major: heap)
  (objs: seq U64.t) (idx: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma (ensures ~(Seq.mem (MajorV a, dst) (all_minor_edges ms major objs idx)))
          (decreases (Seq.length objs - idx))
  = if idx >= Seq.length objs then ()
    else begin
      minor_object_edges_no_major ms major (Seq.index objs idx) a dst;
      all_minor_edges_no_major ms major objs (idx + 1) a dst;
      Seq.lemma_mem_append (minor_object_edges ms major (Seq.index objs idx))
                           (all_minor_edges ms major objs (idx + 1))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Edge Elimination: Public Interface
/// ---------------------------------------------------------------------------

/// Source decomposition
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let edge_source_decomposition (ms: minor_state) (major: heap)
  (e: combined_edge)
  : Lemma (requires mem_ce e (build_combined_graph ms major))
          (ensures
            (match fst e with
             | MinorV src -> Seq.mem src (minor_objects ms)
             | MajorV src ->
               U64.v src >= U64.v mword /\ U64.v src < heap_size /\ U64.v src % U64.v mword == 0 /\
               Seq.mem (src <: obj_addr) (objects zero_addr major)))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0);
    match fst e with
    | MinorV src ->
      all_major_edges_no_minor ms major major_objs 0 src (snd e);
      assert (Seq.mem e (all_minor_edges ms major minor_objs 0));
      all_minor_edges_to_object ms major minor_objs 0 e;
      let open FStar.IndefiniteDescription in
      let k = indefinite_description_ghost nat
        (fun k -> 0 <= k /\ k < Seq.length minor_objs /\
                  Seq.mem e (minor_object_edges ms major (Seq.index minor_objs k))) in
      let obj = Seq.index minor_objs k in
      // minor_object_edges obj = minor_field_edges ms major obj wz 0
      let wz = minor_wosize ms obj in
      minor_field_edges_source ms major obj wz 0 e;
      // This gives us fst e == MinorV obj, i.e., src == obj
      assert (fst e == MinorV obj);
      assert (src == obj);
      Seq.mem_index obj minor_objs
    | MajorV src ->
      all_minor_edges_no_major ms major minor_objs 0 src (snd e);
      assert (Seq.mem e (all_major_edges ms major major_objs 0));
      all_major_edges_to_object ms major major_objs 0 e;
      let open FStar.IndefiniteDescription in
      let k = indefinite_description_ghost nat
        (fun k -> 0 <= k /\ k < Seq.length major_objs /\
                  Seq.mem e (major_object_edges ms major (Seq.index major_objs k))) in
      let obj = Seq.index major_objs k in
      // major_object_edges is non-empty only if ~(is_no_scan), and uses major_field_edges
      assert (Seq.mem e (major_object_edges ms major obj));
      // If is_no_scan, major_object_edges is empty -- contradiction with membership
      // Need fuel to see the `if is_no_scan ... then Seq.empty else ...` branch
      let wz = U64.v (wosize_of_object obj major) in
      // The following assertion helps: if is_no_scan, then edges = empty, but e is in it
      if is_no_scan obj major then begin
        assert (major_object_edges ms major obj == Seq.empty);
        assert (Seq.mem e Seq.empty);
        // This is a contradiction -- Seq.mem in empty is false
        ()
      end else begin
        major_field_edges_source ms major obj wz 0 e;
        assert (fst e == MajorV obj);
        assert (src == obj);
        Seq.mem_index obj major_objs
      end
#pop-options

/// Minor edge elimination
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let minor_edge_elim (ms: minor_state) (major: heap)
  (src: U64.t) (dst: combined_vertex)
  : Lemma (requires mem_ce (MinorV src, dst) (build_combined_graph ms major))
          (ensures Seq.mem src (minor_objects ms) /\
                   (exists (i: nat). i < minor_wosize ms src /\
                     classify_minor_field ms major (minor_read_field ms src i) == Some dst))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let e = (MinorV src, dst) in
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0);
    all_major_edges_no_minor ms major major_objs 0 src dst;
    assert (Seq.mem e (all_minor_edges ms major minor_objs 0));
    all_minor_edges_to_object ms major minor_objs 0 e;
    let open FStar.IndefiniteDescription in
    let k = indefinite_description_ghost nat
      (fun k -> 0 <= k /\ k < Seq.length minor_objs /\
                Seq.mem e (minor_object_edges ms major (Seq.index minor_objs k))) in
    let obj = Seq.index minor_objs k in
    let wz = minor_wosize ms obj in
    minor_field_edges_source ms major obj wz 0 e;
    assert (src == obj);
    Seq.mem_index obj minor_objs
#pop-options

/// Major edge elimination
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let major_edge_elim (ms: minor_state) (major: heap)
  (src: obj_addr) (dst: combined_vertex)
  : Lemma (requires mem_ce (MajorV src, dst) (build_combined_graph ms major))
          (ensures Seq.mem src (objects zero_addr major) /\
                   ~(is_no_scan src major) /\
                   (exists (i: nat). i < U64.v (wosize_of_object src major) /\
                     U64.v src + i * 8 + 8 <= heap_size /\
                     (U64.v src + i * 8) % 8 == 0 /\
                     classify_major_field ms major
                       (read_word major (U64.uint_to_t (U64.v src + i * 8))) == Some dst))
  = let minor_objs = minor_objects ms in
    let major_objs = objects zero_addr major in
    let e = (MajorV src, dst) in
    Seq.lemma_mem_append (all_minor_edges ms major minor_objs 0)
                         (all_major_edges ms major major_objs 0);
    all_minor_edges_no_major ms major minor_objs 0 src dst;
    assert (Seq.mem e (all_major_edges ms major major_objs 0));
    all_major_edges_to_object ms major major_objs 0 e;
    let open FStar.IndefiniteDescription in
    let k = indefinite_description_ghost nat
      (fun k -> 0 <= k /\ k < Seq.length major_objs /\
                Seq.mem e (major_object_edges ms major (Seq.index major_objs k))) in
    let obj = Seq.index major_objs k in
    assert (~(is_no_scan obj major));
    let wz = U64.v (wosize_of_object obj major) in
    major_field_edges_source ms major obj wz 0 e;
    assert (src == obj);
    Seq.mem_index obj major_objs
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
private let rec chunked_minor_field_edges_source
  (ms: minor_state) (mh: MH.major_heap)
  (src: U64.t) (wz i: nat) (e: combined_edge)
  : Lemma
      (requires Seq.mem e (chunked_minor_field_edges ms mh src wz i))
      (ensures fst e == MinorV src /\
               (exists (k:nat). i <= k /\ k < wz /\
                 chunked_classify_minor_field
                   ms mh (minor_read_field ms src k) == Some (snd e)))
      (decreases (wz - i))
  =
  if i >= wz then ()
  else begin
    let rest = chunked_minor_field_edges ms mh src wz (i + 1) in
    match chunked_classify_minor_field ms mh (minor_read_field ms src i) with
    | Some dst ->
      Seq.mem_cons (MinorV src, dst) rest;
      if e = (MinorV src, dst) then ()
      else chunked_minor_field_edges_source ms mh src wz (i + 1) e
    | None ->
      chunked_minor_field_edges_source ms mh src wz (i + 1) e
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
private let rec chunked_major_field_edges_source
  (ms: minor_state) (mh: MH.major_heap)
  (src: obj_addr) (wz i: nat) (e: combined_edge)
  : Lemma
      (requires Seq.mem e (chunked_major_field_edges ms mh src wz i))
      (ensures fst e == MajorV src /\
               (exists (k:nat). exists (field_addr:hp_addr).
                exists (v:U64.t).
                  i <= k /\ k < wz /\
                  chunked_major_field_slot src k == Some field_addr /\
                  MH.read_word_in_major mh field_addr == Some v /\
                  chunked_classify_major_field ms mh v == Some (snd e)))
      (decreases (wz - i))
  =
  if i >= wz then ()
  else begin
    let rest = chunked_major_field_edges ms mh src wz (i + 1) in
    match chunked_major_field_slot src i with
    | None ->
      chunked_major_field_edges_source ms mh src wz (i + 1) e
    | Some field_addr ->
      match MH.read_word_in_major mh field_addr with
      | None ->
        chunked_major_field_edges_source ms mh src wz (i + 1) e
      | Some v ->
        match chunked_classify_major_field ms mh v with
        | Some dst ->
          Seq.mem_cons (MajorV src, dst) rest;
          if e = (MajorV src, dst) then ()
          else chunked_major_field_edges_source ms mh src wz (i + 1) e
        | None ->
          chunked_major_field_edges_source ms mh src wz (i + 1) e
  end
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 5"
private let rec chunked_all_minor_edges_to_object
  (ms: minor_state) (mh: MH.major_heap)
  (objs: seq U64.t) (idx: nat) (e: combined_edge)
  : Lemma
      (requires Seq.mem e (chunked_all_minor_edges ms mh objs idx))
      (ensures exists (k:nat). idx <= k /\ k < Seq.length objs /\
                 Seq.mem e
                   (chunked_minor_object_edges ms mh (Seq.index objs k)))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    Seq.lemma_mem_append
      (chunked_minor_object_edges ms mh (Seq.index objs idx))
      (chunked_all_minor_edges ms mh objs (idx + 1));
    if Seq.mem e (chunked_minor_object_edges ms mh (Seq.index objs idx)) then ()
    else chunked_all_minor_edges_to_object ms mh objs (idx + 1) e
  end
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 5"
private let rec chunked_all_major_object_edges_to_object
  (ms: minor_state) (mh: MH.major_heap)
  (objs: seq obj_addr) (idx: nat) (e: combined_edge)
  : Lemma
      (requires Seq.mem e (chunked_all_major_object_edges ms mh objs idx))
      (ensures exists (k:nat). idx <= k /\ k < Seq.length objs /\
                 Seq.mem e
                   (chunked_major_object_edges ms mh (Seq.index objs k)))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    Seq.lemma_mem_append
      (chunked_major_object_edges ms mh (Seq.index objs idx))
      (chunked_all_major_object_edges ms mh objs (idx + 1));
    if Seq.mem e (chunked_major_object_edges ms mh (Seq.index objs idx)) then ()
    else chunked_all_major_object_edges_to_object ms mh objs (idx + 1) e
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
private let rec chunked_major_field_edges_no_minor
  (ms: minor_state) (mh: MH.major_heap)
  (src: obj_addr) (wz i: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma
      (ensures
        ~(Seq.mem (MinorV a, dst)
          (chunked_major_field_edges ms mh src wz i)))
      (decreases (wz - i))
  =
  if i >= wz then ()
  else begin
    let rest = chunked_major_field_edges ms mh src wz (i + 1) in
    match chunked_major_field_slot src i with
    | None ->
      chunked_major_field_edges_no_minor ms mh src wz (i + 1) a dst
    | Some field_addr ->
      match MH.read_word_in_major mh field_addr with
      | None ->
        chunked_major_field_edges_no_minor ms mh src wz (i + 1) a dst
      | Some v ->
        match chunked_classify_major_field ms mh v with
        | Some d ->
          Seq.mem_cons (MajorV src, d) rest;
          chunked_major_field_edges_no_minor ms mh src wz (i + 1) a dst
        | None ->
          chunked_major_field_edges_no_minor ms mh src wz (i + 1) a dst
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
private let chunked_major_object_edges_no_minor
  (ms: minor_state) (mh: MH.major_heap)
  (obj: obj_addr) (a: U64.t) (dst: combined_vertex)
  : Lemma
      (ensures
        ~(Seq.mem (MinorV a, dst)
          (chunked_major_object_edges ms mh obj)))
  =
  if chunked_is_no_scan mh obj then ()
  else
    chunked_major_field_edges_no_minor
      ms mh obj (chunked_wosize_nat_of_object mh obj) 0 a dst
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 5"
private let rec chunked_all_major_object_edges_no_minor
  (ms: minor_state) (mh: MH.major_heap)
  (objs: seq obj_addr) (idx: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma
      (ensures
        ~(Seq.mem (MinorV a, dst)
          (chunked_all_major_object_edges ms mh objs idx)))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    chunked_major_object_edges_no_minor
      ms mh (Seq.index objs idx) a dst;
    chunked_all_major_object_edges_no_minor
      ms mh objs (idx + 1) a dst;
    Seq.lemma_mem_append
      (chunked_major_object_edges ms mh (Seq.index objs idx))
      (chunked_all_major_object_edges ms mh objs (idx + 1))
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
private let rec chunked_minor_field_edges_no_major
  (ms: minor_state) (mh: MH.major_heap)
  (src: U64.t) (wz i: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma
      (ensures
        ~(Seq.mem (MajorV a, dst)
          (chunked_minor_field_edges ms mh src wz i)))
      (decreases (wz - i))
  =
  if i >= wz then ()
  else begin
    let rest = chunked_minor_field_edges ms mh src wz (i + 1) in
    match chunked_classify_minor_field ms mh (minor_read_field ms src i) with
    | Some d ->
      Seq.mem_cons (MinorV src, d) rest;
      chunked_minor_field_edges_no_major ms mh src wz (i + 1) a dst
    | None ->
      chunked_minor_field_edges_no_major ms mh src wz (i + 1) a dst
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
private let chunked_minor_object_edges_no_major
  (ms: minor_state) (mh: MH.major_heap)
  (obj: U64.t) (a: U64.t) (dst: combined_vertex)
  : Lemma
      (ensures
        ~(Seq.mem (MajorV a, dst)
          (chunked_minor_object_edges ms mh obj)))
  =
  chunked_minor_field_edges_no_major
    ms mh obj (minor_wosize ms obj) 0 a dst
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 5"
private let rec chunked_all_minor_edges_no_major
  (ms: minor_state) (mh: MH.major_heap)
  (objs: seq U64.t) (idx: nat) (a: U64.t) (dst: combined_vertex)
  : Lemma
      (ensures
        ~(Seq.mem (MajorV a, dst)
          (chunked_all_minor_edges ms mh objs idx)))
      (decreases (Seq.length objs - idx))
  =
  if idx >= Seq.length objs then ()
  else begin
    chunked_minor_object_edges_no_major ms mh (Seq.index objs idx) a dst;
    chunked_all_minor_edges_no_major ms mh objs (idx + 1) a dst;
    Seq.lemma_mem_append
      (chunked_minor_object_edges ms mh (Seq.index objs idx))
      (chunked_all_minor_edges ms mh objs (idx + 1))
  end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
let chunked_edge_source_decomposition
  (ms: minor_state) (mh: MH.major_heap) (e: combined_edge)
  : Lemma (requires mem_ce e (build_chunked_combined_graph ms mh))
          (ensures
            (match fst e with
             | MinorV src -> Seq.mem src (minor_objects ms)
             | MajorV src ->
               U64.v src >= U64.v mword /\ U64.v src < heap_size /\
               U64.v src % U64.v mword == 0 /\
               Seq.mem (src <: obj_addr) (MH.major_objects mh)))
  =
  let minor_objs = minor_objects ms in
  let major_objs = MH.major_objects mh in
  Seq.lemma_mem_append
    (chunked_all_minor_edges ms mh minor_objs 0)
    (chunked_all_major_object_edges ms mh major_objs 0);
  match fst e with
  | MinorV src ->
    chunked_all_major_object_edges_no_minor ms mh major_objs 0 src (snd e);
    assert (Seq.mem e (chunked_all_minor_edges ms mh minor_objs 0));
    chunked_all_minor_edges_to_object ms mh minor_objs 0 e;
    let open FStar.IndefiniteDescription in
    let k = indefinite_description_ghost nat
      (fun k -> 0 <= k /\ k < Seq.length minor_objs /\
                Seq.mem e
                  (chunked_minor_object_edges ms mh (Seq.index minor_objs k))) in
    let obj = Seq.index minor_objs k in
    let wz = minor_wosize ms obj in
    chunked_minor_field_edges_source ms mh obj wz 0 e;
    assert (fst e == MinorV obj);
    assert (src == obj);
    Seq.mem_index obj minor_objs
  | MajorV src ->
    chunked_all_minor_edges_no_major ms mh minor_objs 0 src (snd e);
    assert (Seq.mem e (chunked_all_major_object_edges ms mh major_objs 0));
    chunked_all_major_object_edges_to_object ms mh major_objs 0 e;
    let open FStar.IndefiniteDescription in
    let k = indefinite_description_ghost nat
      (fun k -> 0 <= k /\ k < Seq.length major_objs /\
                Seq.mem e
                  (chunked_major_object_edges ms mh (Seq.index major_objs k))) in
    let obj = Seq.index major_objs k in
    assert (Seq.mem e (chunked_major_object_edges ms mh obj));
    if chunked_is_no_scan mh obj then begin
      assert (chunked_major_object_edges ms mh obj == Seq.empty);
      assert (Seq.mem e Seq.empty)
    end else begin
      let wz = chunked_wosize_nat_of_object mh obj in
      chunked_major_field_edges_source ms mh obj wz 0 e;
      assert (fst e == MajorV obj);
      assert (src == obj);
      Seq.mem_index obj major_objs
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
let chunked_minor_edge_elim
  (ms: minor_state) (mh: MH.major_heap)
  (src: U64.t) (dst: combined_vertex)
  : Lemma (requires mem_ce (MinorV src, dst)
              (build_chunked_combined_graph ms mh))
          (ensures Seq.mem src (minor_objects ms) /\
                   (exists (i:nat). i < minor_wosize ms src /\
                     chunked_classify_minor_field
                       ms mh (minor_read_field ms src i) == Some dst))
  =
  let minor_objs = minor_objects ms in
  let major_objs = MH.major_objects mh in
  let e = (MinorV src, dst) in
  Seq.lemma_mem_append
    (chunked_all_minor_edges ms mh minor_objs 0)
    (chunked_all_major_object_edges ms mh major_objs 0);
  chunked_all_major_object_edges_no_minor ms mh major_objs 0 src dst;
  assert (Seq.mem e (chunked_all_minor_edges ms mh minor_objs 0));
  chunked_all_minor_edges_to_object ms mh minor_objs 0 e;
  let open FStar.IndefiniteDescription in
  let k = indefinite_description_ghost nat
    (fun k -> 0 <= k /\ k < Seq.length minor_objs /\
              Seq.mem e
                (chunked_minor_object_edges ms mh (Seq.index minor_objs k))) in
  let obj = Seq.index minor_objs k in
  let wz = minor_wosize ms obj in
  chunked_minor_field_edges_source ms mh obj wz 0 e;
  assert (src == obj);
  Seq.mem_index obj minor_objs
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 5"
let chunked_major_edge_elim
  (ms: minor_state) (mh: MH.major_heap)
  (src: obj_addr) (dst: combined_vertex)
  : Lemma (requires mem_ce (MajorV src, dst)
              (build_chunked_combined_graph ms mh))
          (ensures Seq.mem src (MH.major_objects mh) /\
                   chunked_is_no_scan mh src == false /\
                   (exists (i:nat). exists (field_addr:hp_addr).
                    exists (v:U64.t).
                      i < chunked_wosize_nat_of_object mh src /\
                      chunked_major_field_slot src i == Some field_addr /\
                      MH.read_word_in_major mh field_addr == Some v /\
                      chunked_classify_major_field ms mh v == Some dst))
  =
  let minor_objs = minor_objects ms in
  let major_objs = MH.major_objects mh in
  let e = (MajorV src, dst) in
  Seq.lemma_mem_append
    (chunked_all_minor_edges ms mh minor_objs 0)
    (chunked_all_major_object_edges ms mh major_objs 0);
  chunked_all_minor_edges_no_major ms mh minor_objs 0 src dst;
  assert (Seq.mem e (chunked_all_major_object_edges ms mh major_objs 0));
  chunked_all_major_object_edges_to_object ms mh major_objs 0 e;
  let open FStar.IndefiniteDescription in
  let k = indefinite_description_ghost nat
    (fun k -> 0 <= k /\ k < Seq.length major_objs /\
              Seq.mem e
                (chunked_major_object_edges ms mh (Seq.index major_objs k))) in
  let obj = Seq.index major_objs k in
  assert (~(chunked_is_no_scan mh obj));
  let wz = chunked_wosize_nat_of_object mh obj in
  chunked_major_field_edges_source ms mh obj wz 0 e;
  assert (src == obj);
  Seq.mem_index obj major_objs
#pop-options
noeq
type combined_reach (g: combined_graph) (roots: seq combined_vertex)
  : combined_vertex -> Type =
  | CR_root : v:combined_vertex{Seq.mem v roots /\ mem_cv v g} ->
              combined_reach g roots v
  | CR_step : u:combined_vertex -> v:combined_vertex ->
              combined_reach g roots u ->
              squash (mem_ce (u, v) g) ->
              combined_reach g roots v

/// ---------------------------------------------------------------------------
/// GC Morphism
/// ---------------------------------------------------------------------------

#push-options "--ifuel 1"
let gc_morphism (fwd: forwarding_map) (v: combined_vertex) : GTot combined_vertex =
  match v with
  | MinorV a -> if fwd a <> 0UL then MajorV (fwd a) else MinorV a
  | MajorV a -> MajorV a

let gc_morphism_minor_fwd (fwd: forwarding_map) (v: U64.t)
  : Lemma (requires fwd v <> 0UL)
          (ensures gc_morphism fwd (MinorV v) == MajorV (fwd v))
  = ()

let gc_morphism_minor_stay (fwd: forwarding_map) (v: U64.t)
  : Lemma (requires fwd v == 0UL)
          (ensures gc_morphism fwd (MinorV v) == MinorV v)
  = ()

let gc_morphism_major (fwd: forwarding_map) (v: U64.t)
  : Lemma (ensures gc_morphism fwd (MajorV v) == MajorV v)
  = ()
#pop-options

/// The prop-level predicate: exists a derivation
let combined_reachable (g: combined_graph) (roots: seq combined_vertex)
                       (v: combined_vertex) : GTot prop =
  exists (_: combined_reach g roots v). True

let combined_reachable_root (g: combined_graph) (roots: seq combined_vertex)
                            (v: combined_vertex)
  : Lemma (requires Seq.mem v roots /\ mem_cv v g)
          (ensures combined_reachable g roots v)
  = let witness : combined_reach g roots v = CR_root v in
    assert (combined_reachable g roots v)

let combined_reachable_step (g: combined_graph) (roots: seq combined_vertex)
                            (u v: combined_vertex)
  : Lemma (requires combined_reachable g roots u /\ mem_ce (u, v) g)
          (ensures combined_reachable g roots v)
  = // We know there exists a derivation for u
    let open FStar.IndefiniteDescription in
    assert (exists (d: combined_reach g roots u). True);
    let d = indefinite_description_ghost (combined_reach g roots u) (fun _ -> True) in
    let witness : combined_reach g roots v = CR_step u v d () in
    assert (combined_reachable g roots v)

/// Induction principle
let combined_reachable_ind (g: combined_graph) (roots: seq combined_vertex)
                           (p: combined_vertex -> prop) (v: combined_vertex)
  : Lemma (requires
      combined_reachable g roots v /\
      (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
      (forall u w. p u /\ mem_ce (u, w) g ==> p w))
    (ensures p v)
  = // By induction on the derivation tree
    let open FStar.IndefiniteDescription in
    let d = indefinite_description_ghost (combined_reach g roots v) (fun _ -> True) in
    let rec aux (#v: combined_vertex) (d: combined_reach g roots v)
      : Lemma (requires
          (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
          (forall u w. p u /\ mem_ce (u, w) g ==> p w))
        (ensures p v)
        (decreases d)
      = match d with
        | CR_root _ -> ()
        | CR_step u _ du _ -> aux du
    in
    aux d

let combined_reachable_ind_with_reach
  (g: combined_graph) (roots: seq combined_vertex)
  (p: combined_vertex -> prop) (v: combined_vertex)
  : Lemma (requires
      combined_reachable g roots v /\
      (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
      (forall u w. combined_reachable g roots u /\ p u /\ mem_ce (u, w) g ==> p w))
    (ensures p v)
  = let open FStar.IndefiniteDescription in
    let d = indefinite_description_ghost (combined_reach g roots v) (fun _ -> True) in
    let rec aux (#v: combined_vertex) (d: combined_reach g roots v)
      : Lemma
        (requires (forall r. Seq.mem r roots /\ mem_cv r g ==> p r) /\
                  (forall u w. combined_reachable g roots u /\ p u /\ mem_ce (u, w) g ==> p w))
        (ensures p v)
        (decreases d) =
      match d with
      | CR_root _ -> ()
      | CR_step u _ du _ ->
        aux du;
        let witness : combined_reach g roots u = du in
        assert (combined_reachable g roots u)
    in
    aux d

#push-options "--z3rlimit 5"
let combined_reachable_preserved_by_graph_equality
  (g1 g2: combined_graph) (roots: seq combined_vertex) (v: combined_vertex)
  : Lemma
      (requires combined_reachable g1 roots v /\
                g1.cg_vertices == g2.cg_vertices /\
                g1.cg_edges == g2.cg_edges)
      (ensures combined_reachable g2 roots v)
  =
  let open FStar.IndefiniteDescription in
  let d = indefinite_description_ghost (combined_reach g1 roots v) (fun _ -> True) in
  let rec aux (#v: combined_vertex) (d: combined_reach g1 roots v)
    : Lemma
        (requires g1.cg_vertices == g2.cg_vertices /\
                  g1.cg_edges == g2.cg_edges)
        (ensures combined_reachable g2 roots v)
        (decreases d) =
    match d with
    | CR_root rv ->
      assert (Seq.mem rv roots);
      assert (mem_cv rv g1);
      assert (mem_cv rv g2);
      combined_reachable_root g2 roots rv
    | CR_step u w du _ ->
      aux du;
      assert (mem_ce (u, w) g1);
      assert (mem_ce (u, w) g2);
      combined_reachable_step g2 roots u w
  in
  aux d
#pop-options

#push-options "--z3rlimit 5"
let chunked_old_view_reachable_preserved_by_expansion
  (ms: minor_state) (mh: MH.major_heap) (fresh: MH.heap_chunk) (fp: U64.t)
  (roots: seq combined_vertex) (v: combined_vertex)
  : Lemma
      (requires MH.chunk_disjoint_from_all fresh mh /\
                chunked_all_minor_expansion_safe
                  ms fresh (minor_objects ms) 0 /\
                chunked_all_major_object_expansion_safe
                  mh fresh (MH.major_objects mh) 0 /\
                combined_reachable
                  (build_chunked_combined_graph ms mh) roots v)
      (ensures (
        let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
        combined_reachable
          (build_chunked_combined_graph_from_major_objects
            ms mh' (MH.major_objects mh))
          roots v))
  =
  let mh' = (SpecMajorAlloc.expand_major_heap mh fresh fp).major_out in
  let g = build_chunked_combined_graph ms mh in
  let g' =
    build_chunked_combined_graph_from_major_objects
      ms mh' (MH.major_objects mh) in
  chunked_build_combined_graph_old_view_preserved_by_expansion
    ms mh fresh fp;
  assert (g'.cg_vertices == g.cg_vertices);
  assert (g'.cg_edges == g.cg_edges);
  assert (g.cg_vertices == g'.cg_vertices);
  assert (g.cg_edges == g'.cg_edges);
  combined_reachable_preserved_by_graph_equality g g' roots v
#pop-options

/// ---------------------------------------------------------------------------
/// Root Classification
/// ---------------------------------------------------------------------------

let classify_roots_impl (roots: seq U64.t)
  : GTot (seq combined_vertex)
  = classify_roots roots

/// ---------------------------------------------------------------------------
/// classify_roots membership lemmas
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec classify_roots_minor_mem (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ is_minor_pointer r)
          (ensures Seq.mem (MinorV r) (classify_roots roots))
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      Seq.mem_cons (classify_root hd) (classify_roots tl);
      if hd = r then ()
      else begin
        Seq.lemma_mem_append (Seq.create 1 hd) tl;
        classify_roots_minor_mem tl r
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec classify_roots_major_mem (roots: seq U64.t) (r: U64.t)
  : Lemma (requires Seq.mem r roots /\ ~(is_minor_pointer r))
          (ensures Seq.mem (MajorV r) (classify_roots roots))
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      Seq.mem_cons (classify_root hd) (classify_roots tl);
      if hd = r then ()
      else begin
        Seq.lemma_mem_append (Seq.create 1 hd) tl;
        classify_roots_major_mem tl r
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec classify_roots_inv_minor (roots: seq U64.t) (v: U64.t)
  : Lemma (requires Seq.mem (MinorV v) (classify_roots roots))
          (ensures Seq.mem v roots /\ is_minor_pointer v)
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      Seq.mem_cons (classify_root hd) (classify_roots tl);
      if classify_root hd = MinorV v then ()
      else begin
        Seq.lemma_mem_append (Seq.create 1 hd) tl;
        classify_roots_inv_minor tl v
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"
let rec classify_roots_inv_major (roots: seq U64.t) (v: U64.t)
  : Lemma (requires Seq.mem (MajorV v) (classify_roots roots))
          (ensures Seq.mem v roots /\ ~(is_minor_pointer v))
          (decreases Seq.length roots)
  = if Seq.length roots = 0 then ()
    else begin
      let hd = Seq.head roots in
      let tl = Seq.tail roots in
      Seq.mem_cons (classify_root hd) (classify_roots tl);
      if classify_root hd = MajorV v then ()
      else begin
        Seq.lemma_mem_append (Seq.create 1 hd) tl;
        classify_roots_inv_major tl v
      end
    end
#pop-options
