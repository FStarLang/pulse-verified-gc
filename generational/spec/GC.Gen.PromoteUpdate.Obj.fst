/// ---------------------------------------------------------------------------
/// GC.Gen.PromoteUpdate.Obj — Per-object pointer-update preservation lemmas
/// ---------------------------------------------------------------------------

module GC.Gen.PromoteUpdate.Obj

open FStar.Seq
module U64 = FStar.UInt64
module U8 = FStar.UInt8

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Reachability
open GC.Gen.Remembered
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas

module AllocLemmas = GC.Spec.Allocator.Lemmas
module WriteBody = GC.Gen.WriteBodyLemmas

private let write_body_preserves_objects = WriteBody.write_body_preserves_objects

/// ---------------------------------------------------------------------------
/// Pointer update preserves objects
/// ---------------------------------------------------------------------------

/// update_object_pointers writes only within the body of `obj`, so
/// the objects walk is unchanged.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_objects
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures objects zero_addr (update_object_pointers major obj wosize fwd i) == objects zero_addr major)
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          assert (U64.v addr >= U64.v obj);
          assert (U64.v addr < U64.v obj + (U64.v (wosize_of_object obj major) * 8));
          write_body_preserves_objects major obj addr new_val;
          let major' = write_word major addr new_val in
          hd_address_spec obj;
          read_write_different major addr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_objects major' obj wosize fwd (i + 1)
        end else
          update_object_pointers_preserves_objects major obj wosize fwd (i + 1)
      else
        update_object_pointers_preserves_objects major obj wosize fwd (i + 1)
#pop-options

/// update_object_pointers does not modify headers of OTHER objects.
/// Needed for the fold: after updating obj_a, obj_b's wosize is unchanged.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_other_header
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (other: obj_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      Seq.mem other (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      other <> obj /\
      U64.v other > U64.v obj /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) (hd_address other) ==
      read_word major (hd_address other))
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          // addr = obj + i*8. other > obj, so hd_address other = other - 8 >= obj.
          // By objects_separated: other > obj + wosize*8 >= obj + i*8 = addr
          // So hd_address(other) = other - 8 >= obj + wosize*8 - 8 > addr  
          hd_address_spec other;
          objects_separated 0UL major obj other;
          assert (U64.v addr < U64.v (hd_address other));
          let major' = write_word major addr new_val in
          read_write_different major addr (hd_address other) new_val;
          // Recurse: major' has same objects (proven above)
          write_body_preserves_objects major obj addr new_val;
          hd_address_spec obj;
          read_write_different major addr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_other_header major' obj wosize fwd (i + 1) other
        end else
          update_object_pointers_preserves_other_header major obj wosize fwd (i + 1) other
      else
        update_object_pointers_preserves_other_header major obj wosize fwd (i + 1) other
#pop-options

/// update_object_pointers preserves the header of obj itself.
/// All writes are at obj + i*8 (i >= 0), header is at obj - 8 < obj.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_self_header
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) (hd_address obj) ==
      read_word major (hd_address obj))
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          // addr = obj + i*8 >= obj > obj - 8 = hd_address obj
          hd_address_spec obj;
          assert (U64.v addr > U64.v (hd_address obj));
          let major' = write_word major addr new_val in
          read_write_different major addr (hd_address obj) new_val;
          write_body_preserves_objects major obj addr new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_self_header major' obj wosize fwd (i + 1)
        end else
          update_object_pointers_preserves_self_header major obj wosize fwd (i + 1)
      else
        update_object_pointers_preserves_self_header major obj wosize fwd (i + 1)
#pop-options

/// update_object_pointers preserves reads at any address below obj.
/// All writes are at obj + j*8 >= obj, so any addr < obj is untouched.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_addr_below
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (addr: hp_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      U64.v addr < U64.v obj /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) addr ==
      read_word major addr)
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let waddr : hp_addr = U64.uint_to_t field_offset in
          // waddr = obj + i*8 >= obj > addr
          assert (U64.v waddr >= U64.v obj);
          assert (U64.v addr < U64.v waddr);
          let major' = write_word major waddr new_val in
          read_write_different major waddr addr new_val;
          write_body_preserves_objects major obj waddr new_val;
          hd_address_spec obj;
          read_write_different major waddr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_addr_below major' obj wosize fwd (i + 1) addr
        end else
          update_object_pointers_preserves_addr_below major obj wosize fwd (i + 1) addr
      else
        update_object_pointers_preserves_addr_below major obj wosize fwd (i + 1) addr
#pop-options

/// update_object_pointers preserves reads at addresses >= obj + wosize*8.
/// All writes are at obj + j*8 where j < wosize, so addr above the body is untouched.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_addr_above
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  (addr: hp_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      U64.v addr >= U64.v obj + wosize * 8 /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures
      read_word (update_object_pointers major obj wosize fwd i) addr ==
      read_word major addr)
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then ()
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let waddr : hp_addr = U64.uint_to_t field_offset in
          // waddr = obj + i*8, i < wosize, so waddr < obj + wosize*8 <= addr
          assert (U64.v waddr < U64.v addr);
          let major' = write_word major waddr new_val in
          read_write_different major waddr addr new_val;
          write_body_preserves_objects major obj waddr new_val;
          hd_address_spec obj;
          read_write_different major waddr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          update_object_pointers_preserves_addr_above major' obj wosize fwd (i + 1) addr
        end else
          update_object_pointers_preserves_addr_above major obj wosize fwd (i + 1) addr
      else
        update_object_pointers_preserves_addr_above major obj wosize fwd (i + 1) addr
#pop-options

/// ---------------------------------------------------------------------------
/// Field-self lemma: what update_object_pointers does to field j of obj
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_field_self
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat) (j: nat)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      j < wosize /\
      i <= j /\
      (forall (k:nat). k < wosize ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))
    (ensures
      (let updated = update_object_pointers major obj wosize fwd i in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = read_word major field_addr in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_val)))
    (decreases (wosize - i)) =
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    assert (field_offset + 8 <= heap_size);
    assert (field_offset % 8 == 0);
    let field_val = read_word major (U64.uint_to_t field_offset) in
    if i = j then begin
      // This iteration processes field j directly
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          write_body_preserves_objects major obj addr new_val;
          let major' = write_word major addr new_val in
          hd_address_spec obj;
          read_write_different major addr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          // After writing fwd(field_val) at field j, subsequent updates (i+1..wz-1)
          // don't touch field j because they write at obj+(i+1)*8, obj+(i+2)*8, etc.
          // After writing fwd(field_val) at field j = i, subsequent updates (i+1..wz-1)
          // write at obj + k*8 for k > i, all indices > addr = obj + i*8.
          // update_obj_ptrs_preserves_earlier_field proves the recursive call preserves addr.
          read_write_same major addr new_val;
          assert (read_word major' addr == new_val);
          update_obj_ptrs_preserves_earlier_field major' obj wosize fwd (i + 1) j
        end else begin
          // field_val is minor pointer but fwd is 0: field unchanged, recursive call starts at i+1 > j
          update_obj_ptrs_preserves_earlier_field major obj wosize fwd (i + 1) j
        end
      else
        // Not a minor pointer: field unchanged, recursive call starts at i+1 > j
        update_obj_ptrs_preserves_earlier_field major obj wosize fwd (i + 1) j
    end else begin
      // i < j: this iteration processes field i, not j
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then begin
          let addr : hp_addr = U64.uint_to_t field_offset in
          write_body_preserves_objects major obj addr new_val;
          let major' = write_word major addr new_val in
          hd_address_spec obj;
          read_write_different major addr (hd_address obj) new_val;
          wosize_of_object_spec obj major;
          wosize_of_object_spec obj major';
          // Writing at field i doesn't affect field j (i < j, so addr = obj+i*8 < obj+j*8)
          let field_j_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
          assert (U64.v addr < U64.v field_j_addr);
          read_write_different major addr field_j_addr new_val;
          assert (read_word major' field_j_addr == read_word major field_j_addr);
          update_object_pointers_field_self major' obj wosize fwd (i + 1) j
        end else
          update_object_pointers_field_self major obj wosize fwd (i + 1) j
      else
        update_object_pointers_field_self major obj wosize fwd (i + 1) j
    end

/// Helper: update_object_pointers at indices > j doesn't touch field j
and update_obj_ptrs_preserves_earlier_field
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat) (j: nat)
  : Lemma
    (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      j < i /\ i <= wosize /\
      (forall (k:nat). k < wosize ==>
        (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0)))
    (ensures
      (let field_j_addr = U64.uint_to_t (U64.v obj + j * 8) in
       read_word (update_object_pointers major obj wosize fwd i) field_j_addr ==
       read_word major field_j_addr))
    (decreases (wosize - i)) =
  let field_j_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
  if i >= wosize then ()
  else
    let field_offset = U64.v obj + i * 8 in
    assert (field_offset + 8 <= heap_size);
    assert (field_offset % 8 == 0);
    let field_val = read_word major (U64.uint_to_t field_offset) in
    if is_minor_pointer field_val then
      let new_val = fwd field_val in
      if new_val <> 0UL then begin
        let addr : hp_addr = U64.uint_to_t field_offset in
        // addr = obj + i*8 > obj + j*8 = field_j_addr (since i > j)
        assert (U64.v addr > U64.v field_j_addr);
        write_body_preserves_objects major obj addr new_val;
        let major' = write_word major addr new_val in
        read_write_different major addr field_j_addr new_val;
        hd_address_spec obj;
        read_write_different major addr (hd_address obj) new_val;
        wosize_of_object_spec obj major;
        wosize_of_object_spec obj major';
        update_obj_ptrs_preserves_earlier_field major' obj wosize fwd (i + 1) j
      end else
        update_obj_ptrs_preserves_earlier_field major obj wosize fwd (i + 1) j
    else
      update_obj_ptrs_preserves_earlier_field major obj wosize fwd (i + 1) j
#pop-options
