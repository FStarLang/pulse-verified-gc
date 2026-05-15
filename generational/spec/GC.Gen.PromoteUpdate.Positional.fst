module GC.Gen.PromoteUpdate.Positional

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

open GC.Gen.PromoteUpdate.Obj
open GC.Gen.PromoteUpdate.Aux

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec objects_eq_when_reads_agree (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    (forall (a: hp_addr). U64.v a >= U64.v start ==>
                      read_word g1 a == read_word g2 a))
          (ensures objects start g1 == objects start g2)
          (decreases (Seq.length g1 - U64.v start)) =
  if U64.v start + 8 >= Seq.length g1 then ()
  else begin
    assert (read_word g1 start == read_word g2 start);
    let header = read_word g1 start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g1 || next_start_nat >= pow2 64 then ()
    else if next_start_nat >= heap_size then ()
    else begin
      let next_start : hp_addr = U64.uint_to_t next_start_nat in
      objects_eq_when_reads_agree g1 g2 next_start
    end
  end
#pop-options

/// Objects from start are preserved when start >= obj + wz*8.
/// Since all field writes are at addresses < obj + wz*8 <= start,
/// all reads from start onward are unchanged.
#push-options "--z3rlimit 50 --fuel 0 --ifuel 0 --split_queries always"
private let update_object_pointers_preserves_objects_above
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map)
  (start: hp_addr)
  : Lemma (requires
      Seq.mem obj (objects zero_addr major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      U64.v start >= U64.v obj + wosize * 8 /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures objects start (update_object_pointers major obj wosize fwd 0) == objects start major)
  = let major' = update_object_pointers major obj wosize fwd 0 in
    let read_above_helper (a: hp_addr) : Lemma
      (requires U64.v a >= U64.v start)
      (ensures read_word major' a == read_word major a)
    = update_object_pointers_preserves_addr_above major obj wosize fwd 0 a
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires read_above_helper);
    objects_eq_when_reads_agree major' major start
#pop-options

/// Objects nonemptiness depends only on the header read at start.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let objects_nonempty_from_header (g1 g2: heap) (start: hp_addr)
  : Lemma (requires Seq.length g1 == Seq.length g2 /\
                    read_word g1 start == read_word g2 start /\
                    Seq.length (objects start g1) > 0)
          (ensures Seq.length (objects start g2) > 0)
  = ()
#pop-options

/// Helper: density is preserved through update_object_pointers
#push-options "--z3rlimit 50 --fuel 0 --split_queries always --z3refresh"
private let update_object_pointers_preserves_density
  (major: heap) (obj: obj_addr) (wz: nat) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    Seq.mem obj (objects zero_addr major) /\
                    U64.v obj + wz * 8 <= heap_size /\
                    wz == U64.v (wosize_of_object obj major))
          (ensures heap_objects_dense (update_object_pointers major obj wz fwd 0))
  = let major' = update_object_pointers major obj wz fwd 0 in
    let field_bounds_helper () : Lemma
      (forall (j:nat). j < wz ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0))
      = assert (U64.v obj % 8 == 0);
        assert (U64.v obj + wz * 8 <= heap_size)
    in
    field_bounds_helper ();
    update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);
    let aux (start: hp_addr) : Lemma
      (requires U64.v start + 8 < heap_size /\
               Seq.mem (f_address start) (objects zero_addr major') /\
               Seq.length (objects start major') > 0)
      (ensures (let wz' = getWosize (read_word major' start) in
                let next = U64.v start + ((U64.v wz' + 1) * 8) in
                next + 8 < heap_size ==>
                Seq.length (objects (U64.uint_to_t next) major') > 0 /\
                Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr major')))
    = // Header at start is preserved
      let fa = f_address start in
      f_address_spec start;
      hd_address_spec fa;
      if U64.v fa = U64.v obj then
        update_object_pointers_preserves_self_header major obj wz fwd 0
      else if U64.v fa > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 fa
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 start;
      assert (read_word major' start == read_word major start);
      // Membership transfers
      assert (Seq.mem (f_address start) (objects zero_addr major));
      // Nonemptiness of objects start in major
      objects_nonempty_from_header major' major start;
      assert (Seq.length (objects start major) > 0);
      // Transfer density from major
      let wz' = getWosize (read_word major start) in
      let next = U64.v start + ((U64.v wz' + 1) * 8) in
      if next + 8 < heap_size then begin
        assert (Seq.length (objects (U64.uint_to_t next) major) > 0);
        assert (Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr major));
        let next_hp : hp_addr = U64.uint_to_t next in
        let fa_next = f_address next_hp in
        f_address_spec next_hp;
        hd_address_spec fa_next;
        if U64.v fa_next = U64.v obj then
          update_object_pointers_preserves_self_header major obj wz fwd 0
        else if U64.v fa_next > U64.v obj then
          update_object_pointers_preserves_other_header major obj wz fwd 0 fa_next
        else
          update_object_pointers_preserves_addr_below major obj wz fwd 0 next_hp;
        assert (read_word major' next_hp == read_word major next_hp);
        objects_nonempty_from_header major major' next_hp
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Shift lemma: processing cons hd tl from index (k+1) is the same as processing tl from index k.
/// This is a structural property of the recursive function update_all_objects_aux.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec update_all_objects_aux_shift
  (g: heap) (hd: obj_addr) (tl: seq obj_addr) (fwd: forwarding_map) (k: nat)
  : Lemma (ensures update_all_objects_aux g (Seq.cons hd tl) fwd (k + 1) ==
                   update_all_objects_aux g tl fwd k)
          (decreases (Seq.length tl - k)) =
  if k >= Seq.length tl then ()
  else begin
    // Seq.index (cons hd tl) (k+1) == Seq.index tl k
    Seq.lemma_index_is_nth tl k;
    Seq.lemma_index_is_nth (Seq.cons hd tl) (k + 1);
    assert (Seq.index (Seq.cons hd tl) (k + 1) == Seq.index tl k);
    let obj = Seq.index tl k in
    if is_blue obj g then
      update_all_objects_aux_shift g hd tl fwd (k + 1)
    else if is_no_scan obj g then
      update_all_objects_aux_shift g hd tl fwd (k + 1)
    else begin
      let wz = U64.v (wosize_of_object obj g) in
      let g' = update_object_pointers g obj wz fwd 0 in
      update_all_objects_aux_shift g' hd tl fwd (k + 1)
    end
  end
#pop-options

/// Master positional step lemma
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always --z3refresh"
let update_all_objects_positional_step
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major = false)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let major' = update_object_pointers major obj wz fwd 0 in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    well_formed_heap_part1 major' /\
                    heap_objects_dense major' /\
                    objects zero_addr major' == objects zero_addr major /\
                    (next_nat < heap_size ==>
                      update_all_objects_aux major' (objects (U64.uint_to_t next_nat) major') fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat >= heap_size ==>
                      major' == update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major') /\
                      Seq.length (objects (U64.uint_to_t next_nat) major') > 0)))
  = // Step 1: Establish bounds
    let obj : obj_addr = f_address pos in
    objects_nonempty_head_fits pos major;
    wfh_part1_obj_bound major obj;
    f_address_spec pos;
    hd_f_roundtrip pos;
    let hdr = read_word major pos in
    let wz = U64.v (getWosize hdr) in
    let next_nat = U64.v pos + (wz + 1) * 8 in
    wosize_of_object_spec obj major;
    assert (wz == U64.v (wosize_of_object obj major));
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v pos) ((wz + 1) * 8) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (wz + 1) 8 8;
    objects_nonempty_head pos major;
    objects_nonempty_next pos major;

    // Field bounds
    let field_bounds () : Lemma
      (forall (j:nat). j < wz ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0))
      = assert (U64.v obj % 8 == 0);
        assert (U64.v obj + wz * 8 <= heap_size)
    in
    field_bounds ();

    // Step 2: well_formed_heap_part1 major'
    let major' = update_object_pointers major obj wz fwd 0 in
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects zero_addr major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = update_object_pointers_preserves_objects major obj wz fwd 0;
      hd_address_spec h;
      if h = obj then begin
        update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec h major'; wosize_of_object_spec h major
      end else if U64.v h > U64.v obj then begin
        update_object_pointers_preserves_other_header major obj wz fwd 0 h;
        wosize_of_object_spec h major'; wosize_of_object_spec h major
      end else begin
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
        wosize_of_object_spec h major; wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    assert (well_formed_heap_part1 major');

    // Step 3: density preserved
    update_object_pointers_preserves_density major obj wz fwd;

    // Step 4: objects zero_addr preserved
    update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objects zero_addr major);

    // Step 5: Spec equality
    if next_nat < heap_size then begin
      let next_hp : hp_addr = U64.uint_to_t next_nat in
      // next_hp = pos + (wz+1)*8 = obj + wz*8 (since obj = pos + 8)
      // All field writes are at addresses [obj, obj+(wz-1)*8], all < next_hp
      update_object_pointers_preserves_objects_above major obj wz fwd next_hp;
      assert (objects pos major == Seq.cons obj (objects next_hp major));
      assert (objects next_hp major' == objects next_hp major);
      // Use shift lemma
      update_all_objects_aux_shift major' obj (objects next_hp major) fwd 0;
      ()
    end else begin
      // Terminal case
      assert (Seq.length (objects pos major) == 1);
      assert (Seq.index (objects pos major) 0 == obj);
      ()
    end;
    // Step 6: Density at next position
    if next_nat + 8 < heap_size then begin
      let next_hp : hp_addr = U64.uint_to_t next_nat in
      update_object_pointers_preserves_objects_above major obj wz fwd next_hp;
      assert (objects next_hp major' == objects next_hp major);
      f_address_spec next_hp;
      let fa_next = f_address next_hp in
      hd_address_spec fa_next;
      if U64.v fa_next = U64.v obj then
        update_object_pointers_preserves_self_header major obj wz fwd 0
      else if U64.v fa_next > U64.v obj then
        update_object_pointers_preserves_other_header major obj wz fwd 0 fa_next
      else
        update_object_pointers_preserves_addr_below major obj wz fwd 0 next_hp;
      assert (Seq.mem (f_address pos) (objects zero_addr major));
      assert (Seq.length (objects pos major) > 0)
    end
#pop-options

/// Blue skip step: when the current object is blue (free-list cell),
/// skip it without modifying the heap. The spec connection advances past it.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always"
let update_all_objects_positional_step_blue
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    // Spec: skipping blue advances to the next object with same heap
                    (next_nat < heap_size ==>
                      update_all_objects_aux major (objects (U64.uint_to_t next_nat) major) fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    // Terminal: when next reaches heap_size, result is just major
                    (next_nat >= heap_size ==>
                      major == update_all_objects_aux major (objects pos major) fwd 0) /\
                    // Density: next position is valid
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major) /\
                      Seq.length (objects (U64.uint_to_t next_nat) major) > 0)))
  = let obj : obj_addr = f_address pos in
    objects_nonempty_head_fits pos major;
    wfh_part1_obj_bound major obj;
    f_address_spec pos;
    let hdr = read_word major pos in
    let wz = U64.v (getWosize hdr) in
    let next_nat = U64.v pos + (wz + 1) * 8 in
    wosize_of_object_spec obj major;
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v pos) ((wz + 1) * 8) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (wz + 1) 8 8;
    objects_nonempty_head pos major;
    objects_nonempty_next pos major;
    // Blue skip: update_all_objects_aux skips blue objects, leaving heap unchanged.
    // The objects list at pos is cons obj (objects next major).
    // Since is_blue obj major, the spec function skips obj and recurses at idx+1.
    if next_nat < heap_size then begin
      let next_hp : hp_addr = U64.uint_to_t next_nat in
      assert (objects pos major == Seq.cons obj (objects next_hp major));
      update_all_objects_aux_shift major obj (objects next_hp major) fwd 0
    end else begin
      assert (Seq.length (objects pos major) == 1);
      assert (Seq.index (objects pos major) 0 == obj)
    end
#pop-options

/// No-scan skip step: when the current object has tag >= no_scan_tag,
/// skip it without modifying the heap. Identical structure to the blue step.
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always"
let update_all_objects_positional_step_no_scan
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    heap_objects_dense major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\ next_nat < pow2 64 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    (next_nat < heap_size ==>
                      update_all_objects_aux major (objects (U64.uint_to_t next_nat) major) fwd 0 ==
                        update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat >= heap_size ==>
                      major == update_all_objects_aux major (objects pos major) fwd 0) /\
                    (next_nat + 8 < heap_size ==>
                      Seq.mem (f_address (U64.uint_to_t next_nat)) (objects zero_addr major) /\
                      Seq.length (objects (U64.uint_to_t next_nat) major) > 0)))
  = let obj : obj_addr = f_address pos in
    objects_nonempty_head_fits pos major;
    wfh_part1_obj_bound major obj;
    f_address_spec pos;
    let hdr = read_word major pos in
    let wz = U64.v (getWosize hdr) in
    let next_nat = U64.v pos + (wz + 1) * 8 in
    wosize_of_object_spec obj major;
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v pos) ((wz + 1) * 8) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (wz + 1) 8 8;
    objects_nonempty_head pos major;
    objects_nonempty_next pos major;
    // No-scan skip: update_all_objects_aux skips no-scan objects, leaving heap unchanged.
    // The objects list at pos is cons obj (objects next major).
    // Since is_no_scan obj major, the spec function skips obj and recurses at idx+1.
    if next_nat < heap_size then begin
      let next_hp : hp_addr = U64.uint_to_t next_nat in
      assert (objects pos major == Seq.cons obj (objects next_hp major));
      update_all_objects_aux_shift major obj (objects next_hp major) fwd 0
    end else begin
      assert (Seq.length (objects pos major) == 1);
      assert (Seq.index (objects pos major) 0 == obj)
    end
#pop-options

/// Terminal step
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1 --split_queries always"
let update_all_objects_terminal_step
  (major: heap) (fwd: forwarding_map) (pos: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    U64.v pos + 8 < heap_size /\
                    Seq.mem (f_address pos) (objects zero_addr major) /\
                    Seq.length (objects pos major) > 0 /\
                    is_blue (f_address pos) major = false /\
                    is_no_scan (f_address pos) major = false)
          (ensures (let hdr = read_word major pos in
                    let wz = U64.v (getWosize hdr) in
                    let obj : obj_addr = f_address pos in
                    let next_nat = U64.v pos + (wz + 1) * 8 in
                    next_nat <= heap_size /\ next_nat % 8 == 0 /\
                    U64.v obj + wz * 8 <= heap_size /\
                    (next_nat + 8 >= heap_size ==>
                      (let major' = update_object_pointers major obj wz fwd 0 in
                       major' == update_all_objects_aux major (objects pos major) fwd 0))))
  = // With fuel 2, Z3 unfolds update_all_objects_aux on singleton [obj]:
    //   idx=0 < length [obj]=1: unfolds to aux major' [obj] fwd 1
    //   idx=1 >= length [obj]=1: returns major'
    // So result = major'
    let obj : obj_addr = f_address pos in
    objects_nonempty_head_fits pos major;
    wfh_part1_obj_bound major obj;
    f_address_spec pos;
    hd_f_roundtrip pos;
    wosize_of_object_spec obj major;
    let hdr = read_word major pos in
    let wz = U64.v (getWosize hdr) in
    let next_nat = U64.v pos + (wz + 1) * 8 in
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v pos) ((wz + 1) * 8) 8;
    FStar.Math.Lemmas.lemma_mod_mul_distr_r (wz + 1) 8 8;
    objects_nonempty_head pos major;
    objects_nonempty_next pos major;
    if next_nat + 8 >= heap_size then begin
      assert (Seq.length (objects pos major) == 1);
      assert (Seq.index (objects pos major) 0 == obj);
      ()
    end
#pop-options

/// Initial membership: first object is at f_address zero_addr when heap has objects.
/// The precondition that objects zero_addr g is nonempty is a standard heap invariant
/// (same approach as mark-and-sweep's heap_objects_dense).
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let objects_initial_membership (g: heap)
  : Lemma (requires heap_size > 8 /\ well_formed_heap_part1 g /\
                    Seq.length (objects zero_addr g) > 0)
          (ensures Seq.mem (f_address zero_addr) (objects zero_addr g))
  = // With fuel 2, Z3 can unfold objects zero_addr g and see that when it's nonempty,
    // the head is f_address zero_addr. From the definition:
    // objects zero_addr g = cons (f_address zero_addr) (objects next g) when nonempty.
    // Therefore Seq.mem (f_address zero_addr) (objects zero_addr g).
    ()
#pop-options
