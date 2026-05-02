/// ---------------------------------------------------------------------------
/// GC.Gen.Promote — Implementation of minor→major promotion spec
/// ---------------------------------------------------------------------------

module GC.Gen.Promote

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

module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// Promote a single object: copy fields from minor to major
/// ---------------------------------------------------------------------------

/// Copy `n` fields (words) from minor heap at `src_obj + i*8` to major heap at `dst + i*8`
let rec copy_fields (minor: minor_state) (major: heap) 
                    (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : GTot heap (decreases (n - i)) =
  if i >= n then major
  else
    let field_val = minor_read_field minor src_obj i in
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then major
    else
      let major' = write_word major (U64.uint_to_t dst_offset) field_val in
      copy_fields minor major' src_obj dst_obj (i + 1) n

/// Base case: copy_fields with i >= n is identity
let copy_fields_base (minor: minor_state) (major: heap) 
                     (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i >= n)
          (ensures copy_fields minor major src_obj dst_obj i n == major)
  = ()

/// Step lemma: one recursive unfolding of copy_fields
let copy_fields_step (minor: minor_state) (major: heap) 
                     (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i < n /\
                     U64.v dst_obj + i * 8 + 8 <= heap_size /\
                     (U64.v dst_obj + i * 8) % 8 == 0)
           (ensures copy_fields minor major src_obj dst_obj i n ==
                    copy_fields minor
                      (write_word major (U64.uint_to_t (U64.v dst_obj + i * 8))
                                       (minor_read_field minor src_obj i))
                      src_obj dst_obj (i + 1) n)
  = ()

/// ---------------------------------------------------------------------------
/// copy_fields correctness lemmas
/// ---------------------------------------------------------------------------

/// copy_fields does not modify reads at addresses outside its write range.
/// Specifically, if address `a` does not overlap with any dst + k*8 for
/// k in [i, n), then reading `a` after copy_fields gives the original value.
#push-options "--z3rlimit 20 --fuel 2"
let rec copy_fields_preserves_other
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (a: hp_addr)
  : Lemma
    (requires
      U64.v dst_obj % 8 == 0 /\
      (n > i ==> U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size) /\
      (forall (k:nat). i <= k /\ k < n ==>
        (U64.v a + 8 <= U64.v dst_obj + k * 8 \/ U64.v dst_obj + k * 8 + 8 <= U64.v a)))
    (ensures
      read_word (copy_fields minor major src_obj dst_obj i n) a == read_word major a)
    (decreases (n - i))
  = if i >= n then ()
    else begin
      let field_val = minor_read_field minor src_obj i in
      let dst_offset = U64.v dst_obj + i * 8 in
      assert (dst_offset + 8 <= heap_size);
      assert (dst_offset % 8 == 0);
      assert (dst_offset >= 0);
      let dst_addr : hp_addr = U64.uint_to_t dst_offset in
      let major' = write_word major dst_addr field_val in
      // a doesn't overlap with dst_addr (from precondition instantiated at k = i)
      assert (U64.v a + 8 <= dst_offset \/ dst_offset + 8 <= U64.v a);
      read_write_different major dst_addr a field_val;
      assert (read_word major' a == read_word major a);
      // Recursive call also preserves a
      copy_fields_preserves_other minor major' src_obj dst_obj (i + 1) n a
    end
#pop-options

/// After copy_fields from index i to n, reading field j (with i <= j < n) at
/// address dst + j*8 returns minor_read_field minor src j.
#push-options "--z3rlimit 20 --fuel 2"
let rec copy_fields_preserves
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat) (j: nat)
  : Lemma
    (requires
      i <= j /\ j < n /\
      U64.v dst_obj % 8 == 0 /\
      U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size)
    (ensures
      (let result = copy_fields minor major src_obj dst_obj i n in
       let addr_nat = U64.v dst_obj + j * 8 in
       addr_nat + 8 <= heap_size /\
       addr_nat % 8 == 0 /\
       read_word result (U64.uint_to_t addr_nat) == minor_read_field minor src_obj j))
    (decreases (n - i))
  = let field_val = minor_read_field minor src_obj i in
    let dst_offset = U64.v dst_obj + i * 8 in
    assert (dst_offset + 8 <= heap_size);
    assert (dst_offset % 8 == 0);
    let dst_addr : hp_addr = U64.uint_to_t dst_offset in
    let major' = write_word major dst_addr field_val in
    if j = i then begin
      // Field j was just written at dst_addr
      read_write_same major dst_addr field_val;
      // The recursive call writes at dst + k*8 for k = i+1,...,n-1
      // None of these overlap with dst_addr (they are all strictly greater)
      copy_fields_preserves_other minor major' src_obj dst_obj (i + 1) n dst_addr
    end else begin
      // j > i, so field j is written by the recursive call; apply IH
      copy_fields_preserves minor major' src_obj dst_obj (i + 1) n j
    end
#pop-options

/// Promote a single object from minor to major heap.
/// Uses the major-heap allocator spec to get space, then copies fields.
let promote_object (minor: minor_state) (major: heap) (obj: U64.t)
                   (fp: U64.t) (wosize: nat{wosize > 0})
  : GTot promote_one_result =
  // Use the major allocator to get space
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  let new_major = alloc_res.heap_out in
  let new_fp = alloc_res.fp_out in
  let new_addr = alloc_res.obj_out in
  if new_addr = 0UL then
    // OOM in major heap
    { major_out = major; fp_out = fp; new_addr = 0UL }
  else
    // Copy field data from minor to major
    let final_major = copy_fields minor new_major obj new_addr 0 wosize in
    { major_out = final_major; fp_out = new_fp; new_addr = new_addr }

let promote_object_oom (minor: minor_state) (major: heap) (obj: U64.t)
                       (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out == 0UL)
          (ensures (let res = promote_object minor major obj fp wosize in
                    res.major_out == major /\ res.fp_out == fp /\ res.new_addr == 0UL)) = ()

let promote_object_success (minor: minor_state) (major: heap) (obj: U64.t)
                           (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires (GC.Spec.Allocator.alloc_spec major fp wosize).obj_out <> 0UL)
          (ensures (let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
                    let res = promote_object minor major obj fp wosize in
                    res.major_out == copy_fields minor alloc_res.heap_out obj alloc_res.obj_out 0 wosize /\
                    res.fp_out == alloc_res.fp_out /\
                    res.new_addr == alloc_res.obj_out)) = ()

/// ---------------------------------------------------------------------------
/// Promote all live objects
/// ---------------------------------------------------------------------------

/// Promote objects from live_set one by one, accumulating results
let rec promote_all_aux (minor: minor_state) (major: heap)
                        (fp: U64.t) (live_set: seq U64.t)
                        (fwd: forwarding_map) (idx: nat)
  : GTot promote_all_result (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then
    { major_final = major; fp_final = fp; fwd_map = fwd }
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      // Skip malformed objects
      promote_all_aux minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then
        // OOM — stop promotion (partial collection)
        { major_final = major; fp_final = fp; fwd_map = fwd }
      else
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux minor res.major_out res.fp_out live_set fwd' (idx + 1)

let promote_all_spec (minor: minor_state) (major: heap)
                     (fp: U64.t) (live_set: seq U64.t)
  : GTot promote_all_result =
  promote_all_aux minor major fp live_set empty_forwarding 0

/// ---------------------------------------------------------------------------
/// Pointer update: rewrite minor-heap pointers in major heap
/// ---------------------------------------------------------------------------

/// Update pointers in a single major-heap object.
/// Iterates fields [i, wosize) and rewrites minor-heap pointers via fwd.
let rec update_object_pointers (major: heap) (obj: U64.t) (wosize: nat)
                               (fwd: forwarding_map) (i: nat)
  : GTot heap (decreases (wosize - i)) =
  if i >= wosize then major
  else
    let field_offset = U64.v obj + i * 8 in
    if field_offset + 8 > heap_size || field_offset % 8 <> 0 then major
    else
      let field_val = read_word major (U64.uint_to_t field_offset) in
      if is_minor_pointer field_val then
        let new_val = fwd field_val in
        if new_val <> 0UL then
          let major' = write_word major (U64.uint_to_t field_offset) new_val in
          update_object_pointers major' obj wosize fwd (i + 1)
        else
          update_object_pointers major obj wosize fwd (i + 1)
      else
        update_object_pointers major obj wosize fwd (i + 1)

/// Unfold lemma: one step of update_object_pointers
let update_object_pointers_step (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
  : Lemma (requires i < wosize /\
                    U64.v obj + i * 8 + 8 <= heap_size /\
                    (U64.v obj + i * 8) % 8 = 0)
          (ensures (let field_offset = U64.v obj + i * 8 in
                    let field_val = read_word major (U64.uint_to_t field_offset) in
                    update_object_pointers major obj wosize fwd i ==
                    (if is_minor_pointer field_val then
                       let new_val = fwd field_val in
                       if new_val <> 0UL then
                         update_object_pointers (write_word major (U64.uint_to_t field_offset) new_val) obj wosize fwd (i + 1)
                       else
                         update_object_pointers major obj wosize fwd (i + 1)
                     else
                       update_object_pointers major obj wosize fwd (i + 1)))) = ()

/// Base case: identity at i >= wosize
let update_object_pointers_done (major: heap) (obj: U64.t) (wosize: nat)
                                (fwd: forwarding_map) (i: nat)
  : Lemma (requires i >= wosize)
          (ensures update_object_pointers major obj wosize fwd i == major) = ()

/// Fold update_object_pointers over a sequence of objects
let rec update_all_objects_aux (major: heap) (objs: seq obj_addr)
                               (fwd: forwarding_map) (idx: nat)
  : GTot heap (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then major
  else
    let obj = Seq.index objs idx in
    let wz = U64.v (wosize_of_object obj major) in
    let major' = update_object_pointers major obj wz fwd 0 in
    update_all_objects_aux major' objs fwd (idx + 1)

/// Update all pointers in the major heap:
/// Walk all objects and rewrite fields that point into the minor heap.
let update_major_pointers (major: heap) (fwd: forwarding_map) : GTot heap =
  update_all_objects_aux major (objects zero_addr major) fwd 0

/// ---------------------------------------------------------------------------
/// Root rewriting
/// ---------------------------------------------------------------------------

let rec rewrite_roots (roots: seq U64.t) (fwd: forwarding_map)
  : GTot (seq U64.t) (decreases (Seq.length roots)) =
  if Seq.length roots = 0 then Seq.empty
  else
    let r = Seq.index roots 0 in
    let new_r = rewrite_root r fwd in
    let rest = Seq.slice roots 1 (Seq.length roots) in
    Seq.cons new_r (rewrite_roots rest fwd)

let rec rewrite_roots_length (roots: seq U64.t) (fwd: forwarding_map)
  : Lemma (ensures Seq.length (rewrite_roots roots fwd) == Seq.length roots)
          (decreases (Seq.length roots)) =
  if Seq.length roots = 0 then ()
  else rewrite_roots_length (Seq.slice roots 1 (Seq.length roots)) fwd

let rec rewrite_roots_index (roots: seq U64.t) (fwd: forwarding_map) (i: nat)
  : Lemma (requires i < Seq.length roots)
          (ensures Seq.index (rewrite_roots roots fwd) i == rewrite_root (Seq.index roots i) fwd)
          (decreases i) =
  if i = 0 then ()
  else rewrite_roots_index (Seq.slice roots 1 (Seq.length roots)) fwd (i - 1)

#push-options "--z3rlimit 200"
let rewrite_roots_pointwise (roots: seq U64.t) (fwd: forwarding_map) (rs2: seq U64.t)
  : Lemma (requires Seq.length rs2 == Seq.length roots /\
                    (forall (j: nat). j < Seq.length roots ==>
                      Seq.index rs2 j == rewrite_root (Seq.index roots j) fwd))
          (ensures rs2 == rewrite_roots roots fwd) =
  rewrite_roots_length roots fwd;
  let rr = rewrite_roots roots fwd in
  assert (Seq.length rr == Seq.length rs2);
  let aux (i: nat{i < Seq.length rs2})
    : Lemma (Seq.index rs2 i == Seq.index rr i) =
    rewrite_roots_index roots fwd i
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_intro rs2 rr
#pop-options

/// ---------------------------------------------------------------------------
/// Full minor collection
/// ---------------------------------------------------------------------------

let minor_collect_spec (minor: minor_state) (major: heap)
                       (fp: U64.t) (roots: seq U64.t)
  : GTot minor_collect_result =
  let live_set = live_set_of minor major roots in
  let prom_res = promote_all_spec minor major fp live_set in
  let updated_major = update_major_pointers prom_res.major_final prom_res.fwd_map in
  let new_roots = rewrite_roots roots prom_res.fwd_map in
  { mc_major = updated_major;
    mc_fp = prom_res.fp_final;
    mc_minor = minor_reset minor;
    mc_roots = new_roots;
    mc_fwd = prom_res.fwd_map }

let minor_collect_spec_unfold (minor: minor_state) (major: heap)
                              (fp: U64.t) (roots: seq U64.t)
  : Lemma (let live_set = live_set_of minor major roots in
           let prom_res = promote_all_spec minor major fp live_set in
           (minor_collect_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_spec minor major fp roots).mc_fp == prom_res.fp_final) = ()

let minor_collect_resets_minor (minor: minor_state) (major: heap)
                               (fp: U64.t) (roots: seq U64.t)
  : Lemma (let res = minor_collect_spec minor major fp roots in
           minor_wf res.mc_minor /\ U64.v res.mc_minor.bump == 0) = ()

let minor_collect_rewrites_roots (minor: minor_state) (major: heap)
                                  (fp: U64.t) (roots: seq U64.t)
  : Lemma (let res = minor_collect_spec minor major fp roots in
           res.mc_roots == rewrite_roots roots res.mc_fwd) = ()

/// ---------------------------------------------------------------------------
/// Correctness lemmas (matching .fsti declaration order)
/// ---------------------------------------------------------------------------

/// copy_fields doesn't modify addresses outside the dst region [dst, dst+(n-1)*8+8).
/// Proved by delegating to the internal copy_fields_preserves_other.
#push-options "--z3rlimit 20 --fuel 2"
let copy_fields_frame
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  (addr: hp_addr)
  : Lemma
    (requires
      dst_fields_valid dst_obj n /\
      U64.v dst_obj % 8 == 0 /\
      (U64.v addr + 8 <= U64.v dst_obj \/
       U64.v addr >= U64.v dst_obj + n * 8))
    (ensures
      read_word (copy_fields minor major src_obj dst_obj i n) addr ==
      read_word major addr) =
  copy_fields_preserves_other minor major src_obj dst_obj i n addr
#pop-options

/// Key lemma: copy_fields correctly copies all fields (starting from index 0).
/// Proved by instantiating the internal copy_fields_preserves for each j.
#push-options "--z3rlimit 20 --fuel 2"
let copy_fields_all_correct
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: U64.t) (n: nat)
  : Lemma
    (requires
      dst_fields_valid dst_obj n /\
      U64.v dst_obj % 8 == 0)
    (ensures
      (let result = copy_fields minor major src_obj dst_obj 0 n in
       (forall (j:nat). j < n ==>
         read_word result (U64.uint_to_t (U64.v dst_obj + j * 8)) ==
         minor_read_field minor src_obj j))) =
  if n = 0 then ()
  else begin
    assert (U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size);
    let rec aux (k: nat)
      : Lemma (requires k <= n)
              (ensures (forall (j:nat). j < k ==>
                (let result = copy_fields minor major src_obj dst_obj 0 n in
                 read_word result (U64.uint_to_t (U64.v dst_obj + j * 8)) ==
                 minor_read_field minor src_obj j)))
              (decreases k) =
      if k = 0 then ()
      else begin
        aux (k - 1);
        copy_fields_preserves minor major src_obj dst_obj 0 n (k - 1)
      end
    in
    aux n
  end
#pop-options

/// After promote_object, if allocation succeeds AND the destination
/// has valid bounds, all field data is preserved.
#push-options "--z3rlimit 20 --fuel 2"
let promote_preserves_fields
  (minor: minor_state) (major: heap) (obj: U64.t)
  (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             U64.v obj >= 8 /\ U64.v obj < minor_heap_size)
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              dst_fields_valid res.new_addr wosize ==>
              U64.v res.new_addr % 8 == 0 ==>
              (forall (j:nat). j < wosize ==>
                read_word res.major_out (U64.uint_to_t (U64.v res.new_addr + j * 8)) ==
                minor_read_field minor obj j))) =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    if U64.v alloc_res.obj_out % 8 = 0 &&
       U64.v alloc_res.obj_out + (wosize - 1) * 8 + 8 <= heap_size then
      copy_fields_all_correct minor alloc_res.heap_out obj alloc_res.obj_out wosize
    else ()
  end
#pop-options

/// ---------------------------------------------------------------------------
/// copy_fields preserves objects walk
/// ---------------------------------------------------------------------------

/// The objects walk is determined by header bytes. copy_fields only writes
/// within an object body [dst_obj, dst_obj + (n-1)*8], never at header positions.
/// Therefore the objects walk is unchanged.
///
/// The library's write_word_preserves_objects requires well_formed_heap, but the
/// proof structure doesn't actually need it. We prove a local version without
/// that requirement, using the same inductive structure.

/// Helper: write at addr < start preserves objects from start.
private let write_before_preserves (start: hp_addr) (g: heap) (addr: hp_addr) (v: U64.t)
  : Lemma (requires U64.v addr < U64.v start /\ U64.v addr % 8 = 0)
          (ensures objects start (write_word g addr v) == objects start g) =
  write_word_preserves_objects_before start g addr v

/// Core proof: writing within an object body preserves the objects walk.
/// Does NOT require well_formed_heap — only membership and bounds.
/// Same proof structure as the library's write_word_preserves_objects_aux.
#push-options "--z3rlimit 1600 --fuel 4 --ifuel 2"
private let rec write_body_preserves_objects_aux
  (start: hp_addr) (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires
      Seq.mem obj (objects start g) /\
      U64.v addr >= U64.v obj /\
      U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
      U64.v addr % 8 = 0)
    (ensures objects start (write_word g addr v) == objects start g)
    (decreases (Seq.length g - U64.v start))
  =
  if U64.v start + 8 >= Seq.length g then ()
  else begin
    let header = read_word g start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
    else begin
      let obj_addr_raw = f_address start in
      f_address_spec start;
      let oa : obj_addr = obj_addr_raw in
      hd_address_spec oa;
      if oa = obj then begin
        // addr >= obj = start + 8, so addr > start, separated
        read_write_different g addr start v;
        if next_start_nat >= heap_size then ()
        else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          wosize_of_object_spec obj g;
          // addr < obj + wosize*8 = (start+8) + wz*8 = start + (wz+1)*8 = next_start
          assert (U64.v addr < next_start_nat);
          write_word_preserves_objects_before next_start g addr v
        end
      end else begin
        if next_start_nat >= heap_size then begin
          mem_cons_lemma obj oa (Seq.empty #obj_addr);
          assert (obj = oa)
        end else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          mem_cons_lemma obj oa (objects next_start g);
          objects_addresses_gt_start start g obj;
          // obj > start, so addr >= obj > start
          read_write_different g addr start v;
          write_body_preserves_objects_aux next_start g obj addr v
        end
      end
    end
  end
#pop-options

/// Top-level: writing within an object body preserves objects from 0.
private let write_body_preserves_objects
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires
      Seq.mem obj (objects 0UL g) /\
      U64.v addr >= U64.v obj /\
      U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
      U64.v addr % 8 = 0)
    (ensures objects 0UL (write_word g addr v) == objects 0UL g) =
  write_body_preserves_objects_aux 0UL g obj addr v


#push-options "--z3rlimit 40 --fuel 1"
let rec copy_fields_preserves_objects_aux
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n)
          (ensures
             objects 0UL (copy_fields minor major src_obj dst_obj i n) == objects 0UL major)
          (decreases (n - i)) =
  if i >= n then ()
  else begin
    let field_val = minor_read_field minor src_obj i in
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then ()
    else begin
      let dst_addr : hp_addr = U64.uint_to_t dst_offset in
      assert (U64.v dst_addr >= U64.v dst_obj);
      assert (U64.v dst_addr < U64.v dst_obj + U64.v (wosize_of_object dst_obj major) * 8);
      // Use our local proof that doesn't require well_formed_heap
      write_body_preserves_objects major dst_obj dst_addr field_val;
      let major' = write_word major dst_addr field_val in
      assert (objects 0UL major' == objects 0UL major);
      // dst_obj is in objects 0UL major' (by objects equality)
      assert (Seq.mem dst_obj (objects 0UL major') = true);
      // wosize preserved: write at dst_obj + i*8 doesn't overlap hd_address(dst_obj)
      let hdr_addr = hd_address dst_obj in
      hd_address_spec dst_obj;
      read_write_different major dst_addr hdr_addr field_val;
      wosize_of_object_spec dst_obj major';
      wosize_of_object_spec dst_obj major;
      assert (wosize_of_object dst_obj major' == wosize_of_object dst_obj major);
      copy_fields_preserves_objects_aux minor major' src_obj dst_obj (i + 1) n
    end
  end
#pop-options

let copy_fields_preserves_objects
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n)
          (ensures
             objects 0UL (copy_fields minor major src_obj dst_obj 0 n) == objects 0UL major) =
  copy_fields_preserves_objects_aux minor major src_obj dst_obj 0 n

/// ---------------------------------------------------------------------------
/// copy_fields preserves fl_valid (free-list validity)
/// ---------------------------------------------------------------------------

/// Key insight: copy_fields writes within dst_obj's body. By objects_separated,
/// these writes don't overlap with any other object's address or header.
/// Since all free-list reads are at other objects (not dst_obj), fl_valid is
/// preserved.

/// Predicate: dst_obj is not reachable from fp via the free-list chain.
let rec not_in_fl_chain (g: heap) (fp: U64.t) (dst_obj: obj_addr) (fuel: nat)
  : Tot prop (decreases fuel)
  = if fuel = 0 then True
    else if fp = 0UL then True
    else if U64.v fp < U64.v mword then True
    else if U64.v fp >= heap_size then True
    else if U64.v fp % U64.v mword <> 0 then True
    else
      fp <> dst_obj /\
      (let next_fp = read_word g (fp <: obj_addr) in
       U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
       not_in_fl_chain g next_fp dst_obj (fuel - 1))

/// Bridge: chain_avoids (bool) implies not_in_fl_chain (prop).
/// chain_avoids checks the same conditions as not_in_fl_chain but returns bool.
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let rec chain_avoids_implies_not_in_fl_chain
  (g: heap) (fp: U64.t) (dst_obj: obj_addr) (fuel: nat)
  : Lemma (requires AllocLemmas.chain_avoids g fp dst_obj fuel = true)
          (ensures not_in_fl_chain g fp dst_obj fuel)
          (decreases fuel)
  = if fuel = 0 then ()
    else if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else begin
      // fp is valid, fuel > 0. Use chain_avoids_head_ne to get fp <> dst_obj.
      AllocLemmas.chain_avoids_head_ne g fp dst_obj fuel;
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 <= heap_size then begin
        let next_fp = read_word g (fp <: obj_addr) in
        // Decompose: chain_avoids g next_fp dst_obj (fuel-1) = true
        AllocLemmas.chain_avoids_tail g fp dst_obj fuel;
        chain_avoids_implies_not_in_fl_chain g next_fp dst_obj (fuel - 1)
      end else ()
    end
#pop-options

/// Helper: write within dst_obj's body preserves fl_valid for a chain
/// that does not contain dst_obj.
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
private let rec write_body_preserves_fl_valid_aux
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects 0UL g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel)
    (ensures AllocLemmas.fl_valid (write_word g addr v) fp fuel)
    (decreases fuel)
  =
  if fuel = 0 then AllocLemmas.fl_valid_zero (write_word g addr v) fp
  else if fp = 0UL then AllocLemmas.fl_valid_terminal (write_word g addr v) fp fuel
  else if U64.v fp < U64.v mword then AllocLemmas.fl_valid_terminal (write_word g addr v) fp fuel
  else if U64.v fp >= heap_size then AllocLemmas.fl_valid_terminal (write_word g addr v) fp fuel
  else if U64.v fp % U64.v mword <> 0 then AllocLemmas.fl_valid_terminal (write_word g addr v) fp fuel
  else begin
    // fp is a valid free-list node, and fp <> dst_obj (from not_in_fl_chain)
    assert (fp <> dst_obj);
    let fp_obj : obj_addr = fp in
    AllocLemmas.fl_valid_elim g fp fuel;
    // Show writes at addr don't overlap with reads at fp and hd_address fp
    if U64.v dst_obj < U64.v fp then begin
      objects_separated 0UL g dst_obj fp_obj;
      wosize_of_object_spec dst_obj g;
      hd_address_spec fp_obj;
      read_write_different g addr (fp <: hp_addr) v;
      read_write_different g addr (hd_address fp_obj) v
    end else begin
      objects_separated 0UL g fp_obj dst_obj;
      wosize_of_object_spec fp_obj g;
      hd_address_spec fp_obj;
      read_write_different g addr (fp <: hp_addr) v;
      read_write_different g addr (hd_address fp_obj) v
    end;
    // objects and wosize preserved
    write_body_preserves_objects g dst_obj addr v;
    wosize_of_object_spec fp_obj g;
    wosize_of_object_spec fp_obj (write_word g addr v);
    // Recurse on next node
    let g' = write_word g addr v in
    let hd = hd_address fp_obj in
    if U64.v hd + 16 <= heap_size then begin
      let next_fp = read_word g fp_obj in
      // read_word g' fp_obj == read_word g fp_obj (write didn't touch fp)
      assert (read_word g' fp_obj == next_fp);
      // not_in_fl_chain gives: not_in_fl_chain g next_fp dst_obj (fuel-1)
      // fl_valid gives: fl_valid g next_fp (fuel-1)
      // But we need fl_valid/not_in_fl_chain with respect to g, not g'.
      // Since read_word g fp == read_word g' fp (proven above), the next_fp is the same.
      // For the recursive fl_valid/not_in_fl_chain: they read from g at addresses
      // in the chain (all ≠ dst_obj), so the reads are unchanged.
      write_body_preserves_fl_valid_aux g dst_obj addr v next_fp (fuel - 1);
      AllocLemmas.fl_valid_step g' fp fuel
    end else begin
      AllocLemmas.fl_valid_step g' fp fuel
    end
  end
#pop-options

/// Helper: write within dst_obj's body preserves not_in_fl_chain.
/// Same separation argument: all chain reads are at addresses ≠ dst_obj's body.
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
private let rec write_body_preserves_not_in_fl_chain
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects 0UL g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel)
    (ensures not_in_fl_chain (write_word g addr v) fp dst_obj fuel)
    (decreases fuel)
  =
  if fuel = 0 then ()
  else if fp = 0UL then ()
  else if U64.v fp < U64.v mword then ()
  else if U64.v fp >= heap_size then ()
  else if U64.v fp % U64.v mword <> 0 then ()
  else begin
    assert (fp <> dst_obj);
    let fp_obj : obj_addr = fp in
    AllocLemmas.fl_valid_elim g fp fuel;
    // Show read_word g' fp == read_word g fp (write doesn't touch fp)
    if U64.v dst_obj < U64.v fp then begin
      objects_separated 0UL g dst_obj fp_obj;
      wosize_of_object_spec dst_obj g;
      read_write_different g addr (fp <: hp_addr) v
    end else begin
      objects_separated 0UL g fp_obj dst_obj;
      wosize_of_object_spec fp_obj g;
      read_write_different g addr (fp <: hp_addr) v
    end;
    let g' = write_word g addr v in
    let hd = hd_address fp_obj in
    hd_address_spec fp_obj;
    if U64.v hd + 16 <= heap_size then begin
      let next_fp = read_word g fp_obj in
      assert (read_word g' fp_obj == next_fp);
      write_body_preserves_not_in_fl_chain g dst_obj addr v next_fp (fuel - 1)
    end else ()
  end
#pop-options
private let rec copy_fields_preserves_fl_valid_aux
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             not_in_fl_chain major fp dst_obj fuel)
          (ensures
             AllocLemmas.fl_valid (copy_fields minor major src_obj dst_obj i n) fp fuel)
          (decreases (n - i)) =
  if i >= n then ()
  else begin
    let field_val = minor_read_field minor src_obj i in
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then ()
    else begin
      let dst_addr : hp_addr = U64.uint_to_t dst_offset in
      write_body_preserves_fl_valid_aux major dst_obj dst_addr field_val fp fuel;
      let major' = write_word major dst_addr field_val in
      // For the recursive call: need dst_obj ∈ objects, wosize preserved,
      // not_in_fl_chain in major'
      write_body_preserves_objects major dst_obj dst_addr field_val;
      assert (objects 0UL major' == objects 0UL major);
      hd_address_spec dst_obj;
      read_write_different major dst_addr (hd_address dst_obj) field_val;
      wosize_of_object_spec dst_obj major';
      wosize_of_object_spec dst_obj major;
      // not_in_fl_chain preserved: chain reads are unchanged (separation)
      write_body_preserves_not_in_fl_chain major dst_obj dst_addr field_val fp fuel;
      copy_fields_preserves_fl_valid_aux minor major' src_obj dst_obj (i + 1) n fp fuel
    end
  end

/// Helper: write within dst_obj's body preserves fl_chain_terminates.
/// Same separation argument as fl_valid and not_in_fl_chain.
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
private let rec write_body_preserves_fl_chain_terminates
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects 0UL g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_chain_terminates g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel /\
      AllocLemmas.fl_valid g fp fuel)
    (ensures AllocLemmas.fl_chain_terminates (write_word g addr v) fp fuel)
    (decreases fuel)
  =
  if fp = 0UL then AllocLemmas.fl_chain_terminates_terminal (write_word g addr v) fp fuel
  else if U64.v fp < U64.v mword then AllocLemmas.fl_chain_terminates_terminal (write_word g addr v) fp fuel
  else if U64.v fp >= heap_size then AllocLemmas.fl_chain_terminates_terminal (write_word g addr v) fp fuel
  else if U64.v fp % U64.v mword <> 0 then AllocLemmas.fl_chain_terminates_terminal (write_word g addr v) fp fuel
  else if fuel = 0 then begin
    // fp is valid but fuel = 0 → fl_chain_terminates g fp 0 = false, contradicts precondition
    AllocLemmas.fl_chain_terminates_valid_zero g fp
  end
  else begin
    // fuel > 0, fp valid+aligned: not_in_fl_chain unfolds to fp <> dst_obj /\ ...
    assert (fp <> dst_obj);
    let fp_obj : obj_addr = fp in
    AllocLemmas.fl_valid_elim g fp fuel;
    // Show read at fp is unchanged by write at addr
    if U64.v dst_obj < U64.v fp then begin
      objects_separated 0UL g dst_obj fp_obj;
      wosize_of_object_spec dst_obj g;
      read_write_different g addr (fp <: hp_addr) v
    end else begin
      objects_separated 0UL g fp_obj dst_obj;
      wosize_of_object_spec fp_obj g;
      read_write_different g addr (fp <: hp_addr) v
    end;
    let g' = write_word g addr v in
    let hd = hd_address fp_obj in
    hd_address_spec fp_obj;
    if U64.v hd + 16 > heap_size then
      AllocLemmas.fl_chain_terminates_terminal g' fp fuel
    else begin
      let next_fp = read_word g fp_obj in
      assert (read_word g' fp_obj == next_fp);
      AllocLemmas.fl_chain_terminates_elim g fp fuel;
      write_body_preserves_fl_chain_terminates g dst_obj addr v next_fp (fuel - 1);
      AllocLemmas.fl_chain_terminates_step g' fp fuel
    end
  end
#pop-options

/// copy_fields preserves fl_chain_terminates when dst_obj is not in the chain.
private let rec copy_fields_preserves_fl_chain_terminates
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             AllocLemmas.fl_chain_terminates major fp fuel /\
             not_in_fl_chain major fp dst_obj fuel)
          (ensures
             AllocLemmas.fl_chain_terminates (copy_fields minor major src_obj dst_obj i n) fp fuel)
          (decreases (n - i)) =
  if i >= n then ()
  else begin
    let field_val = minor_read_field minor src_obj i in
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then ()
    else begin
      let dst_addr : hp_addr = U64.uint_to_t dst_offset in
      write_body_preserves_fl_chain_terminates major dst_obj dst_addr field_val fp fuel;
      let major' = write_word major dst_addr field_val in
      write_body_preserves_objects major dst_obj dst_addr field_val;
      hd_address_spec dst_obj;
      read_write_different major dst_addr (hd_address dst_obj) field_val;
      wosize_of_object_spec dst_obj major';
      wosize_of_object_spec dst_obj major;
      write_body_preserves_not_in_fl_chain major dst_obj dst_addr field_val fp fuel;
      write_body_preserves_fl_valid_aux major dst_obj dst_addr field_val fp fuel;
      copy_fields_preserves_fl_chain_terminates minor major' src_obj dst_obj (i + 1) n fp fuel
    end
  end

/// Helper: write within dst_obj's body preserves chain_avoids for dst_obj itself.
/// Chain walk reads link fields at chain nodes ≠ dst_obj (separation argument).
#push-options "--z3rlimit 400 --fuel 2 --ifuel 1 --split_queries no"
private let write_body_preserves_chain_avoids_self
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects 0UL g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      AllocLemmas.chain_avoids g fp dst_obj fuel = true)
    (ensures AllocLemmas.chain_avoids (write_word g addr v) fp dst_obj fuel = true)
  = let g' = write_word g addr v in
    // For chain_avoids_transfer: need read_word g' a == read_word g a for all objects a ≠ dst_obj
    let aux (a: obj_addr) : Lemma
      (requires Seq.mem a (objects 0UL g) /\
               U64.v (wosize_of_object a g) >= 1 /\
               U64.v (hd_address a) + 16 <= heap_size /\
               a <> dst_obj)
      (ensures read_word g' a == read_word g a)
    = hd_address_spec a;
      hd_address_spec dst_obj;
      wosize_of_object_spec dst_obj g;
      if U64.v a < U64.v dst_obj then begin
        objects_separated 0UL g a dst_obj;
        // a + wosize_a*8 < dst_obj (strict), and addr >= dst_obj, so addr > a
        // Also a < dst_obj <= addr, so addr ≠ a is trivial
        read_write_different g addr (a <: hp_addr) v
      end else begin
        objects_separated 0UL g dst_obj a;
        // a > dst_obj + wosize_dst*8, and addr < dst_obj + wosize_dst*8, so addr < a
        read_write_different g addr (a <: hp_addr) v
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    // objects are preserved through write_word in body
    write_body_preserves_objects g dst_obj addr v;
    AllocLemmas.chain_avoids_transfer g g' fp dst_obj fuel
#pop-options

/// copy_fields preserves chain_avoids for dst_obj itself.
private let rec copy_fields_preserves_chain_avoids_self
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             AllocLemmas.chain_avoids major fp dst_obj fuel = true)
          (ensures
             AllocLemmas.chain_avoids (copy_fields minor major src_obj dst_obj i n) fp dst_obj fuel = true)
          (decreases (n - i)) =
  if i >= n then ()
  else begin
    let field_val = minor_read_field minor src_obj i in
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then ()
    else begin
      let dst_addr : hp_addr = U64.uint_to_t dst_offset in
      chain_avoids_implies_not_in_fl_chain major fp dst_obj fuel;
      write_body_preserves_chain_avoids_self major dst_obj dst_addr field_val fp fuel;
      let major' = write_word major dst_addr field_val in
      write_body_preserves_objects major dst_obj dst_addr field_val;
      hd_address_spec dst_obj;
      read_write_different major dst_addr (hd_address dst_obj) field_val;
      wosize_of_object_spec dst_obj major';
      wosize_of_object_spec dst_obj major;
      write_body_preserves_not_in_fl_chain major dst_obj dst_addr field_val fp fuel;
      write_body_preserves_fl_valid_aux major dst_obj dst_addr field_val fp fuel;
      copy_fields_preserves_chain_avoids_self minor major' src_obj dst_obj (i + 1) n fp fuel
    end
  end

#push-options "--z3rlimit 40 --fuel 1"
let promote_object_preserves_objects
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              (forall (x: obj_addr). Seq.mem x (objects 0UL major) ==>
                Seq.mem x (objects 0UL res.major_out)))) =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    // After alloc: old objects are preserved
    AllocLemmas.alloc_spec_preserves_objects major fp wosize;
    // The newly allocated object is in the objects walk
    // alloc_spec_preserves_wf gives well_formed_heap for the post-alloc heap
    AllocLemmas.alloc_spec_preserves_wf major fp wosize;
    // alloc_res.obj_out is a valid obj_addr (from allocator guards)
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    // obj_out is in objects of the output heap
    GC.Gen.AllocProps.alloc_spec_obj_in_objects major fp wosize;
    // wosize of obj_out in output heap >= requested wosize
    GC.Gen.AllocProps.alloc_spec_obj_wosize major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_objects minor alloc_res.heap_out obj dst_obj wosize;
    assert (objects 0UL (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects 0UL alloc_res.heap_out)
  end
#pop-options

/// copy_fields preserves well_formed_heap_part1: since copy_fields only writes
/// to fields (not headers), the objects walk and size bounds are unchanged.
/// Proof: objects are the same (proven), Seq.length is preserved (write_word doesn't
/// change length), and wosize_of_object reads the header which copy_fields doesn't touch.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
private let copy_fields_preserves_wfh_part1
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             n > 0)
          (ensures
             well_formed_heap_part1 (copy_fields minor major src_obj dst_obj 0 n)) =
  let g' = copy_fields minor major src_obj dst_obj 0 n in
  copy_fields_preserves_objects_aux minor major src_obj dst_obj 0 n;
  assert (objects 0UL g' == objects 0UL major);
  // For wfh_part1 we need: for all h in objects(0, g'),
  //   hd_address h + 8 + wosize_of_object h g' * 8 <= Seq.length g'
  // We show wosize_of_object h g' == wosize_of_object h major by showing
  // copy_fields doesn't modify hd_address(h) for any h in objects.
  let wz_dst = U64.v (wosize_of_object dst_obj major) in
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects 0UL major))
    (ensures U64.v (hd_address h) + 8 + U64.v (wosize_of_object h g') * 8 <= Seq.length g')
  = let hdr_addr = hd_address h in
    hd_address_spec h;
    hd_address_spec dst_obj;
    // Need: read_word g' hdr_addr == read_word major hdr_addr
    // i.e., copy_fields doesn't write at hdr_addr = h - 8
    // copy_fields writes at dst_obj + k*8 for k in [0, n)
    // All writes are within [dst_obj, dst_obj + (n-1)*8], i.e., >= dst_obj
    // hdr_addr = h - 8
    // Case h = dst_obj: hdr_addr = dst_obj - 8 < dst_obj. First write is at dst_obj.
    //   So hdr_addr + 8 = dst_obj <= dst_obj + k*8 for all k >= 0.
    // Case h ≠ dst_obj, h < dst_obj: both 8-aligned, so h <= dst_obj - 8.
    //   hdr_addr = h - 8 <= dst_obj - 16 < dst_obj. So hdr_addr + 8 <= dst_obj - 8 < dst_obj <= dst_obj + k*8.
    // Case h > dst_obj: by objects_separated, h > dst_obj + wz_dst * 8.
    //   Both 8-aligned, so h >= dst_obj + wz_dst * 8 + 8 >= dst_obj + n*8 + 8.
    //   hdr_addr = h - 8 >= dst_obj + n*8. For k < n: dst_obj + k*8 + 8 <= dst_obj + (n-1)*8 + 8 = dst_obj + n*8 <= hdr_addr.
    if U64.v h > U64.v dst_obj then begin
      objects_separated 0UL major dst_obj h;
      wosize_of_object_spec dst_obj major;
      assert (U64.v h > U64.v dst_obj + wz_dst * 8)
    end else if U64.v h < U64.v dst_obj then begin
      ()
    end else begin
      // h = dst_obj
      ()
    end;
    // In all cases: for all k in [0, n), hdr_addr doesn't overlap dst_obj + k*8
    assert (forall (k:nat). 0 <= k /\ k < n ==>
      (U64.v hdr_addr + 8 <= U64.v dst_obj + k * 8 \/ U64.v dst_obj + k * 8 + 8 <= U64.v hdr_addr));
    // wfh_part1 bound check: need n > 0 for the copy_fields_preserves_other precondition
    assert (U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size);
    copy_fields_preserves_other minor major src_obj dst_obj 0 n hdr_addr;
    assert (read_word g' hdr_addr == read_word major hdr_addr);
    wosize_of_object_spec h g';
    wosize_of_object_spec h major;
    assert (wosize_of_object h g' == wosize_of_object h major)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Composite lemma: copy_fields preserves all allocator invariants together.
/// Uses chain_avoids (bool) from the allocator, avoiding the need to export not_in_fl_chain.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let copy_fields_preserves_alloc_invariants
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat{n > 0})
  (fp: U64.t)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             AllocLemmas.chain_avoids major fp dst_obj (heap_size / U64.v mword) = true)
           (ensures (let g' = copy_fields minor major src_obj dst_obj 0 n in
                     well_formed_heap_part1 g' /\
                     AllocLemmas.fl_valid g' fp (heap_size / U64.v mword) /\
                     AllocLemmas.fl_chain_terminates g' fp (heap_size / U64.v mword)))
  = let fuel = heap_size / U64.v mword in
    chain_avoids_implies_not_in_fl_chain major fp dst_obj fuel;
    copy_fields_preserves_wfh_part1 minor major src_obj dst_obj n;
    copy_fields_preserves_fl_valid_aux minor major src_obj dst_obj 0 n fp fuel;
    copy_fields_preserves_fl_chain_terminates minor major src_obj dst_obj 0 n fp fuel
#pop-options

/// promote_object preserves objects (part1 version — no full well_formed_heap needed)
#push-options "--z3rlimit 40 --fuel 1"
private let promote_object_preserves_objects_part1
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              (forall (x: obj_addr). Seq.mem x (objects 0UL major) ==>
                Seq.mem x (objects 0UL res.major_out)))) =
  let fuel = heap_size / U64.v mword in
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    // After alloc: old objects are preserved (part1 version)
    AllocLemmas.alloc_spec_preserves_objects_part1 major fp wosize;
    // obj_out is a valid obj_addr
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    // obj_out is in objects of the output heap (part1 version)
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    // wosize of obj_out >= requested (no wfh needed)
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
    assert (objects 0UL (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects 0UL alloc_res.heap_out)
  end
#pop-options

#push-options "--z3rlimit 200 --fuel 1 --split_queries always"
let rec promote_all_aux_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_aux minor major fp live_set fwd idx in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.major_final))))
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      promote_all_aux_preserves_objects minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then ()
      else begin
        let fuel = heap_size / U64.v mword in
        promote_object_preserves_objects_part1 minor major obj fp wz;
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        // alloc_res.obj_out is a valid obj_addr (from allocator guards)
        GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        // After alloc: fl_valid for the post-alloc heap
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        // After alloc: obj_out is in objects and has sufficient wosize (part1)
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        // Key allocator property: alloc removes obj_out from the chain.
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        // fl_chain_terminates after alloc
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        // copy_fields preserves fl_valid
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        // copy_fields preserves fl_chain_terminates
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        assert (AllocLemmas.fl_valid res.major_out res.fp_out fuel);
        assert (AllocLemmas.fl_chain_terminates res.major_out res.fp_out fuel);
        // copy_fields preserves well_formed_heap_part1
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        assert (well_formed_heap_part1 res.major_out);
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux_preserves_objects minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
#pop-options

let promote_all_preserves_objects
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
                      Seq.mem x (objects zero_addr res.major_final)))) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_aux_preserves_objects minor major fp live_set empty_forwarding 0

/// promote_all preserves well_formed_heap_part1
#push-options "--z3rlimit 200 --fuel 1 --split_queries always"
let rec promote_all_aux_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (promote_all_aux minor major fp live_set fwd idx).major_final)
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      promote_all_aux_preserves_wfh_part1 minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then ()
      else begin
        let fuel = heap_size / U64.v mword in
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        assert (well_formed_heap_part1 res.major_out);
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux_preserves_wfh_part1 minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
#pop-options

/// Top-level: promote_all_spec preserves well_formed_heap_part1
let promote_all_preserves_wfh_part1
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part1 (promote_all_spec minor major fp live_set).major_final) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_aux_preserves_wfh_part1 minor major fp live_set empty_forwarding 0

/// copy_fields preserves well_formed_heap_part4 (no infix objects).
/// Since copy_fields only writes to field addresses (>= dst_obj), no headers change.
#push-options "--z3rlimit 40 --fuel 0 --split_queries always"
private let copy_fields_preserves_wfh_part4
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             well_formed_heap_part1 major /\
             well_formed_heap_part4 major /\
             Seq.mem dst_obj (objects 0UL major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             n > 0)
          (ensures
             well_formed_heap_part4 (copy_fields minor major src_obj dst_obj 0 n)) =
  let g' = copy_fields minor major src_obj dst_obj 0 n in
  copy_fields_preserves_objects_aux minor major src_obj dst_obj 0 n;
  assert (objects 0UL g' == objects 0UL major);
  let wz_dst = U64.v (wosize_of_object dst_obj major) in
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects 0UL major))
    (ensures ~(GC.Spec.Object.is_infix h g'))
  = let hdr_addr = hd_address h in
    hd_address_spec h;
    hd_address_spec dst_obj;
    if U64.v h > U64.v dst_obj then begin
      objects_separated 0UL major dst_obj h;
      wosize_of_object_spec dst_obj major
    end else ();
    assert (forall (k:nat). 0 <= k /\ k < n ==>
      (U64.v hdr_addr + 8 <= U64.v dst_obj + k * 8 \/ U64.v dst_obj + k * 8 + 8 <= U64.v hdr_addr));
    assert (U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size);
    copy_fields_preserves_other minor major src_obj dst_obj 0 n hdr_addr;
    GC.Spec.Object.tag_of_object_spec h g';
    GC.Spec.Object.tag_of_object_spec h major;
    GC.Spec.Object.is_infix_spec h g';
    GC.Spec.Object.is_infix_spec h major
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// promote_all_aux preserves well_formed_heap_part4 (no infix objects).
#push-options "--z3rlimit 200 --fuel 1 --split_queries always"
let rec promote_all_aux_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    well_formed_heap_part4 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part4 (promote_all_aux minor major fp live_set fwd idx).major_final)
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      promote_all_aux_preserves_wfh_part4 minor major fp live_set fwd (idx + 1)
    else
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then ()
      else begin
        let fuel = heap_size / U64.v mword in
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        // alloc preserves part1 and part4
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        AllocLemmas.alloc_spec_preserves_wfh_part4 major fp wz;
        // copy_fields preserves part1 and part4
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        copy_fields_preserves_wfh_part4 minor alloc_res.heap_out obj dst_obj wz;
        assert (well_formed_heap_part1 res.major_out);
        assert (well_formed_heap_part4 res.major_out);
        let fwd' = extend_forwarding fwd obj res.new_addr in
        promote_all_aux_preserves_wfh_part4 minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
#pop-options

/// Top-level: promote_all_spec preserves well_formed_heap_part4
let promote_all_preserves_wfh_part4
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures well_formed_heap_part4 (promote_all_spec minor major fp live_set).major_final) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  promote_all_aux_preserves_wfh_part4 minor major fp live_set empty_forwarding 0


/// ---------------------------------------------------------------------------
/// Pointer update preserves objects
/// ---------------------------------------------------------------------------

/// update_object_pointers writes only within the body of `obj`, so
/// the objects walk is unchanged.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_preserves_objects
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat)
  : Lemma (requires
      Seq.mem obj (objects 0UL major) /\
      U64.v obj % 8 == 0 /\
      wosize == U64.v (wosize_of_object obj major) /\
      (forall (j:nat). j < wosize ==>
        (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0)))
    (ensures objects 0UL (update_object_pointers major obj wosize fwd i) == objects 0UL major)
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
      Seq.mem obj (objects 0UL major) /\
      Seq.mem other (objects 0UL major) /\
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
      Seq.mem obj (objects 0UL major) /\
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
      Seq.mem obj (objects 0UL major) /\
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
      Seq.mem obj (objects 0UL major) /\
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

#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_preserves_objects
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major)
    (ensures objects zero_addr (update_all_objects_aux major objs fwd idx) == objs)
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    let wz = U64.v (wosize_of_object obj major) in
    // From well_formed_heap_part1: field bounds for obj
    hd_address_spec obj;
    assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
    assert (forall (j:nat). j < wz ==>
      (U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 == 0));
    // Step 1: update_object_pointers preserves objects list
    update_object_pointers_preserves_objects major obj wz fwd 0;
    let major' = update_object_pointers major obj wz fwd 0 in
    assert (objects zero_addr major' == objs);
    // Step 2: show well_formed_heap_part1 major' (all headers unchanged)
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = obj then begin
        update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else if U64.v h > U64.v obj then begin
        update_object_pointers_preserves_other_header major obj wz fwd 0 h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        // h < obj: hd_address(h) = h - 8 < h < obj, so it's below obj
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
        wosize_of_object_spec h major;
        wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    assert (well_formed_heap_part1 major');
    // Step 3: recurse
    update_all_objects_aux_preserves_objects major' objs fwd (idx + 1)
  end
#pop-options

/// update_major_pointers preserves the objects walk.
let update_major_pointers_preserves_objects (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures objects zero_addr (update_major_pointers major fwd) == objects zero_addr major) =
  update_all_objects_aux_preserves_objects major (objects zero_addr major) fwd 0

/// update_all_objects_aux preserves well_formed_heap_part1 (inductive).
/// Each step: update_object_pointers preserves all headers → preserves wfh_part1.
#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_preserves_wfh_part1
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major)
    (ensures well_formed_heap_part1 (update_all_objects_aux major objs fwd idx))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    let wz = U64.v (wosize_of_object obj major) in
    hd_address_spec obj;
    assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
    // update_object_pointers preserves objects list
    update_object_pointers_preserves_objects major obj wz fwd 0;
    let major' = update_object_pointers major obj wz fwd 0 in
    assert (objects zero_addr major' == objs);
    // Prove wfh_part1 of major' (same structure as in preserves_objects)
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = obj then begin
        update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else if U64.v h > U64.v obj then begin
        update_object_pointers_preserves_other_header major obj wz fwd 0 h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
        wosize_of_object_spec h major;
        wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    assert (well_formed_heap_part1 major');
    // Recurse
    update_all_objects_aux_preserves_wfh_part1 major' objs fwd (idx + 1)
  end
#pop-options

/// update_major_pointers preserves well_formed_heap_part1.
let update_major_pointers_preserves_wfh_part1 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major)
    (ensures well_formed_heap_part1 (update_major_pointers major fwd)) =
  update_all_objects_aux_preserves_wfh_part1 major (objects zero_addr major) fwd 0

/// ---------------------------------------------------------------------------
/// update_major_pointers preserves headers (tag, wosize, color)
/// ---------------------------------------------------------------------------

/// Inductive: update_all_objects_aux preserves the header word of any object.
#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_preserves_header
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map) (idx: nat) (h: obj_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem h objs)
    (ensures read_word (update_all_objects_aux major objs fwd idx) (hd_address h) ==
             read_word major (hd_address h))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let obj = Seq.index objs idx in
    assert (Seq.mem obj objs);
    let wz = U64.v (wosize_of_object obj major) in
    hd_address_spec obj;
    assert (U64.v (hd_address obj) + 8 + (wz * 8) <= Seq.length major);
    update_object_pointers_preserves_objects major obj wz fwd 0;
    let major' = update_object_pointers major obj wz fwd 0 in
    assert (objects zero_addr major' == objs);
    // Show header of h is preserved through this step
    hd_address_spec h;
    if h = obj then
      update_object_pointers_preserves_self_header major obj wz fwd 0
    else if U64.v h > U64.v obj then
      update_object_pointers_preserves_other_header major obj wz fwd 0 h
    else
      update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
    assert (read_word major' (hd_address h) == read_word major (hd_address h));
    // Establish wfh_part1 for major' (needed for recursive call)
    let aux_wfh (x: obj_addr) : Lemma
      (requires Seq.mem x (objects 0UL major'))
      (ensures U64.v (hd_address x) + 8 + (U64.v (wosize_of_object x major') * 8) <= Seq.length major')
    = hd_address_spec x;
      if x = obj then begin
        update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec x major'; wosize_of_object_spec x major
      end else if U64.v x > U64.v obj then begin
        update_object_pointers_preserves_other_header major obj wz fwd 0 x;
        wosize_of_object_spec x major'; wosize_of_object_spec x major
      end else begin
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address x);
        wosize_of_object_spec x major; wosize_of_object_spec x major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    assert (well_formed_heap_part1 major');
    // Recurse
    update_all_objects_aux_preserves_header major' objs fwd (idx + 1) h
  end
#pop-options

/// update_major_pointers preserves the header word of any object in the objects list.
let update_major_pointers_preserves_header (major: heap) (fwd: forwarding_map) (h: obj_addr)
  : Lemma (requires well_formed_heap_part1 major /\ Seq.mem h (objects 0UL major))
    (ensures read_word (update_major_pointers major fwd) (hd_address h) ==
             read_word major (hd_address h)) =
  update_all_objects_aux_preserves_header major (objects zero_addr major) fwd 0 h

/// update_major_pointers preserves well_formed_heap_part4 (no infix objects).
#push-options "--z3rlimit 20"
let update_major_pointers_preserves_wfh_part4 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part4 (update_major_pointers major fwd)) =
  update_major_pointers_preserves_objects major fwd;
  let mc = update_major_pointers major fwd in
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects 0UL mc))
    (ensures ~(GC.Spec.Object.is_infix h mc))
  = update_major_pointers_preserves_header major fwd h;
    GC.Spec.Object.tag_of_object_spec h mc;
    GC.Spec.Object.tag_of_object_spec h major;
    GC.Spec.Object.is_infix_spec h mc;
    GC.Spec.Object.is_infix_spec h major
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// update_major_pointers preserves well_formed_heap_part3 (infix well-formedness).
/// Since part4 holds (no objects are infix), infix_wf is vacuously true.
#push-options "--z3rlimit 20"
let update_major_pointers_preserves_wfh_part3 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\ well_formed_heap_part4 major)
    (ensures well_formed_heap_part3 (update_major_pointers major fwd)) =
  update_major_pointers_preserves_wfh_part4 major fwd;
  update_major_pointers_preserves_objects major fwd;
  let mc = update_major_pointers major fwd in
  let pf (h: obj_addr) : Lemma
    (requires Seq.mem h (objects 0UL mc) /\ GC.Spec.Object.is_infix h mc)
    (ensures (let p = GC.Spec.Object.parent_closure_addr_nat h mc in
              p >= 8 /\ p < heap_size /\ p % 8 == 0 /\
              Seq.mem (U64.uint_to_t p) (objects 0UL mc) /\
              GC.Spec.Object.is_closure (U64.uint_to_t p) mc))
  = // part4 says ~(is_infix h mc), contradiction
    assert (well_formed_heap_part4 mc);
    assert (Seq.mem h (objects 0UL mc) ==> ~(GC.Spec.Object.is_infix h mc))
  in
  GC.Spec.Object.infix_wf_intro mc (objects 0UL mc) pf
#pop-options

/// ---------------------------------------------------------------------------
/// Promoted objects land in the final major heap's objects list
/// ---------------------------------------------------------------------------

/// After promote_object succeeds (new_addr ≠ 0), new_addr ∈ objects(result).
#push-options "--z3rlimit 40 --fuel 1"
private let promote_object_adds_new_addr
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wosize: nat{wosize > 0})
  : Lemma (requires
             well_formed_heap_part1 major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures
             (let res = promote_object minor major obj fp wosize in
              res.new_addr <> 0UL ==>
              (U64.v res.new_addr >= U64.v mword /\
               U64.v res.new_addr < heap_size /\
               U64.v res.new_addr % U64.v mword == 0 /\
               Seq.mem (res.new_addr <: obj_addr) (objects zero_addr res.major_out)))) =
  let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
  if alloc_res.obj_out = 0UL then ()
  else begin
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_objects_aux minor alloc_res.heap_out obj dst_obj 0 wosize;
    assert (objects 0UL (copy_fields minor alloc_res.heap_out obj dst_obj 0 wosize) ==
            objects 0UL alloc_res.heap_out)
  end
#pop-options

/// fwd_all_targets_valid implies fwd_targets_in_objects (for any idx)
let fwd_all_implies_positional (fwd: forwarding_map) (live_set: seq U64.t) (idx: nat) (g: heap)
  : Lemma (requires fwd_all_targets_valid fwd g)
          (ensures fwd_targets_in_objects fwd live_set idx g) = ()

/// The core induction: promote_all_aux puts every forwarded address into objects of the final heap.
/// Uses the simpler fwd_all_targets_valid invariant.
#push-options "--z3rlimit 200 --fuel 1 --split_queries always"
let rec promote_all_aux_adds_promoted
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    fwd_all_targets_valid fwd major)
          (ensures (let res = promote_all_aux minor major fp live_set fwd idx in
                    fwd_all_targets_valid res.fwd_map res.major_final))
          (decreases (Seq.length live_set - idx)) =
  if idx >= Seq.length live_set then ()
  else
    let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    if wz = 0 then
      // Skip: fwd unchanged, heap unchanged — invariant trivially preserved
      promote_all_aux_adds_promoted minor major fp live_set fwd (idx + 1)
    else begin
      let res = promote_object minor major obj fp wz in
      if res.new_addr = 0UL then
        // OOM: fwd unchanged, heap unchanged — invariant trivially preserved
        ()
      else begin
        let fuel = heap_size / U64.v mword in
        // new_addr is in objects of res.major_out
        promote_object_adds_new_addr minor major obj fp wz;
        // existing objects persist
        promote_object_preserves_objects_part1 minor major obj fp wz;
        // allocator properties for recursion
        let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
        GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
        let dst_obj : obj_addr = alloc_res.obj_out in
        AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
        GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
        AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
        chain_avoids_implies_not_in_fl_chain alloc_res.heap_out alloc_res.fp_out dst_obj fuel;
        AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
        copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
        AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
        copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
        // fwd' extends fwd with obj -> new_addr
        let fwd' = extend_forwarding fwd obj res.new_addr in
        // Show fwd_all_targets_valid fwd' res.major_out:
        // For x ≠ obj: fwd'(x) = fwd(x), target in objects(major) ⊆ objects(res.major_out) ✓
        // For x = obj: fwd'(obj) = new_addr, which is in objects(res.major_out) ✓
        assert (fwd_all_targets_valid fwd' res.major_out);
        promote_all_aux_adds_promoted minor res.major_out res.fp_out live_set fwd' (idx + 1)
      end
    end
#pop-options

/// Top-level: promote_all_spec produces fwd_all_targets_valid for its final heap.
let promote_all_fwd_all_targets_valid
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_all_targets_valid res.fwd_map res.major_final)) =
  reveal_opaque (`%well_formed_heap) well_formed_heap;
  assert (fwd_all_targets_valid empty_forwarding major);
  promote_all_aux_adds_promoted minor major fp live_set empty_forwarding 0

/// Top-level: after promote_all_spec, every forwarded object's address is in objects of the final heap.
let promote_all_adds_promoted
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fwd_targets_in_objects res.fwd_map live_set (Seq.length live_set) res.major_final)) =
  promote_all_fwd_all_targets_valid minor major fp live_set;
  let res = promote_all_spec minor major fp live_set in
  fwd_all_implies_positional res.fwd_map live_set (Seq.length live_set) res.major_final

/// ---------------------------------------------------------------------------
/// Minor collection correctness (strengthened)
/// ---------------------------------------------------------------------------

/// After minor collection, every promoted object's forwarded address
/// is in the post-collection major heap's objects list.
let minor_collect_preserves_reachable
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (obj: U64.t)
  : Lemma (requires
             minor_wf minor /\
             well_formed_heap major /\
             AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
             Seq.mem obj (live_set_of minor major roots))
          (ensures
             (let res = minor_collect_spec minor major fp roots in
              let live_set = live_set_of minor major roots in
              let prom_res = promote_all_spec minor major fp live_set in
              fwd_targets_in_objects prom_res.fwd_map live_set (Seq.length live_set) res.mc_major)) =
  let live_set = live_set_of minor major roots in
  promote_all_adds_promoted minor major fp live_set;
  let prom_res = promote_all_spec minor major fp live_set in
  promote_all_preserves_wfh_part1 minor major fp live_set;
  update_major_pointers_preserves_objects prom_res.major_final prom_res.fwd_map;
  minor_collect_spec_unfold minor major fp roots

/// ---------------------------------------------------------------------------
/// Field effect of update_object_pointers (single object)
/// ---------------------------------------------------------------------------

/// After update_object_pointers, reading field j gives the expected result:
/// forwarded if it was a minor pointer with valid fwd, unchanged otherwise.
#push-options "--z3rlimit 40 --fuel 1"
let rec update_object_pointers_field_self
  (major: heap) (obj: obj_addr) (wosize: nat) (fwd: forwarding_map) (i: nat) (j: nat)
  : Lemma
    (requires
      Seq.mem obj (objects 0UL major) /\
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
      Seq.mem obj (objects 0UL major) /\
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

/// ---------------------------------------------------------------------------
/// update_all_objects_aux field effect
/// ---------------------------------------------------------------------------

/// Helper: find the index of an element in a sequence
private let rec seq_index_of (#a:eqtype) (s: seq a) (x: a{Seq.mem x s})
  : GTot (n:nat{n < Seq.length s /\ Seq.index s n == x})
  (decreases Seq.length s) =
  if Seq.index s 0 = x then 0
  else begin
    Seq.lemma_index_is_nth s 0;
    let tl = Seq.tail s in
    Seq.lemma_mem_append (Seq.create 1 (Seq.index s 0)) tl;
    1 + seq_index_of tl x
  end

/// Helper: adjacent elements in objects list are strictly ordered.
/// Proof by structural induction on the objects list construction.
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
private let rec objects_monotone_adjacent (g: heap) (start: hp_addr) (i: nat)
  : Lemma
    (requires i + 1 < Seq.length (objects start g))
    (ensures U64.v (Seq.index (objects start g) i) < U64.v (Seq.index (objects start g) (i + 1)))
    (decreases (Seq.length g - U64.v start)) =
  // objects start g = if start+8 >= |g| then [] else cons (start+8) (objects next_start g)
  // where next_start = start + (wz+1)*8
  if U64.v start + 8 >= Seq.length g then ()  // impossible: objects is empty, contradicts precond
  else
    let header = read_word g start in
    let wz = getWosize header in
    let obj_size_nat = U64.v wz + 1 in
    let next_start_nat = U64.v start + (obj_size_nat * 8) in
    if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()  // impossible
    else begin
      f_address_spec start;
      let first : obj_addr = f_address start in
      if next_start_nat >= heap_size then ()  // objects is singleton, can't have i+1 < 1
      else begin
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        let rest = objects next_start g in
        // objects start g = cons first rest
        // Seq.index (cons first rest) 0 = first
        // Seq.index (cons first rest) (k+1) = Seq.index rest k
        if i = 0 then begin
          // Need: first < Seq.index rest 0
          // All elements of rest are > next_start (from objects_addresses_gt_start)
          // next_start = start + (wz+1)*8 > start + 8 = first (since wz >= 0, (wz+1)*8 >= 8)
          // Actually next_start = start + (wz+1)*8 >= start + 8 = first
          // But wz could be 0 and then next_start = start + 8 = first!
          // No: wz is getWosize header. And next_start_nat < heap_size was checked.
          // If wz = 0, then next_start = start + 8 = first, and objects_addresses_gt_start
          // gives elements of rest > next_start = first. 
          objects_addresses_gt_start next_start g (Seq.index rest 0);
          FStar.Seq.Properties.seq_mem_k rest 0;
          assert (U64.v (Seq.index rest 0) > U64.v next_start);
          assert (U64.v next_start >= U64.v first)
        end else begin
          // i > 0: Seq.index (cons first rest) i = Seq.index rest (i-1)
          //        Seq.index (cons first rest) (i+1) = Seq.index rest i
          // Need: Seq.index rest (i-1) < Seq.index rest i
          // By induction on rest = objects next_start g
          objects_monotone_adjacent g next_start (i - 1)
        end
      end
    end
#pop-options

/// Helper: objects list is strictly monotone — earlier positions have lower addresses.
/// Proof: objects_addresses_gt_start shows all elements at index > 0 have address > first element.
/// By induction on the sequence structure, earlier positions have lower addresses.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec objects_strictly_monotone (g: heap) (i j: nat)
  : Lemma
    (requires
      i < j /\ j < Seq.length (objects 0UL g))
    (ensures U64.v (Seq.index (objects 0UL g) i) < U64.v (Seq.index (objects 0UL g) j))
    (decreases j - i) =
  if j = i + 1 then
    objects_monotone_adjacent g 0UL i
  else begin
    objects_strictly_monotone g i (j - 1);
    objects_strictly_monotone g (j - 1) j
  end
#pop-options

/// Helper: objects before position pos have addresses < obj
#push-options "--z3rlimit 20"
private let objects_below_before (g: heap) (obj: obj_addr) (pos: nat)
  : Lemma
    (requires
      pos < Seq.length (objects 0UL g) /\
      Seq.index (objects 0UL g) pos == obj)
    (ensures
      (forall (k:nat). k < pos /\ k < Seq.length (objects 0UL g) ==>
        U64.v (Seq.index (objects 0UL g) k) < U64.v obj)) =
  let aux (k: nat{k < Seq.length (objects 0UL g)}) : Lemma
    (requires k < pos)
    (ensures U64.v (Seq.index (objects 0UL g) k) < U64.v obj)
  = objects_strictly_monotone g k pos
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// Helper: objects after position pos have addresses > obj
#push-options "--z3rlimit 20"
private let objects_above_after (g: heap) (obj: obj_addr) (pos: nat)
  : Lemma
    (requires
      pos < Seq.length (objects 0UL g) /\
      Seq.index (objects 0UL g) pos == obj)
    (ensures
      (forall (k:nat). k > pos /\ k < Seq.length (objects 0UL g) ==>
        U64.v (Seq.index (objects 0UL g) k) > U64.v obj)) =
  let aux (k: nat{k < Seq.length (objects 0UL g)}) : Lemma
    (requires k > pos)
    (ensures U64.v (Seq.index (objects 0UL g) k) > U64.v obj)
  = objects_strictly_monotone g pos k
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// update_all_objects_aux processing objects AFTER obj doesn't change obj's field j.
/// Those objects are at higher addresses, so their body regions don't overlap obj's fields.
#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_after_preserves_field
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map)
  (idx: nat) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem obj objs /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      (forall (k:nat). k >= idx /\ k < Seq.length objs ==>
        U64.v (Seq.index objs k) > U64.v obj))
    (ensures
      (let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       read_word (update_all_objects_aux major objs fwd idx) field_addr ==
       read_word major field_addr))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else begin
    let other = Seq.index objs idx in
    assert (U64.v other > U64.v obj);
    let wz_other = U64.v (wosize_of_object other major) in
    hd_address_spec other;
    // obj + j*8 < obj + wz_obj*8 < other (by objects_separated, since obj < other and both in objs)
    let wz_obj = U64.v (wosize_of_object obj major) in
    objects_separated 0UL major obj other;
    assert (U64.v obj + (wz_obj + 1) * 8 <= U64.v other);
    assert (U64.v obj + j * 8 < U64.v other);
    let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
    assert (forall (k:nat). k < wz_other ==>
      (U64.v other + k * 8 + 8 <= heap_size /\ (U64.v other + k * 8) % 8 == 0));
    update_object_pointers_preserves_addr_below major other wz_other fwd 0 field_addr;
    let major' = update_object_pointers major other wz_other fwd 0 in
    update_object_pointers_preserves_objects major other wz_other fwd 0;
    assert (objects zero_addr major' == objs);
    // Establish well_formed_heap_part1 major'
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = other then begin
        update_object_pointers_preserves_self_header major other wz_other fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else if U64.v h > U64.v other then begin
        update_object_pointers_preserves_other_header major other wz_other fwd 0 h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address h);
        wosize_of_object_spec h major;
        wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    // wosize of obj is unchanged: hd_address obj < other, so header is preserved
    hd_address_spec obj;
    update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address obj);
    wosize_of_object_spec obj major;
    wosize_of_object_spec obj major';
    update_all_objects_aux_after_preserves_field major' objs fwd (idx + 1) obj j
  end
#pop-options

/// Main induction: update_all_objects_aux computes the expected field effect.
#push-options "--z3rlimit 80 --fuel 1 --split_queries always"
let rec update_all_objects_aux_field_effect
  (major: heap) (objs: seq obj_addr) (fwd: forwarding_map)
  (idx: nat) (obj: obj_addr) (j: nat) (pos: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      objs == objects zero_addr major /\
      Seq.mem obj objs /\
      pos < Seq.length objs /\ Seq.index objs pos == obj /\
      idx <= pos /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0 /\
      (forall (k:nat). k >= idx /\ k < pos ==>
        U64.v (Seq.index objs k) < U64.v obj))
    (ensures
      (let updated = update_all_objects_aux major objs fwd idx in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = read_word major field_addr in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_val)))
    (decreases (Seq.length objs - idx)) =
  if idx >= Seq.length objs then ()
  else if idx = pos then begin
    // Processing obj itself
    let wz = U64.v (wosize_of_object obj major) in
    hd_address_spec obj;
    assert (forall (k:nat). k < wz ==>
      (U64.v obj + k * 8 + 8 <= heap_size /\ (U64.v obj + k * 8) % 8 == 0));
    update_object_pointers_field_self major obj wz fwd 0 j;
    let major' = update_object_pointers major obj wz fwd 0 in
    update_object_pointers_preserves_objects major obj wz fwd 0;
    assert (objects zero_addr major' == objs);
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = obj then begin
        update_object_pointers_preserves_self_header major obj wz fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else if U64.v h > U64.v obj then begin
        update_object_pointers_preserves_other_header major obj wz fwd 0 h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        update_object_pointers_preserves_addr_below major obj wz fwd 0 (hd_address h);
        wosize_of_object_spec h major;
        wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    update_object_pointers_preserves_self_header major obj wz fwd 0;
    wosize_of_object_spec obj major;
    wosize_of_object_spec obj major';
    // Remaining objects (pos+1..) are all > obj — they don't change field j
    objects_above_after major obj pos;
    let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
    update_all_objects_aux_after_preserves_field major' objs fwd (idx + 1) obj j
  end else begin
    // idx < pos: processing an object before obj (which has lower address)
    let other = Seq.index objs idx in
    assert (U64.v other < U64.v obj);
    let wz_other = U64.v (wosize_of_object other major) in
    hd_address_spec other;
    // other's body is [other, other + wz_other*8), and by objects_separated,
    // other + (wz_other+1)*8 <= obj, so obj + j*8 >= obj > other + wz_other*8
    objects_separated 0UL major other obj;
    let field_addr : hp_addr = U64.uint_to_t (U64.v obj + j * 8) in
    assert (U64.v field_addr >= U64.v other + wz_other * 8);
    assert (forall (k:nat). k < wz_other ==>
      (U64.v other + k * 8 + 8 <= heap_size /\ (U64.v other + k * 8) % 8 == 0));
    update_object_pointers_preserves_addr_above major other wz_other fwd 0 field_addr;
    let major' = update_object_pointers major other wz_other fwd 0 in
    update_object_pointers_preserves_objects major other wz_other fwd 0;
    assert (objects zero_addr major' == objs);
    let aux_wfh (h: obj_addr) : Lemma
      (requires Seq.mem h (objects 0UL major'))
      (ensures U64.v (hd_address h) + 8 + (U64.v (wosize_of_object h major') * 8) <= Seq.length major')
    = hd_address_spec h;
      if h = other then begin
        update_object_pointers_preserves_self_header major other wz_other fwd 0;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else if U64.v h > U64.v other then begin
        update_object_pointers_preserves_other_header major other wz_other fwd 0 h;
        wosize_of_object_spec h major';
        wosize_of_object_spec h major
      end else begin
        update_object_pointers_preserves_addr_below major other wz_other fwd 0 (hd_address h);
        wosize_of_object_spec h major;
        wosize_of_object_spec h major'
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_wfh);
    // wosize of obj preserved (obj > other, so header of obj preserved)
    hd_address_spec obj;
    // obj > other + wz_other*8, both multiples of 8, so obj >= other + wz_other*8 + 8
    // hence hd_address obj = obj - 8 >= other + wz_other*8
    assert (U64.v (hd_address obj) >= U64.v other + wz_other * 8);
    update_object_pointers_preserves_addr_above major other wz_other fwd 0 (hd_address obj);
    wosize_of_object_spec obj major;
    wosize_of_object_spec obj major';
    update_all_objects_aux_field_effect major' objs fwd (idx + 1) obj j pos
  end
#pop-options

/// Top-level: update_major_pointers field effect
let update_major_pointers_field_effect
  (major: heap) (fwd: forwarding_map) (obj: obj_addr) (j: nat)
  : Lemma
    (requires
      well_formed_heap_part1 major /\
      Seq.mem obj (objects zero_addr major) /\
      j < U64.v (wosize_of_object obj major) /\
      U64.v obj + j * 8 + 8 <= heap_size /\
      (U64.v obj + j * 8) % 8 == 0)
    (ensures
      (let updated = update_major_pointers major fwd in
       let field_addr = U64.uint_to_t (U64.v obj + j * 8) in
       let old_val = read_word major field_addr in
       let new_val = read_word updated field_addr in
       (is_minor_pointer old_val /\ fwd old_val <> 0UL ==> new_val == fwd old_val) /\
       (~(is_minor_pointer old_val /\ fwd old_val <> 0UL) ==> new_val == old_val))) =
  let objs = objects zero_addr major in
  let pos = seq_index_of objs obj in
  objects_below_before major obj pos;
  update_all_objects_aux_field_effect major objs fwd 0 obj j pos

/// update_major_pointers establishes well_formed_heap_part2 (pointer closure).
/// Uses pointer_closure_modulo_fwd (weaker than full part2) + fwd_all_targets_valid.
#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let update_major_pointers_preserves_wfh_part2 (major: heap) (fwd: forwarding_map)
  : Lemma (requires well_formed_heap_part1 major /\
                    pointer_closure_modulo_fwd major fwd /\
                    fwd_all_targets_valid fwd major)
    (ensures well_formed_heap_part2 (update_major_pointers major fwd)) =
  let mc = update_major_pointers major fwd in
  update_major_pointers_preserves_objects major fwd;
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires Seq.mem src (objects 0UL mc) /\
                      j < U64.v (wosize_of_object src mc) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let v = read_word mc (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer v ==> Seq.mem (v <: obj_addr) (objects 0UL mc)))
    = update_major_pointers_preserves_header major fwd src;
      assert (read_word mc (hd_address src) == read_word major (hd_address src));
      GC.Spec.Object.wosize_of_object_spec src mc;
      GC.Spec.Object.wosize_of_object_spec src major;
      assert (wosize_of_object src mc == wosize_of_object src major);
      let field_addr = U64.uint_to_t (U64.v src + j * 8) in
      assert ((U64.v src + j * 8) % 8 == 0);
      update_major_pointers_field_effect major fwd src j;
      let old_val = read_word major field_addr in
      let new_val = read_word mc field_addr in
      if is_minor_pointer old_val && fwd old_val <> 0UL then begin
        // Case 1: rewritten to fwd(old_val), which is in objects by fwd_all_targets_valid
        assert (new_val == fwd old_val);
        assert (is_pointer new_val ==> Seq.mem ((fwd old_val) <: obj_addr) (objects zero_addr major))
      end else begin
        // Case 2: unchanged. new_val = old_val.
        assert (new_val == old_val);
        // If is_pointer(old_val), then is_minor_pointer(old_val) (heap_size < minor_heap_size).
        // Combined with ~(is_minor_pointer /\ fwd≠0), we get fwd(old_val)==0.
        // pointer_closure_modulo_fwd then gives old_val ∈ objects(major).
        ()
      end
  in
  update_major_pointers_preserves_wfh_part1 major fwd;
  well_formed_heap_part2_from_field_closure mc field_closure
#pop-options

/// ---------------------------------------------------------------------------
/// Promote_all field preservation
/// ---------------------------------------------------------------------------

/// Helper: promote_object preserves reads in the body of a different object
/// that avoids the free-list chain. After alloc + copy_fields, the body of
/// `other` is untouched because:
/// 1. alloc_spec only modifies headers/links of free-list blocks (alloc_spec_read_other)
/// 2. copy_fields writes to the newly allocated body, which is different from other's body
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
private let promote_object_read_other
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (other: obj_addr) (addr: hp_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem other (objects 0UL major) /\
      AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
      U64.v addr >= U64.v other /\
      U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8 /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures read_word (promote_object minor major obj fp wosize).major_out addr ==
             read_word major addr)
  = let fuel = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let new_addr = alloc_res.obj_out in
    // Step 1: alloc preserves addr (in other's body, other avoids chain)
    AllocLemmas.alloc_spec_read_other major fp wosize other addr;
    assert (read_word new_major addr == read_word major addr);
    // Step 2: copy_fields to new_addr preserves addr
    // Establish: new_addr is a valid obj_addr in PRE-alloc objects
    GC.Gen.AllocProps.alloc_search_obj_in_objects_pre_part1 major fp 0UL fp
      (if wosize = 0 then 1 else wosize) fuel;
    // new_addr ∈ objects(0UL, major) and other ∈ objects(0UL, major)
    let dst_obj : obj_addr = new_addr in
    // other ≠ new_addr (other avoids the chain, new_addr was in the chain)
    GC.Gen.AllocProps.alloc_spec_obj_ne_excl major fp wosize other;
    assert (new_addr <> other);
    // Pre-alloc wosize of new_addr >= wosize
    GC.Gen.AllocProps.alloc_spec_obj_wosize_pre_part1 major fp wosize;
    assert (U64.v (wosize_of_object dst_obj major) >= wosize);
    // Use objects_separated on the ORIGINAL heap (same wosize as precondition)
    if U64.v other < U64.v new_addr then begin
      objects_separated 0UL major other dst_obj;
      // Gives: new_addr > other + wosize_of_object(other, major)*8
      // Combined with addr + 8 <= other + wosize_of_object(other, major)*8:
      // addr + 8 <= new_addr, so addr is below the write range [new_addr, new_addr+wosize*8)
      // copy_fields_preserves_other precond 2: dst_obj + (wosize-1)*8 + 8 <= heap_size
      // From wfh_part1: hd(new_addr) + 8 + wosize_of_object(new_addr, major)*8 <= heap_size
      // Since wosize_of_object(new_addr, major) >= wosize and hd(new_addr) = new_addr - 8:
      // new_addr + wosize_of_object(new_addr, major)*8 <= heap_size, so new_addr + wosize*8 <= heap_size
      hd_address_spec dst_obj;
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize addr
    end else begin
      // other > new_addr: objects_separated gives other > new_addr + wosize_of_object(new_addr, major)*8
      objects_separated 0UL major dst_obj other;
      // Gives: other > new_addr + wosize_of_object(new_addr, major)*8 >= new_addr + wosize*8
      // Since addr >= other: addr >= new_addr + wosize*8, so addr is above the write range
      hd_address_spec dst_obj;
      copy_fields_preserves_other minor new_major obj dst_obj 0 wosize addr
    end
#pop-options

/// Helper: promote_object preserves chain_avoids for an excluded object
/// that was already not in the chain.
#push-options "--z3rlimit 160 --fuel 1 --ifuel 0"
private let promote_object_preserves_chain_avoids
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wosize: nat{wosize > 0}) (excl: U64.t)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      AllocLemmas.chain_avoids major fp excl (heap_size / U64.v mword) = true /\
      U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
      U64.v excl % U64.v mword == 0 /\
      Seq.mem (excl <: obj_addr) (objects 0UL major) /\
      U64.v (wosize_of_object (excl <: obj_addr) major) >= 1 /\
      (promote_object minor major obj fp wosize).new_addr <> 0UL)
    (ensures
      (let res = promote_object minor major obj fp wosize in
       AllocLemmas.chain_avoids res.major_out res.fp_out excl (heap_size / U64.v mword) = true))
  = let fuel = heap_size / U64.v mword in
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wosize in
    let new_major = alloc_res.heap_out in
    let new_fp = alloc_res.fp_out in
    let dst = alloc_res.obj_out in
    // Establish obj_out is a valid obj_addr
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wosize;
    let dst_obj : obj_addr = dst in
    // Step 1: alloc preserves chain_avoids for excl
    AllocLemmas.alloc_spec_preserves_chain_avoids_other major fp wosize excl;
    assert (AllocLemmas.chain_avoids new_major new_fp excl fuel = true);
    // Step 2: chain_avoids for dst_obj in new chain
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wosize;
    assert (AllocLemmas.chain_avoids new_major new_fp dst_obj fuel = true);
    // Step 3: fl_valid new_major new_fp fuel
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wosize;
    assert (AllocLemmas.fl_valid new_major new_fp fuel);
    // Step 4: well_formed_heap_part1 new_major
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wosize;
    assert (well_formed_heap_part1 new_major);
    // Step 5: promote_object = alloc + copy_fields
    let res = promote_object minor major obj fp wosize in
    // Step 6: prove the quantifier for chain_avoids_transfer_excl2
    // copy_fields writes only to [dst_obj, dst_obj + wosize*8)
    // For any a ∈ objects(new_major), a ≠ excl, a ≠ dst_obj:
    //   a's first field at address a doesn't overlap [dst_obj, dst_obj + wosize*8)
    //   because objects_separated gives disjoint ranges
    //   So read_word res.major_out a == read_word new_major a
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wosize;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wosize;
    assert (Seq.mem dst_obj (objects 0UL new_major));
    assert (U64.v (wosize_of_object dst_obj new_major) >= wosize);
    // Instantiate wfh_part1 at dst_obj
    hd_address_spec dst_obj;
    assert (U64.v (hd_address dst_obj) + 8 + U64.v (wosize_of_object dst_obj new_major) * 8 <= heap_size);
    assert (U64.v dst_obj + wosize * 8 <= heap_size);
    let transfer_helper (a: hp_addr) : Lemma
      (requires U64.v a >= U64.v mword /\
               Seq.mem a (objects 0UL new_major) /\ a <> excl /\ a <> dst_obj /\
               U64.v (wosize_of_object (a <: obj_addr) new_major) >= 1 /\
               U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size)
      (ensures read_word res.major_out a == read_word new_major a)
    = let ao : obj_addr = a in
      // a ≠ dst_obj, both in objects(new_major) → objects_separated
      // Then copy_fields at [dst_obj, dst_obj+wosize*8) doesn't touch address a
      // First establish dst_obj body fits in heap (for copy_fields_preserves_other precondition)
      assert (U64.v dst_obj + wosize * 8 <= heap_size);
      if U64.v a < U64.v dst_obj then begin
        objects_separated 0UL new_major ao dst_obj;
        // objects_separated gives: dst_obj > a + wz_a*8 where wz_a >= 1
        assert (U64.v dst_obj > U64.v a + U64.v (wosize_of_object_as_wosize ao new_major) * 8);
        assert (U64.v a + 8 <= U64.v dst_obj);
        assert (forall (k:nat). 0 <= k /\ k < wosize ==> U64.v a + 8 <= U64.v dst_obj + k * 8);
        copy_fields_preserves_other minor new_major obj dst_obj 0 wosize ao
      end else begin
        objects_separated 0UL new_major dst_obj ao;
        // objects_separated gives: a > dst_obj + wz_dst*8
        assert (U64.v a > U64.v dst_obj + U64.v (wosize_of_object_as_wosize dst_obj new_major) * 8);
        assert (U64.v (wosize_of_object dst_obj new_major) >= wosize);
        assert (U64.v a >= U64.v dst_obj + wosize * 8 + 8);
        assert (forall (k:nat). 0 <= k /\ k < wosize ==> U64.v dst_obj + k * 8 + 8 <= U64.v a);
        copy_fields_preserves_other minor new_major obj dst_obj 0 wosize ao
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires transfer_helper);
    AllocLemmas.chain_avoids_transfer_excl2 new_major res.major_out new_fp excl dst_obj fuel
#pop-options

/// Top-level helper: promote_object preserves a single field read for a previously promoted object.
#push-options "--z3rlimit 160 --fuel 1 --ifuel 0 --split_queries no"
private let promote_object_preserves_one_field
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: U64.t)
  (wz: nat{wz > 0})
  (prev_addr: obj_addr) (j: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem prev_addr (objects 0UL major) /\
      AllocLemmas.chain_avoids major fp prev_addr (heap_size / U64.v mword) = true /\
      (promote_object minor major obj fp wz).new_addr <> 0UL /\
      U64.v prev_addr + j * 8 + 8 <= heap_size /\
      U64.v prev_addr % 8 == 0 /\
      U64.v prev_addr + j * 8 < U64.v prev_addr + U64.v (wosize_of_object prev_addr major) * 8)
    (ensures read_word (promote_object minor major obj fp wz).major_out
                       (U64.uint_to_t (U64.v prev_addr + j * 8)) ==
             read_word major (U64.uint_to_t (U64.v prev_addr + j * 8)))
  = let field_addr : hp_addr = U64.uint_to_t (U64.v prev_addr + j * 8) in
    promote_object_read_other minor major obj fp wz prev_addr field_addr
#pop-options

/// Inductive proof: promote_all_aux preserves field data of all previously
/// promoted objects AND maintains chain_avoids for all promoted addresses.
///
/// Invariant at index idx:
///   - well_formed_heap_part1 major
///   - fl_valid major fp fuel
///   - fl_chain_terminates major fp fuel
///   - For all k < idx: if fwd(live_set[k]) ≠ 0, then fields match minor
///     AND chain_avoids holds for fwd(live_set[k]) in current state
/// Step lemma: one promote_object call preserves the inductive invariant.
/// Extracted as a non-recursive top-level lemma for deterministic verification.
#push-options "--z3rlimit 2000 --fuel 1 --ifuel 0 --z3refresh"
private let promote_step_preserves_invariant
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      idx < Seq.length live_set /\
      (let obj = Seq.index live_set idx in
       let wz = minor_wosize minor obj in
       wz > 0 /\
       (promote_object minor major obj fp wz).new_addr <> 0UL) /\
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      (forall (k:nat). k < idx /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz_k = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj) ==>
         (Seq.mem ((fwd obj) <: obj_addr) (objects 0UL major) /\
          U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
          AllocLemmas.chain_avoids major fp (fwd obj) (heap_size / U64.v mword) = true))))
    (ensures (let obj = Seq.index live_set idx in
              let wz = minor_wosize minor obj in
              let res = promote_object minor major obj fp wz in
              let fwd' = extend_forwarding fwd obj res.new_addr in
              well_formed_heap_part1 res.major_out /\
              AllocLemmas.fl_valid res.major_out res.fp_out (heap_size / U64.v mword) /\
              AllocLemmas.fl_chain_terminates res.major_out res.fp_out (heap_size / U64.v mword) /\
              fields_match_minor minor res.major_out fwd' live_set (idx + 1) /\
              (forall (k:nat). k < idx + 1 /\ k < Seq.length live_set ==>
                (let ok = Seq.index live_set k in
                 let wz_k = minor_wosize minor ok in
                 fwd' ok <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd' ok) ==>
                 (Seq.mem ((fwd' ok) <: obj_addr) (objects 0UL res.major_out) /\
                  U64.v (wosize_of_object ((fwd' ok) <: obj_addr) res.major_out) >= wz_k /\
                  AllocLemmas.chain_avoids res.major_out res.fp_out (fwd' ok) (heap_size / U64.v mword) = true)))))
  = let obj = Seq.index live_set idx in
    let wz = minor_wosize minor obj in
    let res = promote_object minor major obj fp wz in
    let new_addr = res.new_addr in
    let fwd' = extend_forwarding fwd obj new_addr in
    let fuel = heap_size / U64.v mword in
    // Alloc/copy infrastructure lemmas
    AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
    AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
    AllocLemmas.alloc_spec_obj_not_in_chain_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_in_objects_part1 major fp wz;
    GC.Gen.AllocProps.alloc_spec_obj_wosize_part1 major fp wz;
    promote_preserves_fields minor major obj fp wz;
    let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
    let dst_obj : obj_addr = alloc_res.obj_out in
    copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj dst_obj wz;
    copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    // For each previous k: fields preserved through promote_object
    let aux_field (k:nat) : Lemma
      (requires k < idx /\ k < Seq.length live_set /\
               (let prev_obj = Seq.index live_set k in
                let prev_wz = minor_wosize minor prev_obj in
                fwd prev_obj <> 0UL /\ prev_wz > 0 /\ is_val_addr (fwd prev_obj) /\
                Seq.mem ((fwd prev_obj) <: obj_addr) (objects 0UL major) /\
                U64.v (wosize_of_object ((fwd prev_obj) <: obj_addr) major) >= prev_wz /\
                AllocLemmas.chain_avoids major fp (fwd prev_obj) (heap_size / U64.v mword) = true))
      (ensures (let prev_obj = Seq.index live_set k in
                let prev_wz = minor_wosize minor prev_obj in
                let prev_addr = fwd prev_obj in
                dst_fields_valid prev_addr prev_wz /\
                U64.v prev_addr % 8 == 0 ==>
                (forall (j:nat). j < prev_wz ==>
                  read_word res.major_out (U64.uint_to_t (U64.v prev_addr + j * 8)) ==
                  minor_read_field minor prev_obj j)))
    = let prev_obj = Seq.index live_set k in
      let prev_wz = minor_wosize minor prev_obj in
      let prev_addr : obj_addr = fwd prev_obj in
      if not (U64.v prev_addr % 8 = 0) then ()
      else if not (U64.v prev_addr + (prev_wz - 1) * 8 + 8 <= heap_size) then ()
      else begin
        let aux_j (j:nat) : Lemma
          (requires j < prev_wz)
          (ensures read_word res.major_out (U64.uint_to_t (U64.v prev_addr + j * 8)) ==
                   minor_read_field minor prev_obj j) =
          promote_object_preserves_one_field minor major obj fp wz prev_addr j
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux_j)
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_field);
    // chain_avoids for each previous k is preserved
    let aux_chain (k:nat) : Lemma
      (requires k < idx /\ k < Seq.length live_set /\
               (let prev_obj = Seq.index live_set k in
                let prev_wz = minor_wosize minor prev_obj in
                fwd prev_obj <> 0UL /\ prev_wz > 0 /\ is_val_addr (fwd prev_obj) /\
                Seq.mem ((fwd prev_obj) <: obj_addr) (objects 0UL major) /\
                U64.v (wosize_of_object ((fwd prev_obj) <: obj_addr) major) >= prev_wz /\
                AllocLemmas.chain_avoids major fp (fwd prev_obj) (heap_size / U64.v mword) = true))
      (ensures (let prev_obj = Seq.index live_set k in
                AllocLemmas.chain_avoids res.major_out res.fp_out (fwd prev_obj) fuel = true))
    = let prev_obj = Seq.index live_set k in
      promote_object_preserves_chain_avoids minor major obj fp wz (fwd prev_obj)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux_chain);
    // chain_avoids for new_addr
    copy_fields_preserves_chain_avoids_self minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
    // Explicitly assert each postcondition conjunct to guide Z3
    assert (well_formed_heap_part1 res.major_out);
    assert (AllocLemmas.fl_valid res.major_out res.fp_out fuel);
    assert (AllocLemmas.fl_chain_terminates res.major_out res.fp_out fuel);
    assert (AllocLemmas.chain_avoids res.major_out res.fp_out res.new_addr fuel = true)
#pop-options

/// Inductive proof: promote_all_aux preserves field data of all previously
/// promoted objects AND maintains chain_avoids for all promoted addresses.
///
/// Invariant at index idx:
///   - well_formed_heap_part1 major
///   - fl_valid major fp fuel
///   - fl_chain_terminates major fp fuel
///   - For all k < idx: if fwd(live_set[k]) ≠ 0, then fields match minor
///     AND chain_avoids holds for fwd(live_set[k]) in current state
#push-options "--z3rlimit 50 --fuel 1 --ifuel 0"
private let rec promote_all_aux_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      fields_match_minor minor major fwd live_set idx /\
      (forall (k:nat). k < idx /\ k < Seq.length live_set ==>
        (let obj = Seq.index live_set k in
         let wz_k = minor_wosize minor obj in
         fwd obj <> 0UL /\ wz_k > 0 /\ is_val_addr (fwd obj) ==>
         (Seq.mem ((fwd obj) <: obj_addr) (objects 0UL major) /\
          U64.v (wosize_of_object ((fwd obj) <: obj_addr) major) >= wz_k /\
          AllocLemmas.chain_avoids major fp (fwd obj) (heap_size / U64.v mword) = true))))
    (ensures
      (let res = promote_all_aux minor major fp live_set fwd idx in
       fields_match_minor minor res.major_final res.fwd_map live_set (Seq.length live_set)))
    (decreases (Seq.length live_set - idx))
  = if idx >= Seq.length live_set then ()
    else begin
      let obj = Seq.index live_set idx in
      let wz = minor_wosize minor obj in
      if wz = 0 then
        promote_all_aux_preserves_fields minor major fp live_set fwd (idx + 1)
      else begin
        let res = promote_object minor major obj fp wz in
        if res.new_addr = 0UL then ()
        else begin
          promote_step_preserves_invariant minor major fp live_set fwd idx;
          let fwd' = extend_forwarding fwd obj res.new_addr in
          promote_all_aux_preserves_fields minor res.major_out res.fp_out live_set fwd' (idx + 1)
        end
      end
    end
#pop-options

let promote_all_preserves_fields
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword))
          (ensures (let res = promote_all_spec minor major fp live_set in
                    fields_match_minor minor res.major_final res.fwd_map
                                       live_set (Seq.length live_set)))
  = promote_all_aux_preserves_fields minor major fp live_set empty_forwarding 0

/// ---------------------------------------------------------------------------
/// Frame lemma: promote_all_spec preserves body reads for non-promoted objects
/// ---------------------------------------------------------------------------

/// Inductive: promote_all_aux preserves reads in the body of an object
/// that avoids the free chain.
#push-options "--z3rlimit 200 --fuel 1 --ifuel 0 --split_queries always"
private let rec promote_all_aux_read_other
  (minor: minor_state) (major: heap) (fp: U64.t)
  (live_set: seq U64.t) (fwd: forwarding_map) (idx: nat)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires
      well_formed_heap_part1 major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      Seq.mem other (objects 0UL major) /\
      AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
      U64.v addr >= U64.v other /\
      U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8)
    (ensures
      (let res = promote_all_aux minor major fp live_set fwd idx in
       read_word res.major_final addr == read_word major addr))
    (decreases (Seq.length live_set - idx))
  = if idx >= Seq.length live_set then ()
    else begin
      let obj = Seq.index live_set idx in
      let wz = minor_wosize minor obj in
      if wz = 0 then
        promote_all_aux_read_other minor major fp live_set fwd (idx + 1) other addr
      else begin
        let res = promote_object minor major obj fp wz in
        if res.new_addr = 0UL then ()
        else begin
          let fuel = heap_size / U64.v mword in
          // promote_object preserves the read at addr (body of other)
          promote_object_read_other minor major obj fp wz other addr;
          assert (read_word res.major_out addr == read_word major addr);
          // Maintain invariants for recursion:
          // wfh_part1
          AllocLemmas.alloc_spec_preserves_wfh_part1 major fp wz;
          let alloc_res = GC.Spec.Allocator.alloc_spec major fp wz in
          copy_fields_preserves_wfh_part1 minor alloc_res.heap_out obj (alloc_res.obj_out <: obj_addr) wz;
          // fl_valid
          AllocLemmas.alloc_spec_preserves_fl_valid_part1 major fp wz;
          GC.Gen.AllocProps.alloc_spec_obj_valid major fp wz;
          let dst_obj : obj_addr = alloc_res.obj_out in
          copy_fields_preserves_fl_valid_aux minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
          // fl_chain_terminates
          AllocLemmas.alloc_spec_preserves_fl_chain_terminates_part1 major fp wz;
          copy_fields_preserves_fl_chain_terminates minor alloc_res.heap_out obj dst_obj 0 wz alloc_res.fp_out fuel;
          // chain_avoids preserved for other
          promote_object_preserves_chain_avoids minor major obj fp wz other;
          // other still in objects
          promote_object_preserves_objects_part1 minor major obj fp wz;
          // Recurse
          let fwd' = extend_forwarding fwd obj res.new_addr in
          promote_all_aux_read_other minor res.major_out res.fp_out
                                     live_set fwd' (idx + 1) other addr
        end
      end
    end
#pop-options

let promote_all_read_other
  (minor: minor_state) (major: heap) (fp: U64.t) (live_set: seq U64.t)
  (other: obj_addr) (addr: hp_addr)
  : Lemma (requires well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Seq.mem other (objects 0UL major) /\
                    AllocLemmas.chain_avoids major fp other (heap_size / U64.v mword) = true /\
                    U64.v addr >= U64.v other /\
                    U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other major) * 8)
          (ensures (let res = promote_all_spec minor major fp live_set in
                    read_word res.major_final addr == read_word major addr))
  = promote_all_aux_read_other minor major fp live_set empty_forwarding 0 other addr

/// Trivial unfold lemma for minor_collect_all_spec
let minor_collect_all_spec_unfold (minor: minor_state) (major: heap)
                                   (fp: U64.t) (roots: seq U64.t)
  : Lemma (let all_objs = minor_objects minor in
           let prom_res = promote_all_spec minor major fp all_objs in
           (minor_collect_all_spec minor major fp roots).mc_major ==
             update_major_pointers prom_res.major_final prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fwd == prom_res.fwd_map /\
           (minor_collect_all_spec minor major fp roots).mc_fp == prom_res.fp_final)
  = ()
