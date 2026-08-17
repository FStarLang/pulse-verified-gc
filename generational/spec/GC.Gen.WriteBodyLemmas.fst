/// ---------------------------------------------------------------------------
/// GC.Gen.Promote.WriteBody — Write-body preservation lemmas
/// ---------------------------------------------------------------------------

module GC.Gen.WriteBodyLemmas

open FStar.Seq
module U64 = FStar.UInt64
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
module AllocLemmas = GC.Spec.Allocator.Lemmas

/// ---------------------------------------------------------------------------
/// copy_fields — core recursive definition
/// ---------------------------------------------------------------------------

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

let copy_fields_base (minor: minor_state) (major: heap)
                     (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i >= n)
          (ensures copy_fields minor major src_obj dst_obj i n == major) = ()

let copy_fields_step (minor: minor_state) (major: heap)
                     (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i < n /\
                     U64.v dst_obj + i * 8 + 8 <= heap_size /\
                     (U64.v dst_obj + i * 8) % 8 == 0)
           (ensures copy_fields minor major src_obj dst_obj i n ==
                    copy_fields minor
                      (write_word major (U64.uint_to_t (U64.v dst_obj + i * 8))
                                       (minor_read_field minor src_obj i))
                      src_obj dst_obj (i + 1) n) = ()

let copy_fields_oob (minor: minor_state) (major: heap)
                    (src_obj: U64.t) (dst_obj: U64.t) (i: nat) (n: nat)
  : Lemma (requires i < n /\
                     (U64.v dst_obj + i * 8 + 8 > heap_size \/
                      (U64.v dst_obj + i * 8) % 8 <> 0))
           (ensures copy_fields minor major src_obj dst_obj i n == major) = ()

/// ---------------------------------------------------------------------------
/// not_in_fl_chain
/// ---------------------------------------------------------------------------

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

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec chain_avoids_implies_not_in_fl_chain
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
      AllocLemmas.chain_avoids_head_ne g fp dst_obj fuel;
      let hd = hd_address (fp <: obj_addr) in
      if U64.v hd + 16 <= heap_size then begin
        let next_fp = read_word g (fp <: obj_addr) in
        AllocLemmas.chain_avoids_tail g fp dst_obj fuel;
        chain_avoids_implies_not_in_fl_chain g next_fp dst_obj (fuel - 1)
      end else ()
    end
#pop-options

/// ---------------------------------------------------------------------------
/// write_body_preserves_objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 4 --ifuel 2 --z3refresh"
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
        read_write_different g addr start v;
        if next_start_nat >= heap_size then ()
        else begin
          let next_start : hp_addr = U64.uint_to_t next_start_nat in
          wosize_of_object_spec obj g;
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
          read_write_different g addr start v;
          write_body_preserves_objects_aux next_start g obj addr v
        end
      end
    end
  end
#pop-options

let write_body_preserves_objects
  (g: heap) (obj: obj_addr) (addr: hp_addr) (v: U64.t)
  : Lemma (requires
      Seq.mem obj (objects zero_addr g) /\
      U64.v addr >= U64.v obj /\
      U64.v addr < U64.v obj + (U64.v (wosize_of_object obj g) * 8) /\
      U64.v addr % 8 = 0)
    (ensures objects zero_addr (write_word g addr v) == objects zero_addr g) =
  write_body_preserves_objects_aux zero_addr g obj addr v

/// ---------------------------------------------------------------------------
/// write_body_preserves_fl_valid_aux
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let rec write_body_preserves_fl_valid_aux_impl
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
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
    assert (fp <> dst_obj);
    let fp_obj : obj_addr = fp in
    AllocLemmas.fl_valid_elim g fp fuel;
    if U64.v dst_obj < U64.v fp then begin
      objects_separated zero_addr g dst_obj fp_obj;
      wosize_of_object_spec dst_obj g;
      hd_address_spec fp_obj;
      read_write_different g addr (fp <: hp_addr) v;
      read_write_different g addr (hd_address fp_obj) v
    end else begin
      objects_separated zero_addr g fp_obj dst_obj;
      wosize_of_object_spec fp_obj g;
      hd_address_spec fp_obj;
      read_write_different g addr (fp <: hp_addr) v;
      read_write_different g addr (hd_address fp_obj) v
    end;
    write_body_preserves_objects g dst_obj addr v;
    wosize_of_object_spec fp_obj g;
    wosize_of_object_spec fp_obj (write_word g addr v);
    let g' = write_word g addr v in
    let hd = hd_address fp_obj in
    if U64.v hd + 16 <= heap_size then begin
      let next_fp = read_word g fp_obj in
      assert (read_word g' fp_obj == next_fp);
      write_body_preserves_fl_valid_aux_impl g dst_obj addr v next_fp (fuel - 1);
      AllocLemmas.fl_valid_step g' fp fuel
    end else begin
      AllocLemmas.fl_valid_step g' fp fuel
    end
  end
#pop-options

let write_body_preserves_fl_valid_aux
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel)
    (ensures AllocLemmas.fl_valid (write_word g addr v) fp fuel) =
  write_body_preserves_fl_valid_aux_impl g dst_obj addr v fp fuel

/// ---------------------------------------------------------------------------
/// write_body_preserves_not_in_fl_chain
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let rec write_body_preserves_not_in_fl_chain_impl
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
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
    if U64.v dst_obj < U64.v fp then begin
      objects_separated zero_addr g dst_obj fp_obj;
      wosize_of_object_spec dst_obj g;
      read_write_different g addr (fp <: hp_addr) v
    end else begin
      objects_separated zero_addr g fp_obj dst_obj;
      wosize_of_object_spec fp_obj g;
      read_write_different g addr (fp <: hp_addr) v
    end;
    let g' = write_word g addr v in
    let hd = hd_address fp_obj in
    hd_address_spec fp_obj;
    if U64.v hd + 16 <= heap_size then begin
      let next_fp = read_word g fp_obj in
      assert (read_word g' fp_obj == next_fp);
      write_body_preserves_not_in_fl_chain_impl g dst_obj addr v next_fp (fuel - 1)
    end else ()
  end
#pop-options

let write_body_preserves_not_in_fl_chain
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel)
    (ensures not_in_fl_chain (write_word g addr v) fp dst_obj fuel) =
  write_body_preserves_not_in_fl_chain_impl g dst_obj addr v fp fuel

/// ---------------------------------------------------------------------------
/// write_body_preserves_fl_chain_terminates
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
private let rec write_body_preserves_fl_chain_terminates_impl
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
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
    AllocLemmas.fl_chain_terminates_valid_zero g fp
  end
  else begin
    assert (fp <> dst_obj);
    let fp_obj : obj_addr = fp in
    AllocLemmas.fl_valid_elim g fp fuel;
    if U64.v dst_obj < U64.v fp then begin
      objects_separated zero_addr g dst_obj fp_obj;
      wosize_of_object_spec dst_obj g;
      read_write_different g addr (fp <: hp_addr) v
    end else begin
      objects_separated zero_addr g fp_obj dst_obj;
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
      write_body_preserves_fl_chain_terminates_impl g dst_obj addr v next_fp (fuel - 1);
      AllocLemmas.fl_chain_terminates_step g' fp fuel
    end
  end
#pop-options

let write_body_preserves_fl_chain_terminates
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_chain_terminates g fp fuel /\
      not_in_fl_chain g fp dst_obj fuel /\
      AllocLemmas.fl_valid g fp fuel)
    (ensures AllocLemmas.fl_chain_terminates (write_word g addr v) fp fuel) =
  write_body_preserves_fl_chain_terminates_impl g dst_obj addr v fp fuel

/// ---------------------------------------------------------------------------
/// write_body_preserves_chain_avoids_self
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let write_body_preserves_chain_avoids_self
  (g: heap) (dst_obj: obj_addr) (addr: hp_addr) (v: U64.t)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
      Seq.mem dst_obj (objects zero_addr g) /\
      U64.v addr >= U64.v dst_obj /\
      U64.v addr < U64.v dst_obj + (U64.v (wosize_of_object dst_obj g) * 8) /\
      U64.v addr % 8 = 0 /\
      AllocLemmas.fl_valid g fp fuel /\
      AllocLemmas.chain_avoids g fp dst_obj fuel = true)
    (ensures AllocLemmas.chain_avoids (write_word g addr v) fp dst_obj fuel = true)
  = let g' = write_word g addr v in
    let aux (a: obj_addr) : Lemma
      (requires Seq.mem a (objects zero_addr g) /\
               U64.v (wosize_of_object a g) >= 1 /\
               U64.v (hd_address a) + 16 <= heap_size /\
               a <> dst_obj)
      (ensures read_word g' a == read_word g a)
    = hd_address_spec a;
      hd_address_spec dst_obj;
      wosize_of_object_spec dst_obj g;
      if U64.v a < U64.v dst_obj then begin
        objects_separated zero_addr g a dst_obj;
        read_write_different g addr (a <: hp_addr) v
      end else begin
        objects_separated zero_addr g dst_obj a;
        read_write_different g addr (a <: hp_addr) v
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    write_body_preserves_objects g dst_obj addr v;
    AllocLemmas.chain_avoids_transfer g g' fp dst_obj fuel
#pop-options

/// ---------------------------------------------------------------------------
/// copy_fields_preserves_objects_aux
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1"
let rec copy_fields_preserves_objects_aux
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n)
          (ensures
             objects zero_addr (copy_fields minor major src_obj dst_obj i n) ==
             objects zero_addr major)
          (decreases (n - i)) =
  if i >= n then
    copy_fields_base minor major src_obj dst_obj i n
  else begin
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then
      copy_fields_oob minor major src_obj (dst_obj <: U64.t) i n
    else begin
      // Unfold copy_fields via step lemma (copy_fields is abstract from fsti)
      copy_fields_step minor major src_obj dst_obj i n;
      let field_val = minor_read_field minor src_obj i in
      let dst_addr : hp_addr = U64.uint_to_t dst_offset in
      assert (U64.v dst_addr >= U64.v dst_obj);
      assert (U64.v dst_addr < U64.v dst_obj + U64.v (wosize_of_object dst_obj major) * 8);
      write_body_preserves_objects major dst_obj dst_addr field_val;
      let major' = write_word major dst_addr field_val in
      assert (objects zero_addr major' == objects zero_addr major);
      assert (Seq.mem dst_obj (objects zero_addr major') = true);
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

/// ---------------------------------------------------------------------------
/// copy_fields_preserves_fl_valid_aux
/// ---------------------------------------------------------------------------

let rec copy_fields_preserves_fl_valid_aux
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             not_in_fl_chain major fp dst_obj fuel)
          (ensures
             AllocLemmas.fl_valid (copy_fields minor major src_obj dst_obj i n) fp fuel)
          (decreases (n - i)) =
  if i >= n then
    copy_fields_base minor major src_obj dst_obj i n
  else begin
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then copy_fields_oob minor major src_obj (dst_obj <: U64.t) i n
    else begin
      copy_fields_step minor major src_obj dst_obj i n;
      let field_val = minor_read_field minor src_obj i in
      let dst_addr : hp_addr = U64.uint_to_t dst_offset in
      write_body_preserves_fl_valid_aux major dst_obj dst_addr field_val fp fuel;
      let major' = write_word major dst_addr field_val in
      write_body_preserves_objects major dst_obj dst_addr field_val;
      assert (objects zero_addr major' == objects zero_addr major);
      hd_address_spec dst_obj;
      read_write_different major dst_addr (hd_address dst_obj) field_val;
      wosize_of_object_spec dst_obj major';
      wosize_of_object_spec dst_obj major;
      write_body_preserves_not_in_fl_chain major dst_obj dst_addr field_val fp fuel;
      copy_fields_preserves_fl_valid_aux minor major' src_obj dst_obj (i + 1) n fp fuel
    end
  end

/// ---------------------------------------------------------------------------
/// copy_fields_preserves_fl_chain_terminates
/// ---------------------------------------------------------------------------

let rec copy_fields_preserves_fl_chain_terminates
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             AllocLemmas.fl_chain_terminates major fp fuel /\
             not_in_fl_chain major fp dst_obj fuel)
          (ensures
             AllocLemmas.fl_chain_terminates (copy_fields minor major src_obj dst_obj i n) fp fuel)
          (decreases (n - i)) =
  if i >= n then
    copy_fields_base minor major src_obj dst_obj i n
  else begin
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then copy_fields_oob minor major src_obj (dst_obj <: U64.t) i n
    else begin
      copy_fields_step minor major src_obj dst_obj i n;
      let field_val = minor_read_field minor src_obj i in
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

/// ---------------------------------------------------------------------------
/// copy_fields_preserves_chain_avoids_self
/// ---------------------------------------------------------------------------

let rec copy_fields_preserves_chain_avoids_self
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (i: nat) (n: nat)
  (fp: U64.t) (fuel: nat)
  : Lemma (requires
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             i <= n /\
             AllocLemmas.fl_valid major fp fuel /\
             AllocLemmas.chain_avoids major fp dst_obj fuel = true)
          (ensures
             AllocLemmas.chain_avoids (copy_fields minor major src_obj dst_obj i n) fp dst_obj fuel = true)
          (decreases (n - i)) =
  if i >= n then
    copy_fields_base minor major src_obj dst_obj i n
  else begin
    let dst_offset = U64.v dst_obj + i * 8 in
    if dst_offset + 8 > heap_size || dst_offset % 8 <> 0 then copy_fields_oob minor major src_obj (dst_obj <: U64.t) i n
    else begin
      copy_fields_step minor major src_obj dst_obj i n;
      let field_val = minor_read_field minor src_obj i in
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

/// ---------------------------------------------------------------------------
/// copy_fields_preserves_other
/// ---------------------------------------------------------------------------

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
      assert (U64.v a + 8 <= dst_offset \/ dst_offset + 8 <= U64.v a);
      read_write_different major dst_addr a field_val;
      assert (read_word major' a == read_word major a);
      copy_fields_preserves_other minor major' src_obj dst_obj (i + 1) n a
    end
#pop-options

/// ---------------------------------------------------------------------------
/// copy_fields_preserves_wfh_part1
/// ---------------------------------------------------------------------------

let copy_fields_preserves_wfh_part1
  (minor: minor_state) (major: heap)
  (src_obj: U64.t) (dst_obj: obj_addr) (n: nat)
  : Lemma (requires
             well_formed_heap_part1 major /\
             Seq.mem dst_obj (objects zero_addr major) /\
             U64.v dst_obj % 8 == 0 /\
             U64.v (wosize_of_object dst_obj major) >= n /\
             n > 0)
          (ensures
             well_formed_heap_part1 (copy_fields minor major src_obj dst_obj 0 n)) =
  let g' = copy_fields minor major src_obj dst_obj 0 n in
  copy_fields_preserves_objects_aux minor major src_obj dst_obj 0 n;
  assert (objects zero_addr g' == objects zero_addr major);
  let wz_dst = U64.v (wosize_of_object dst_obj major) in
  let aux (h: obj_addr) : Lemma
    (requires Seq.mem h (objects zero_addr major))
    (ensures U64.v (hd_address h) + 8 + U64.v (wosize_of_object h g') * 8 <= Seq.length g')
  = let hdr_addr = hd_address h in
    hd_address_spec h;
    hd_address_spec dst_obj;
    if U64.v h > U64.v dst_obj then begin
      objects_separated zero_addr major dst_obj h;
      wosize_of_object_spec dst_obj major;
      assert (U64.v h > U64.v dst_obj + wz_dst * 8)
    end else if U64.v h < U64.v dst_obj then begin
      ()
    end else begin
      ()
    end;
    assert (forall (k:nat). 0 <= k /\ k < n ==>
      (U64.v hdr_addr + 8 <= U64.v dst_obj + k * 8 \/ U64.v dst_obj + k * 8 + 8 <= U64.v hdr_addr));
    assert (U64.v dst_obj + (n - 1) * 8 + 8 <= heap_size);
    copy_fields_preserves_other minor major src_obj dst_obj 0 n hdr_addr;
    assert (read_word g' hdr_addr == read_word major hdr_addr);
    wosize_of_object_spec h g';
    wosize_of_object_spec h major;
    assert (wosize_of_object h g' == wosize_of_object h major)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
