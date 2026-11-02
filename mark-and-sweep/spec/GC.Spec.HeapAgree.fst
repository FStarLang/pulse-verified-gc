module GC.Spec.HeapAgree

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
module HeapGraph = GC.Spec.HeapGraph
module HeapModel = GC.Spec.HeapModel
module Mark = GC.Spec.Mark
module FL = GC.Spec.FreeList
module AllocCommon = GC.Spec.Allocator.Lemmas.Common
module AllocChain = GC.Spec.Allocator.Lemmas.Chain

#set-options "--z3rlimit 20 --fuel 1 --ifuel 1"

/// ---------------------------------------------------------------------------
/// Building `walk_agree`
/// ---------------------------------------------------------------------------

let rec walk_agree_of_equal_from (start: hp_addr) (h1 h2: heap)
  : Lemma (requires forall (a: hp_addr). U64.v a >= U64.v start ==> read_word h1 a == read_word h2 a)
          (ensures walk_agree start h1 h2)
          (decreases (heap_size - U64.v start))
  = if U64.v start + 8 >= heap_size then ()
    else begin
      let wz = getWosize (read_word h2 start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size then ()
      else begin
        walk_next_aligned start (U64.v wz);
        f_address_spec start;
        hd_f_roundtrip start;
        if next < heap_size then walk_agree_of_equal_from (U64.uint_to_t next) h1 h2
      end
    end

let walk_agree_step (start: hp_addr) (h1 h2: heap) = ()

/// ---------------------------------------------------------------------------
/// Walking `walk_agree`
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let rec walk_agree_objects (start: hp_addr) (h1 h2: heap)
  : Lemma (requires walk_agree start h1 h2)
          (ensures objects start h1 == objects start h2 /\
                   (forall (b: obj_addr). Seq.mem b (objects start h2) ==> block_agree h1 h2 b))
          (decreases (heap_size - U64.v start))
  = if U64.v start + 8 >= heap_size then ()
    else begin
      let wz = getWosize (read_word h2 start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size then ()
      else begin
        walk_next_aligned start (U64.v wz);
        f_address_spec start;
        let b0 = f_address start in
        if next < heap_size then begin
          let nx : hp_addr = U64.uint_to_t next in
          walk_agree_objects nx h1 h2;
          objects_cons_step_to start h1 nx;
          objects_cons_step_to start h2 nx;
          let aux (b: obj_addr)
            : Lemma (Seq.mem b (objects start h2) ==> block_agree h1 h2 b)
            = mem_cons_lemma b b0 (objects nx h2)
          in
          FStar.Classical.forall_intro aux
        end else begin
          objects_cons_end start h1;
          objects_cons_end start h2;
          let aux (b: obj_addr)
            : Lemma (Seq.mem b (objects start h2) ==> block_agree h1 h2 b)
            = mem_cons_lemma b b0 Seq.empty
          in
          FStar.Classical.forall_intro aux
        end
      end
    end
#pop-options

let agree_objects (h1 h2: heap) = walk_agree_objects zero_addr h1 h2

#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let agree_block (h1 h2: heap) (b: obj_addr) =
  walk_agree_objects zero_addr h1 h2;
  assert (block_agree h1 h2 b);
  color_of_header_eq b h1 h2;
  color_of_object_spec b h1;
  color_of_object_spec b h2;
  wosize_of_object_spec b h1;
  wosize_of_object_spec b h2;
  tag_of_object_spec b h1;
  tag_of_object_spec b h2;
  is_no_scan_spec b h1;
  is_no_scan_spec b h2;
  resolve_object_locality b h1 h2
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let agree_get_field (h1 h2: heap) (b: obj_addr) (i: U64.t{U64.v i >= 1}) =
  agree_block h1 h2 b;
  hd_address_spec b;
  wosize_of_object_bound b h2;
  if U64.v (hd_address b) + U64.v mword * U64.v i + U64.v mword <= heap_size then begin
    HeapGraph.get_field_addr_eq h1 b i;
    HeapGraph.get_field_addr_eq h2 b i
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Field targets
/// ---------------------------------------------------------------------------

/// `exists_field_pointing_to_unchecked` reads only the words it scans.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
private let rec efptu_congr (h1 h2: heap) (src: obj_addr) (wz: U64.t{U64.v wz < pow2 54})
    (dst: obj_addr)
  : Lemma (requires forall (a: hp_addr).
                      U64.v a >= U64.v src /\ U64.v a + 8 <= U64.v src + U64.v wz * 8 ==>
                      read_word h1 a == read_word h2 a)
          (ensures exists_field_pointing_to_unchecked h1 src wz dst ==
                   exists_field_pointing_to_unchecked h2 src wz dst)
          (decreases U64.v wz)
  = if wz = 0UL then ()
    else begin
      let idx = U64.sub wz 1UL in
      FStar.Math.Lemmas.pow2_plus 54 3;
      assert_norm (pow2 3 == 8);
      assert (U64.v idx * 8 < pow2 57);
      FStar.Math.Lemmas.pow2_lt_compat 64 57;
      FStar.Math.Lemmas.small_mod (U64.v idx * 8) (pow2 64);
      assert (U64.v (U64.mul_mod idx mword) == U64.v idx * 8);
      FStar.Math.Lemmas.pow2_double_sum 57;
      FStar.Math.Lemmas.pow2_lt_compat 64 58;
      FStar.Math.Lemmas.small_mod (U64.v src + U64.v idx * 8) (pow2 64);
      assert (U64.v (U64.add_mod src (U64.mul_mod idx mword)) == U64.v src + U64.v idx * 8);
      efptu_congr h1 h2 src idx dst
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let agree_points_to (h1 h2: heap) (src dst: obj_addr) =
  agree_block h1 h2 src;
  wosize_of_object_bound src h2;
  efptu_congr h1 h2 src (wosize_of_object src h2) dst
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let agree_target (h1 h2: heap) (src dst: obj_addr) =
  wf_parts ();
  agree_objects h1 h2;
  let objs = objects zero_addr h2 in
  wosize_of_object_bound src h2;
  wfh_part2_elim h2 src dst;
  wfh_part3_elim h2 src dst;
  let r = resolve_object dst h2 in
  assert (~(is_blue r h2));
  if is_infix dst h2 then begin
    infix_addr_wf_elim h2 objs dst;
    let w = U64.v (wosize_of_object dst h2) in
    let p : obj_addr = U64.uint_to_t (U64.v dst - w * 8) in
    parent_closure_addr_nat_spec dst h2;
    resolve_infix_spec dst h2;
    assert (r == p);
    agree_block h1 h2 p;
    hd_address_spec dst;
    let a : hp_addr = hd_address dst in
    assert (U64.v a >= U64.v p);
    assert (U64.v a + 8 <= U64.v p + U64.v (wosize_of_object p h2) * 8);
    resolve_object_locality dst h1 h2
  end else begin
    resolve_non_infix dst h2;
    agree_block h1 h2 dst;
    resolve_object_locality dst h1 h2
  end
#pop-options

/// ---------------------------------------------------------------------------
/// Transferred properties
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let agree_wfh_part1 (h1 h2: heap) =
  agree_objects h1 h2;
  let p1 (h: obj_addr)
    : Lemma (Seq.mem h (objects zero_addr h1) ==>
             (let wz = wosize_of_object h h1 in
              U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length h1))
    = if Seq.mem h (objects zero_addr h2) then agree_block h1 h2 h
  in
  FStar.Classical.forall_intro p1

let agree_white_or_blue (h1 h2: heap) =
  agree_objects h1 h2;
  let c (x: obj_addr)
    : Lemma (Seq.mem x (objects zero_addr h1) ==> is_white x h1 \/ is_blue x h1)
    = if Seq.mem x (objects zero_addr h2) then agree_block h1 h2 x
  in
  FStar.Classical.forall_intro c
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let agree_well_formed_heap (h1 h2: heap) =
  wf_parts ();
  agree_objects h1 h2;
  let objs = objects zero_addr h2 in
  let p1 (h: obj_addr)
    : Lemma (Seq.mem h (objects zero_addr h1) ==>
             (let wz = wosize_of_object h h1 in
              U64.v (hd_address h) + 8 + (U64.v wz * 8) <= Seq.length h1))
    = if Seq.mem h objs then agree_block h1 h2 h
  in
  FStar.Classical.forall_intro p1;
  assert (well_formed_heap_part1 h1);
  let p4 (h: obj_addr)
    : Lemma (Seq.mem h (objects zero_addr h1) ==> ~(is_infix h h1))
    = if Seq.mem h objs then agree_block h1 h2 h
  in
  FStar.Classical.forall_intro p4;
  assert (well_formed_heap_part4 h1);
  let to_h2 (src dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr h1) /\ fields_constrained h1 src /\
                      (let wz = wosize_of_object src h1 in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked h1 src wz dst))
            (ensures Seq.mem src objs /\ fields_constrained h2 src /\ points_to h2 src dst /\
                     resolve_object dst h1 == resolve_object dst h2 /\
                     is_infix dst h1 == is_infix dst h2 /\
                     wosize_of_object dst h1 == wosize_of_object dst h2 /\
                     Seq.mem (resolve_object dst h2) objs /\
                     infix_addr_wf h2 objs dst)
    = agree_block h1 h2 src;
      agree_points_to h1 h2 src dst;
      agree_target h1 h2 src dst;
      wosize_of_object_bound src h2;
      wfh_part3_elim h2 src dst
  in
  let pf2 (src dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr h1) /\ fields_constrained h1 src /\
                      (let wz = wosize_of_object src h1 in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked h1 src wz dst))
            (ensures Seq.mem (resolve_object dst h1) (objects zero_addr h1))
    = to_h2 src dst
  in
  well_formed_heap_part2_intro h1 pf2;
  let pf3 (src dst: obj_addr)
    : Lemma (requires Seq.mem src (objects zero_addr h1) /\ fields_constrained h1 src /\
                      (let wz = wosize_of_object src h1 in
                       U64.v wz < pow2 54 /\
                       exists_field_pointing_to_unchecked h1 src wz dst))
            (ensures infix_addr_wf h1 (objects zero_addr h1) dst)
    = to_h2 src dst;
      if is_infix dst h2 then begin
        infix_addr_wf_elim h2 objs dst;
        let w = U64.v (wosize_of_object dst h2) in
        let p : obj_addr = U64.uint_to_t (U64.v dst - w * 8) in
        agree_block h1 h2 p
      end;
      infix_addr_wf_transfer h2 h1 objs (objects zero_addr h1) dst
  in
  well_formed_heap_part3_intro h1 pf3
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let agree_no_pointer_to_blue (h1 h2: heap) =
  agree_objects h1 h2;
  let aux (src dst: obj_addr)
    : Lemma (Seq.mem src (objects zero_addr h1) /\ ~(is_blue src h1) /\
             fields_constrained h1 src /\ points_to h1 src dst ==>
             ~(is_blue (resolve_object dst h1) h1))
    = if Seq.mem src (objects zero_addr h1) && not (is_blue src h1) &&
         fields_constrained h1 src && points_to h1 src dst then begin
        agree_block h1 h2 src;
        agree_points_to h1 h2 src dst;
        agree_target h1 h2 src dst;
        agree_block h1 h2 (resolve_object dst h2)
      end
  in
  FStar.Classical.forall_intro_2 aux
#pop-options

/// ---------------------------------------------------------------------------
/// The graph
/// ---------------------------------------------------------------------------

/// A pointer field of a live, scannable block resolves the same way in both heaps.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
private let agree_field_resolve (h1 h2: heap) (b: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ agree_target_pre h2 /\
                    Seq.mem b (objects zero_addr h2) /\ fields_constrained h2 b /\
                    U64.v j <= U64.v (wosize_of_object b h2))
          (ensures (let v = HeapGraph.get_field h2 b j in
                    HeapGraph.get_field h1 b j == v /\
                    HeapGraph.resolve_field h1 v == HeapGraph.resolve_field h2 v))
  = agree_get_field h1 h2 b j;
    let v = HeapGraph.get_field h2 b j in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let vo : obj_addr = v in
      wf_parts ();
      let wz = wosize_of_object b h2 in
      wosize_of_object_bound b h2;
      wf_object_size_bound h2 b;
      hd_address_spec b;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      HeapGraph.get_field_addr_eq h2 b j;
      field_read_implies_exists_pointing h2 b wz (U64.sub j 1UL) vo;
      assert (points_to h2 b vo);
      agree_target h1 h2 b vo
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let rec agree_gpf_aux (h1 h2: heap) (b: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ agree_target_pre h2 /\
                    Seq.mem b (objects zero_addr h2) /\ fields_constrained h2 b /\
                    ws == wosize_of_object b h2)
          (ensures HeapGraph.get_pointer_fields_aux h1 b i ws ==
                   HeapGraph.get_pointer_fields_aux h2 b i ws)
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else begin
      agree_field_resolve h1 h2 b i;
      if U64.v i < U64.v ws then agree_gpf_aux h1 h2 b (U64.add i 1UL) ws
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let agree_object_edges (h1 h2: heap) (b: obj_addr)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ agree_target_pre h2 /\
                    Seq.mem b (objects zero_addr h2))
          (ensures HeapGraph.object_edges h1 b == HeapGraph.object_edges h2 b)
  = agree_block h1 h2 b;
    if fields_constrained h2 b && HeapGraph.object_fits_in_heap b h2 then
      agree_gpf_aux h1 h2 b 1UL (wosize_of_object b h2)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let rec agree_all_edges (h1 h2: heap) (objs: seq obj_addr)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ agree_target_pre h2 /\
                    (forall (b: obj_addr). Seq.mem b objs ==> Seq.mem b (objects zero_addr h2)))
          (ensures HeapGraph.all_edges h1 objs == HeapGraph.all_edges h2 objs)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else begin
      Seq.Properties.lemma_mem_append (Seq.create 1 (Seq.head objs)) (Seq.tail objs);
      Seq.Properties.cons_head_tail objs;
      mem_cons_lemma (Seq.head objs) (Seq.head objs) (Seq.tail objs);
      let tl_sub (b: obj_addr) : Lemma (Seq.mem b (Seq.tail objs) ==> Seq.mem b objs)
        = mem_cons_lemma b (Seq.head objs) (Seq.tail objs)
      in
      FStar.Classical.forall_intro tl_sub;
      agree_object_edges h1 h2 (Seq.head objs);
      agree_all_edges h1 h2 (Seq.tail objs)
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let agree_create_graph (h1 h2: heap) =
  agree_objects h1 h2;
  agree_all_edges h1 h2 (objects zero_addr h2);
  HeapModel.objects_is_vertex_set h2;
  assert (HeapModel.create_graph h1 ==
          HeapGraph.create_graph_from_heap h1 (objects zero_addr h2));
  assert (HeapModel.create_graph h2 ==
          HeapGraph.create_graph_from_heap h2 (objects zero_addr h2))
#pop-options

/// ---------------------------------------------------------------------------
/// The free list
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let agree_field0 (h1 h2: heap) (b: obj_addr) =
  agree_block h1 h2 b
#pop-options

/// The per-object facts the allocator's transfer lemmas ask for.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let agree_alloc_facts (h1 h2: heap)
  : Lemma (requires heaps_agree_mod_free h1 h2)
          (ensures forall (a: obj_addr). Seq.mem a (objects zero_addr h2) ==>
                     Seq.mem a (objects zero_addr h1) /\
                     wosize_of_object a h1 == wosize_of_object a h2 /\
                     (U64.v (wosize_of_object a h2) >= 1 ==> read_word h1 a == read_word h2 a))
  = let aux (a: obj_addr)
      : Lemma (Seq.mem a (objects zero_addr h2) ==>
               Seq.mem a (objects zero_addr h1) /\
               wosize_of_object a h1 == wosize_of_object a h2 /\
               (U64.v (wosize_of_object a h2) >= 1 ==> read_word h1 a == read_word h2 a))
      = if Seq.mem a (objects zero_addr h2) then agree_block h1 h2 a
    in
    FStar.Classical.forall_intro aux
#pop-options

let agree_fl_valid (h1 h2: heap) (fp: U64.t) (fuel: nat) =
  agree_alloc_facts h1 h2;
  AllocChain.fl_valid_transfer h2 h1 fp fuel

let agree_fl_chain_terminates (h1 h2: heap) (fp: U64.t) (steps: nat) =
  agree_alloc_facts h1 h2;
  AllocChain.fl_chain_terminates_transfer h2 h1 fp steps

let agree_chain_avoids (h1 h2: heap) (fp excl: U64.t) (fuel: nat) =
  agree_alloc_facts h1 h2;
  AllocChain.chain_avoids_transfer h2 h1 fp excl fuel

/// Along a sound chain every link is a link of a free block, so the chain is
/// the same in both heaps.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let rec agree_on_fl (h1 h2: heap) (fp obj: U64.t) (n: nat)
  : Lemma (requires heaps_agree_mod_free h1 h2 /\ FL.fl_sound h2 fp)
          (ensures FL.on_fl h1 fp obj n == FL.on_fl h2 fp obj n)
          (decreases n)
  = if n = 0 || not (FL.fl_node fp) || fp = obj then ()
    else begin
      FL.on_fl_head h2 fp;
      assert (FL.reachable_on_fl h2 fp fp);
      agree_field0 h1 h2 (fp <: obj_addr);
      FL.fl_sound_tail h2 fp;
      agree_on_fl h1 h2 (FL.fl_next h2 fp) obj (n - 1)
    end
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let agree_fl_exact (h1 h2: heap) (fp: U64.t) =
  agree_objects h1 h2;
  let reach (obj: U64.t)
    : Lemma (FL.reachable_on_fl h1 fp obj <==> FL.reachable_on_fl h2 fp obj)
    = let n_eq (n: nat) : Lemma (FL.on_fl h1 fp obj n == FL.on_fl h2 fp obj n)
        = agree_on_fl h1 h2 fp obj n
      in
      FStar.Classical.forall_intro n_eq
  in
  FStar.Classical.forall_intro reach;
  let blk (x: obj_addr)
    : Lemma (Seq.mem x (objects zero_addr h2) ==>
             is_blue x h1 == is_blue x h2 /\ wosize_of_object x h1 == wosize_of_object x h2)
    = if Seq.mem x (objects zero_addr h2) then agree_block h1 h2 x
  in
  FStar.Classical.forall_intro blk
#pop-options

/// ---------------------------------------------------------------------------
/// Density
/// ---------------------------------------------------------------------------

/// Agreement from a position carries over to every later block on the walk.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let rec walk_agree_suffix (start: hp_addr) (h1 h2: heap) (b: obj_addr)
  : Lemma (requires walk_agree start h1 h2 /\ Seq.mem b (objects start h2))
          (ensures walk_agree (hd_address b) h1 h2)
          (decreases (heap_size - U64.v start))
  = let wz = getWosize (read_word h2 start) in
    let next = U64.v start + (U64.v wz + 1) * 8 in
    walk_next_aligned start (U64.v wz);
    f_address_spec start;
    hd_f_roundtrip start;
    let b0 = f_address start in
    if b = b0 then ()
    else if next < heap_size then begin
      let nx : hp_addr = U64.uint_to_t next in
      objects_cons_step_to start h2 nx;
      mem_cons_lemma b b0 (objects nx h2);
      walk_agree_suffix nx h1 h2 b
    end else begin
      objects_cons_end start h2;
      mem_cons_lemma b b0 Seq.empty
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let agree_dense (h1 h2: heap) =
  agree_objects h1 h2;
  reveal_opaque (`%heap_objects_dense) heap_objects_dense;
  let aux (start: hp_addr)
    : Lemma (U64.v start + 8 < heap_size ==>
             Seq.mem (f_address start) (objects zero_addr h1) ==>
             Seq.length (objects start h1) > 0 ==>
             (let wz = getWosize (read_word h1 start) in
              let next = U64.v start + ((U64.v wz + 1) * 8) in
              next + 8 < heap_size ==>
              Seq.length (objects (U64.uint_to_t next) h1) > 0 /\
              Seq.mem (f_address (U64.uint_to_t next)) (objects zero_addr h1)))
    = if U64.v start + 8 < heap_size && Seq.mem (f_address start) (objects zero_addr h2) then begin
        hd_f_roundtrip start;
        walk_agree_suffix zero_addr h1 h2 (f_address start);
        walk_agree_objects start h1 h2;
        let wz = getWosize (read_word h2 start) in
        let next = U64.v start + ((U64.v wz + 1) * 8) in
        if Seq.length (objects start h2) > 0 && next + 8 < heap_size then begin
          objects_nonempty_next start h2;
          let nx : hp_addr = U64.uint_to_t next in
          hd_f_roundtrip nx;
          walk_agree_suffix zero_addr h1 h2 (f_address nx);
          walk_agree_objects nx h1 h2
        end
      end
  in
  FStar.Classical.forall_intro aux
#pop-options
