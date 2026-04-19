/// ---------------------------------------------------------------------------
/// GC.Spec.Coalesce - Free-object coalescing pass
/// ---------------------------------------------------------------------------
///
/// Applied after sweep to merge adjacent blue (free) blocks into larger
/// free blocks, reducing fragmentation.
///
/// Design: Spec is defined separately from sweep, preserving all existing
/// sweep proofs. A Pulse implementation can fuse sweep + coalesce into a
/// single pass, proved equivalent to (coalesce ∘ sweep).
///
/// Key invariant: coalescing only writes to blue object regions.
/// Survivor (white) objects are byte-identical before and after.
///
/// After coalescing, merged blue blocks have:
///   - Header: correct merged wosize, blue color, tag 0
///   - Field 1: free list link
///   - Fields 2+: zeroed (to maintain well_formed_heap_part2)

module GC.Spec.Coalesce

#set-options "--z3rlimit 50 --fuel 2 --ifuel 1"

open FStar.Seq
open FStar.Mul

module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
module HeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator

/// ---------------------------------------------------------------------------
/// Post-sweep heap predicate
/// ---------------------------------------------------------------------------

/// A heap where all objects are white or blue (output of sweep)
let post_sweep (g: heap) : prop =
  well_formed_heap g /\
  (forall (x: obj_addr). Seq.mem x (objects 0UL g) ==>
    is_white x g \/ is_blue x g)

/// ---------------------------------------------------------------------------
/// Flush a blue run
/// ---------------------------------------------------------------------------

/// Flush accumulated blue run: write merged header, link to free list,
/// zero garbage fields.
///
/// - run_words = 0: no pending run, no-op
/// - run_words = 1: wosize=0 block (just header, no fields) — write header
///   but don't link to free list (no room for link pointer)
/// - run_words >= 2: wosize>=1 block — write header, link field 1, zero rest
///
/// Returns (updated_heap, new_free_list_head).

let flush_blue (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (heap & U64.t)
  = if run_words = 0 then (g, fp)
    else if U64.v first_blue < U64.v mword
         || U64.v first_blue >= heap_size
         || U64.v first_blue % U64.v mword <> 0
    then (g, fp)
    else
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      let wz = run_words - 1 in
      if wz >= pow2 54 then (g, fp)
      else begin
        FStar.Math.Lemmas.pow2_lt_compat 64 54;
        let wz_u64 : (x:U64.t{U64.v x < pow2 54}) = U64.uint_to_t wz in
        let hdr = Alloc.make_header wz_u64 Alloc.blue_bits 0UL in
        let g1 = write_word g hd hdr in
        if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
          assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
          let g2 = HeapGraph.set_field g1 fb 1UL fp in
          let zero_start_nat = U64.v fb + U64.v mword in
          if wz >= 2 && zero_start_nat < pow2 64 then
            let g3 = Alloc.zero_fields g2 (U64.uint_to_t zero_start_nat) (wz - 1) in
            (g3, fb)
          else
            (g2, fb)
        end
        else
          (g1, fp)
      end

/// ---------------------------------------------------------------------------
/// Coalesce pass
/// ---------------------------------------------------------------------------

/// Walk objects, merging consecutive blue runs.
///
/// g0: original post-sweep heap (used for color checks — avoids needing
///     to re-establish color properties on modified intermediate heaps)
/// g: current heap (modified by flush_blue calls)
/// first_blue: obj_addr of first blue in current run (unused when run_words=0)
/// run_words: total words accumulated in current blue run (0 = no pending run)
/// fp: free list pointer being threaded through

let rec coalesce_aux (g0: heap) (g: heap) (objs: seq obj_addr)
    (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : GTot (heap & U64.t) (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      flush_blue g first_blue run_words fp
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_blue obj g0 then
        let ws = U64.v (wosize_of_object obj g0) in
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        coalesce_aux g0 g rest new_first (run_words + ws + 1) fp
      else begin
        // White object: flush pending blue run, then continue
        let (g', fp') = flush_blue g first_blue run_words fp in
        coalesce_aux g0 g' rest 0UL 0 fp'
      end

/// Top-level coalesce: walk all objects, build fresh free list.
let coalesce (g: heap) : GTot (heap & U64.t) =
  coalesce_aux g g (objects 0UL g) 0UL 0 0UL

/// ---------------------------------------------------------------------------
/// Object region disjointness helper
/// ---------------------------------------------------------------------------

/// Addresses within one object's region are outside any other object's region.
/// Follows from objects_separated which shows non-overlapping layout.
#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"
val addr_in_object_outside_other
  (g: heap) (x o: obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      Seq.mem x (objects 0UL g) /\ Seq.mem o (objects 0UL g) /\
      is_white x g /\ is_blue o g /\
      U64.v addr >= U64.v (hd_address x) /\
      U64.v addr < U64.v (hd_address x) + (U64.v (wosize_of_object x g) + 1) * U64.v mword)
    (ensures
      U64.v addr + U64.v mword <= U64.v (hd_address o) \/
      U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g) + 1) * U64.v mword)

let addr_in_object_outside_other g x o addr =
  hd_address_spec x;
  hd_address_spec o;
  wosize_of_object_spec x g;
  wosize_of_object_spec o g;
  wosize_of_object_bound x g;
  wosize_of_object_bound o g;
  let wz_x = wosize_of_object x g in
  let wz_o = wosize_of_object o g in
  // x is white and o is blue → different colors → x ≠ o
  is_white_iff x g;
  is_blue_iff o g;
  assert (color_of_object x g = White);
  assert (color_of_object o g = Blue);
  assert (x <> o);
  if U64.v x < U64.v o then begin
    objects_separated 0UL g x o;
    // objects_separated gives: o > x + wosize_of_object_as_wosize(x,g) * 8
    assert (U64.v o > U64.v x + FStar.Mul.(U64.v wz_x * 8));
    // hd_address(o) = o - 8, hd_address(x) = x - 8
    // addr < hd(x) + (wz_x + 1) * 8 = x - 8 + (wz_x + 1) * 8 = x + wz_x * 8
    // o > x + wz_x * 8 → hd(o) = o - 8 >= x + wz_x * 8 = hd(x) + (wz_x + 1) * 8 > addr
    assert (U64.v addr < U64.v x + FStar.Mul.(U64.v wz_x * 8));
    assert (U64.v (hd_address o) >= U64.v x + FStar.Mul.(U64.v wz_x * 8));
    assert (U64.v addr + U64.v mword <= U64.v (hd_address o))
  end else begin
    assert (U64.v x > U64.v o);
    objects_separated 0UL g o x;
    // x > o + wosize_of_object_as_wosize(o,g) * 8
    assert (U64.v x > U64.v o + FStar.Mul.(U64.v wz_o * 8));
    // hd(x) = x - 8 >= o + wz_o * 8 = hd(o) + (wz_o + 1) * 8
    // addr >= hd(x) ≥ hd(o) + (wz_o + 1) * 8
    assert (U64.v (hd_address x) >= U64.v o + FStar.Mul.(U64.v wz_o * 8));
    assert (U64.v addr >= U64.v (hd_address o) + (U64.v wz_o + 1) * U64.v mword)
  end
#pop-options

/// For a white object x, any address in x's region is outside all blue objects' regions
val white_addr_outside_all_blue (g: heap) (x: obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      Seq.mem x (objects 0UL g) /\ is_white x g /\
      U64.v addr >= U64.v (hd_address x) /\
      U64.v addr < U64.v (hd_address x) + (U64.v (wosize_of_object x g) + 1) * U64.v mword)
    (ensures
      forall (o: obj_addr). Seq.mem o (objects 0UL g) /\ is_blue o g ==>
        (U64.v addr + U64.v mword <= U64.v (hd_address o) \/
         U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g) + 1) * U64.v mword))

let white_addr_outside_all_blue g x addr =
  let aux (o: obj_addr)
    : Lemma
      (requires Seq.mem o (objects 0UL g) /\ is_blue o g)
      (ensures U64.v addr + U64.v mword <= U64.v (hd_address o) \/
               U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g) + 1) * U64.v mword)
    = addr_in_object_outside_other g x o addr
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// zero_fields helpers
/// ---------------------------------------------------------------------------

/// zero_fields preserves heap length
let rec zero_fields_preserves_length (g: heap) (addr: U64.t) (n: nat)
  : Lemma (ensures Seq.length (Alloc.zero_fields g addr n) == Seq.length g)
          (decreases n)
  = if n = 0 then ()
    else if U64.v addr + 8 > heap_size then ()
    else if U64.v addr >= heap_size then ()
    else if U64.v addr % 8 <> 0 then ()
    else begin
      let g' = write_word g (addr <: hp_addr) 0UL in
      if U64.v addr + 8 >= pow2 64 then ()
      else zero_fields_preserves_length g' (U64.uint_to_t (U64.v addr + 8)) (n - 1)
    end

/// zero_fields preserves reads at addresses before the zeroed range
let rec zero_fields_preserves_before (g: heap) (start: U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires U64.v addr + U64.v mword <= U64.v start)
    (ensures read_word (Alloc.zero_fields g start n) addr == read_word g addr)
    (decreases n)
  = if n = 0 then ()
    else if U64.v start + 8 > heap_size then ()
    else if U64.v start >= heap_size then ()
    else if U64.v start % 8 <> 0 then ()
    else begin
      let g' = write_word g (start <: hp_addr) 0UL in
      read_write_different g (start <: hp_addr) addr 0UL;
      if U64.v start + 8 >= pow2 64 then ()
      else begin
        let next = U64.uint_to_t (U64.v start + 8) in
        zero_fields_preserves_before g' next (n - 1) addr
      end
    end

/// zero_fields preserves reads at addresses after the zeroed range
let rec zero_fields_preserves_after (g: heap) (start: U64.t) (n: nat) (addr: hp_addr)
  : Lemma
    (requires U64.v addr >= U64.v start + n * U64.v mword)
    (ensures read_word (Alloc.zero_fields g start n) addr == read_word g addr)
    (decreases n)
  = if n = 0 then ()
    else if U64.v start + 8 > heap_size then ()
    else if U64.v start >= heap_size then ()
    else if U64.v start % 8 <> 0 then ()
    else begin
      let g' = write_word g (start <: hp_addr) 0UL in
      read_write_different g (start <: hp_addr) addr 0UL;
      if U64.v start + 8 >= pow2 64 then ()
      else begin
        let next = U64.uint_to_t (U64.v start + 8) in
        zero_fields_preserves_after g' next (n - 1) addr
      end
    end

/// ---------------------------------------------------------------------------
/// Flush locality: writes stay within the blue run
/// ---------------------------------------------------------------------------

/// flush_blue preserves reads at addresses outside [hd_address fb, hd_address fb + run_words*8)
val flush_blue_preserves_outside
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (addr: hp_addr)
  : Lemma
    (requires run_words > 0 ==>
      (U64.v first_blue >= U64.v mword /\
       U64.v first_blue < heap_size /\
       U64.v first_blue % U64.v mword == 0 /\
       (U64.v addr + U64.v mword <= U64.v first_blue - U64.v mword \/
        U64.v addr >= U64.v first_blue - U64.v mword + run_words * U64.v mword)))
    (ensures read_word (fst (flush_blue g first_blue run_words fp)) addr
          == read_word g addr)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let flush_blue_preserves_outside g first_blue run_words fp addr =
  if run_words = 0 then ()
  else if U64.v first_blue < U64.v mword
       || U64.v first_blue >= heap_size
       || U64.v first_blue % U64.v mword <> 0
  then ()
  else
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    hd_address_spec fb;
    let wz = run_words - 1 in
    if wz >= pow2 54 then ()
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      let wz_u64 : (x:U64.t{U64.v x < pow2 54}) = U64.uint_to_t wz in
      let hdr = Alloc.make_header wz_u64 Alloc.blue_bits 0UL in
      let g1 = write_word g hd hdr in
      assert (hd <> addr);
      read_write_different g hd addr hdr;
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
        let field1_addr : hp_addr = U64.add (hd_address fb) (U64.mul mword 1UL) in
        assert (U64.v field1_addr == U64.v fb);
        assert (field1_addr <> addr);
        let g2 = HeapGraph.set_field g1 fb 1UL fp in
        read_write_different g1 field1_addr addr fp;
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then begin
          let zero_start = U64.uint_to_t zero_start_nat in
          if U64.v addr + U64.v mword <= U64.v zero_start then
            zero_fields_preserves_before g2 zero_start (wz - 1) addr
          else
            zero_fields_preserves_after g2 zero_start (wz - 1) addr
        end else ()
      end
      else ()
    end
#pop-options

/// flush_blue preserves heap length
val flush_blue_preserves_length
  (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (Seq.length (fst (flush_blue g first_blue run_words fp)) == Seq.length g)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let flush_blue_preserves_length g first_blue run_words fp =
  if run_words = 0 then ()
  else if U64.v first_blue < U64.v mword
       || U64.v first_blue >= heap_size
       || U64.v first_blue % U64.v mword <> 0
  then ()
  else
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    let wz = run_words - 1 in
    if wz >= pow2 54 then ()
    else begin
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      let wz_u64 : (x:U64.t{U64.v x < pow2 54}) = U64.uint_to_t wz in
      let hdr = Alloc.make_header wz_u64 Alloc.blue_bits 0UL in
      let g1 = write_word g hd hdr in
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.v (hd_address fb) + U64.v mword * (U64.v 1UL + 1) <= heap_size);
        let g2 = HeapGraph.set_field g1 fb 1UL fp in
        let zero_start_nat = U64.v fb + U64.v mword in
        if wz >= 2 && zero_start_nat < pow2 64 then
          zero_fields_preserves_length g2 (U64.uint_to_t zero_start_nat) (wz - 1)
        else ()
      end
      else ()
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Coalesce preserves survivor data
/// ---------------------------------------------------------------------------

/// Helper: coalesce_aux preserves reads at addresses outside all blue regions
/// and outside the pending run.
///
/// Key strengthening: objs == objects start g0 links the remaining objects
/// to the heap walk structure, enabling contiguity proofs.
val coalesce_aux_preserves_outside
  (g0: heap) (g: heap) (start: hp_addr) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  (all_objs: seq obj_addr) (addr: hp_addr)
  : Lemma
    (requires
      objs == objects start g0 /\
      all_objs == objects 0UL g0 /\
      Seq.length g0 == Seq.length g /\
      // all objects in objs are also in all_objs
      (forall (o: obj_addr). Seq.mem o objs ==> Seq.mem o all_objs) /\
      // addr is outside the pending blue run
      (run_words > 0 ==>
        (U64.v first_blue >= U64.v mword /\
         U64.v first_blue < heap_size /\
         U64.v first_blue % U64.v mword == 0 /\
         U64.v first_blue - U64.v mword + run_words * U64.v mword == U64.v start /\
         (U64.v addr + U64.v mword <= U64.v first_blue - U64.v mword \/
          U64.v addr >= U64.v first_blue - U64.v mword + run_words * U64.v mword))) /\
      // addr is outside every blue object's region in the full objects list
      (forall (o: obj_addr). Seq.mem o all_objs /\ is_blue o g0 ==>
        (U64.v addr + U64.v mword <= U64.v (hd_address o) \/
         U64.v addr >= U64.v (hd_address o) + (U64.v (wosize_of_object o g0) + 1) * U64.v mword)))
    (ensures read_word (fst (coalesce_aux g0 g objs first_blue run_words fp)) addr
          == read_word g addr)
    (decreases Seq.length objs)

/// Geometric helper: extending a blue run preserves the "addr outside" property.
/// When run_words = 0, the run starts fresh at obj.
/// When run_words > 0, the old run is contiguous with obj.
#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
val extend_run_preserves_outside
  (addr: hp_addr) (first_blue: U64.t) (run_words: nat) (obj: obj_addr) (ws: nat)
  (start_val: nat)
  : Lemma
    (requires
      // obj starts at start_val
      U64.v (hd_address obj) == start_val /\
      (run_words > 0 ==>
        (U64.v first_blue >= U64.v mword /\
         U64.v first_blue < heap_size /\
         U64.v first_blue % U64.v mword == 0 /\
         U64.v first_blue - U64.v mword + run_words * U64.v mword == start_val /\
         (U64.v addr + U64.v mword <= U64.v first_blue - U64.v mword \/
          U64.v addr >= U64.v first_blue - U64.v mword + run_words * U64.v mword))) /\
      // addr outside obj region
      (U64.v addr + U64.v mword <= U64.v (hd_address obj) \/
       U64.v addr >= U64.v (hd_address obj) + (ws + 1) * U64.v mword))
    (ensures (
      let new_first = if run_words = 0 then obj else first_blue in
      let new_rw = run_words + ws + 1 in
      U64.v new_first >= U64.v mword /\
      U64.v new_first < heap_size /\
      U64.v new_first % U64.v mword == 0 /\
      (U64.v addr + U64.v mword <= U64.v new_first - U64.v mword \/
       U64.v addr >= U64.v new_first - U64.v mword + new_rw * U64.v mword)))

let extend_run_preserves_outside addr first_blue run_words obj ws start_val =
  hd_address_spec obj;
  if run_words = 0 then begin
    // new_first = obj, new run = [hd(obj), hd(obj) + (ws+1)*8)
    // addr outside obj region gives exactly what we need
    assert (U64.v obj >= U64.v mword);  // obj_addr >= 8
    ()
  end else begin
    // Contiguity: first_blue - 8 + run_words * 8 = start_val = hd(obj)
    // old run: [first_blue - 8, first_blue - 8 + run_words * 8) = [first_blue - 8, start_val)
    // obj: [start_val, start_val + (ws+1)*8)
    // extended run: [first_blue - 8, first_blue - 8 + (run_words + ws + 1) * 8)
    //             = [first_blue - 8, start_val + (ws+1)*8)
    //
    // addr outside old run: addr + 8 <= first_blue - 8  ∨  addr >= start_val
    // addr outside obj: addr + 8 <= start_val  ∨  addr >= start_val + (ws+1)*8
    //
    // Case analysis:
    //   addr + 8 <= first_blue - 8 ==> addr + 8 <= new_first - 8 ✓
    //   addr >= start_val ∧ addr + 8 <= start_val ==> impossible (addr >= start_val > start_val - 8 >= addr)
    //   addr >= start_val ∧ addr >= start_val + (ws+1)*8 ==> addr >= start_val + (ws+1)*8
    //     = addr >= first_blue - 8 + run_words * 8 + (ws+1)*8
    //     = addr >= first_blue - 8 + (run_words + ws + 1) * 8 ✓
    ()
  end
#pop-options

/// When objects walk ends (next >= heap_size), tail is empty.
/// This follows from the objects definition with fuel 2.
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
val objects_tail_empty_when_done (start: hp_addr) (g: heap)
  : Lemma
    (requires
      Seq.length (objects start g) > 0 /\
      (let wz = getWosize (read_word g start) in
       let next = U64.v start + (U64.v wz + 1) * U64.v mword in
       next <= Seq.length g /\ next < pow2 64 /\ next >= heap_size))
    (ensures Seq.tail (objects start g) == Seq.empty)

let objects_tail_empty_when_done start g = ()
#pop-options

#push-options "--z3rlimit 400 --fuel 2 --ifuel 1"
let rec coalesce_aux_preserves_outside g0 g start objs first_blue run_words fp all_objs addr =
  if Seq.length objs = 0 then
    flush_blue_preserves_outside g first_blue run_words fp addr
  else begin
    objects_nonempty_next start g0;
    let header = read_word g0 start in
    let wz = getWosize header in
    let obj = f_address start in
    f_address_spec start;
    hd_address_spec obj;
    assert (U64.v (hd_address obj) == U64.v start);
    let rest_start_nat = U64.v start + (U64.v wz + 1) * U64.v mword in
    assert (obj == Seq.head objs);
    wosize_of_object_spec obj g0;
    let ws = U64.v (wosize_of_object obj g0) in
    assert (ws == U64.v wz);
    // obj ∈ objs (it's the head), and objs ⊆ all_objs, so obj ∈ all_objs
    mem_cons_lemma obj obj (Seq.tail objs);
    assert (Seq.mem obj objs);
    // Establish subset: tail ⊆ objs ⊆ all_objs for the recursive call
    let tail_subset (o: obj_addr)
      : Lemma (Seq.mem o (Seq.tail objs) ==> Seq.mem o all_objs)
      = mem_cons_lemma o obj (Seq.tail objs)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires tail_subset);
    if is_blue obj g0 then begin
      let new_first : U64.t = if run_words = 0 then obj else first_blue in
      extend_run_preserves_outside addr first_blue run_words obj ws (U64.v start);

      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        // objects_nonempty_next gives: objects start g0 == cons obj (objects next g0)
        // So tail objs == objects next g0
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);
        assert (U64.v new_first - U64.v mword + (run_words + ws + 1) * U64.v mword == rest_start_nat);
        coalesce_aux_preserves_outside g0 g next (Seq.tail objs)
          new_first (run_words + ws + 1) fp all_objs addr
      end else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.tail objs == Seq.empty);
        flush_blue_preserves_outside g new_first (run_words + ws + 1) fp addr
      end
    end
    else begin
      let (g', fp') = flush_blue g first_blue run_words fp in
      flush_blue_preserves_outside g first_blue run_words fp addr;
      flush_blue_preserves_length g first_blue run_words fp;
      if rest_start_nat < heap_size then begin
        let next : hp_addr = U64.uint_to_t rest_start_nat in
        Seq.lemma_tl obj (objects next g0);
        assert (Seq.tail objs == objects next g0);
        coalesce_aux_preserves_outside g0 g' next (Seq.tail objs) 0UL 0 fp' all_objs addr
      end else begin
        objects_tail_empty_when_done start g0;
        assert (Seq.tail objs == Seq.empty)
      end
    end
  end
#pop-options

/// Coalesce preserves survivor headers
val coalesce_preserves_survivor_header (g: heap) (x: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem x (objects 0UL g) /\ is_white x g)
    (ensures read_word (fst (coalesce g)) (hd_address x)
          == read_word g (hd_address x))

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let coalesce_preserves_survivor_header g x =
  hd_address_spec x;
  wosize_of_object_bound x g;
  let addr = hd_address x in
  white_addr_outside_all_blue g x addr;
  coalesce_aux_preserves_outside g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) addr
#pop-options

/// Coalesce preserves survivor fields
val coalesce_preserves_survivor_field
  (g: heap) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma
    (requires post_sweep g /\
             Seq.mem x (objects 0UL g) /\ is_white x g /\
             U64.v i <= U64.v (wosize_of_object x g))
    (ensures HeapGraph.get_field (fst (coalesce g)) x i
          == HeapGraph.get_field g x i)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
let coalesce_preserves_survivor_field g x i =
  hd_address_spec x;
  wosize_of_object_bound x g;
  let hd = hd_address x in
  if U64.v hd + U64.v mword * U64.v i + U64.v mword <= heap_size then begin
    let field_addr_nat = U64.v hd + U64.v mword * U64.v i in
    assert (field_addr_nat < heap_size);
    assert (field_addr_nat % U64.v mword == 0);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (field_addr_nat < pow2 64);
    let field_addr : hp_addr = U64.uint_to_t field_addr_nat in
    // field_addr is in x's region: hd(x) <= field_addr < hd(x) + (wz+1)*8
    // since field index i >= 1 and i <= wz, field_addr = hd + i*8 where hd = x-8
    white_addr_outside_all_blue g x field_addr;
    coalesce_aux_preserves_outside g g 0UL (objects 0UL g) 0UL 0 0UL (objects 0UL g) field_addr
  end else ()
#pop-options

/// ---------------------------------------------------------------------------
/// Well-formedness of coalesced heap
/// ---------------------------------------------------------------------------

val coalesce_preserves_wf (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures well_formed_heap (fst (coalesce g)))

let coalesce_preserves_wf g = admit ()

/// ---------------------------------------------------------------------------
/// Color postcondition
/// ---------------------------------------------------------------------------

val coalesce_all_white_or_blue (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (forall (x: obj_addr).
               Seq.mem x (objects 0UL (fst (coalesce g))) ==>
               is_white x (fst (coalesce g)) \/ is_blue x (fst (coalesce g))))

let coalesce_all_white_or_blue g = admit ()

/// ---------------------------------------------------------------------------
/// Survivors appear in coalesced objects
/// ---------------------------------------------------------------------------

val coalesce_survivors_in_objects (g: heap) (x: obj_addr)
  : Lemma
    (requires post_sweep g /\ Seq.mem x (objects 0UL g) /\ is_white x g)
    (ensures Seq.mem x (objects 0UL (fst (coalesce g))))

let coalesce_survivors_in_objects g x = admit ()

/// ---------------------------------------------------------------------------
/// Free list validity
/// ---------------------------------------------------------------------------

/// The coalesce result's free pointer is null or in the new objects set
val coalesce_fp_valid (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures (let (g', fp') = coalesce g in
             fp' = 0UL \/
             (U64.v fp' >= U64.v mword /\
              U64.v fp' < heap_size /\
              U64.v fp' % U64.v mword == 0 /\
              Seq.mem (fp' <: obj_addr) (objects 0UL g'))))

let coalesce_fp_valid g = admit ()

/// ---------------------------------------------------------------------------
/// Heap length preservation
/// ---------------------------------------------------------------------------

/// Heap length preservation
/// ---------------------------------------------------------------------------

let rec coalesce_aux_preserves_length
  (g0: heap) (g: heap) (objs: seq obj_addr)
  (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : Lemma (ensures Seq.length (fst (coalesce_aux g0 g objs first_blue run_words fp)) == Seq.length g)
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      flush_blue_preserves_length g first_blue run_words fp
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_blue obj g0 then
        let ws = U64.v (wosize_of_object obj g0) in
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        coalesce_aux_preserves_length g0 g rest new_first (run_words + ws + 1) fp
      else begin
        let (g', fp') = flush_blue g first_blue run_words fp in
        flush_blue_preserves_length g first_blue run_words fp;
        coalesce_aux_preserves_length g0 g' rest 0UL 0 fp'
      end

val coalesce_preserves_length (g: heap)
  : Lemma
    (requires post_sweep g)
    (ensures Seq.length (fst (coalesce g)) == Seq.length g)

let coalesce_preserves_length g =
  coalesce_aux_preserves_length g g (objects 0UL g) 0UL 0 0UL
