/// ---------------------------------------------------------------------------
/// GC.Spec.SweepPar.Exec — executable twins of the fused sweep's ghost spec
///
/// `GC.Spec.SweepCoalesce.Defs.fused_sweep_coalesce` and everything it calls
/// (`is_black`, `wosize_of_object`, `makeWhite`, `flush_blue`, `objects`, ...)
/// are `GTot`, so extraction erases them.  To run the spec, this module gives
/// each one a `Tot` twin built from the same `Tot` primitives (`read_word`,
/// `write_word`, `getColor`, ...), and the twin's return type states that it
/// *is* the ghost original.  The extracted twin therefore computes exactly the
/// spec's value; nothing here is a re-implementation that tests could
/// disagree with silently.
///
/// ---------------------------------------------------------------------------
module GC.Spec.SweepPar.Exec

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header

module HeapGraph = GC.Spec.HeapGraph
module Alloc = GC.Spec.Allocator
module SpecCoalesce = GC.Spec.Coalesce
module CC = GC.Spec.Coalesce.Correct
module Defs = GC.Spec.SweepCoalesce.Defs

/// ---------------------------------------------------------------------------
/// Object primitives
/// ---------------------------------------------------------------------------

let is_black_x (x: obj_addr) (g: heap)
  : r:bool{r == is_black x g}
  = is_black_iff x g;
    color_of_object_spec x g;
    getColor (read_word g (hd_address x)) = Black

let wosize_x (x: obj_addr) (g: heap)
  : r:U64.t{r == wosize_of_object x g}
  = wosize_of_object_spec x g;
    getWosize (read_word g (hd_address x))

let makeWhite_x (x: obj_addr) (g: heap)
  : r:heap{r == makeWhite x g}
  = makeWhite_spec x g;
    write_word g (hd_address x) (colorHeader (read_word g (hd_address x)) White)

let set_field_x (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (v: U64.t)
  : Pure heap
         (requires U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= heap_size)
         (ensures fun r -> r == HeapGraph.set_field g obj i v)
  = let field_addr = U64.add (hd_address obj) (U64.mul mword i) in
    write_word g field_addr v

let rec zero_fields_x (g: heap) (addr: U64.t) (n: nat)
  : Tot (r:heap{r == Alloc.zero_fields g addr n}) (decreases n)
  = if n = 0 then g
    else if U64.v addr + 8 > heap_size then g
    else if U64.v addr >= heap_size then g
    else if U64.v addr % 8 <> 0 then g
    else
      let g' = write_word g (addr <: hp_addr) 0UL in
      if U64.v addr + 8 >= pow2 64 then g'
      else
        zero_fields_x g' (U64.uint_to_t (U64.v addr + 8)) (n - 1)

/// ---------------------------------------------------------------------------
/// flush_blue
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let flush_blue_x (g: heap) (first_blue: U64.t) (run_words: nat) (fp: U64.t)
  : r:(heap & U64.t){r == SpecCoalesce.flush_blue g first_blue run_words fp}
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
        let wz_u64 : wosize = U64.uint_to_t wz in
        let hdr = makeHeader wz_u64 Blue 0UL in
        let g1 = write_word g hd hdr in
        if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
          let g2 = set_field_x g1 fb 1UL fp in
          let zero_start_nat = U64.v fb + U64.v mword in
          if wz >= 2 && zero_start_nat < pow2 64 then
            let g3 = zero_fields_x g2 (U64.uint_to_t zero_start_nat) (wz - 1) in
            (g3, fb)
          else
            (g2, fb)
        end
        else
          (g1, fp)
      end
#pop-options

/// ---------------------------------------------------------------------------
/// objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec objects_x (start: hp_addr) (g: heap)
  : Tot (r:Seq.seq obj_addr{r == objects start g})
        (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then Seq.empty
    else
      let header = read_word g start in
      let wz = getWosize header in
      let obj_size_nat = U64.v wz + 1 in
      let next_start_nat = U64.v start + (obj_size_nat * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then Seq.empty
      else begin
        f_address_spec start;
        let obj_addr : obj_addr = f_address start in
        let next_start_raw = U64.uint_to_t next_start_nat in
        if next_start_nat >= heap_size then Seq.cons obj_addr Seq.empty
        else begin
          let next_start : hp_addr = next_start_raw in
          Seq.cons obj_addr (objects_x next_start g)
        end
      end
#pop-options

/// ---------------------------------------------------------------------------
/// fused sweep + coalesce
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec fused_aux_x (g0: heap) (g: heap) (objs: seq obj_addr)
    (fb: U64.t) (rw: nat) (fp: U64.t)
  : Tot (r:(heap & U64.t){r == Defs.fused_aux g0 g objs fb rw fp})
        (decreases Seq.length objs)
  = if Seq.length objs = 0 then
      flush_blue_x g fb rw fp
    else
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      if is_black_x obj g0 then
        let (g', fp') = flush_blue_x g fb rw fp in
        let g'' = makeWhite_x obj g' in
        fused_aux_x g0 g'' rest 0UL 0 fp'
      else
        let ws = U64.v (wosize_x obj g0) in
        let new_fb : U64.t = if rw = 0 then obj else fb in
        fused_aux_x g0 g rest new_fb (rw + ws + 1) fp
#pop-options

let fused_sweep_coalesce_x (g: heap)
  : r:(heap & U64.t){r == Defs.fused_sweep_coalesce g}
  = fused_aux_x g g (objects_x zero_addr g) 0UL 0 0UL

/// ---------------------------------------------------------------------------
/// walk_visits
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --ifuel 0"
let rec walk_visits_x (g: heap) (s a: hp_addr)
  : Tot (r:bool{r == CC.walk_visits g s a}) (decreases (heap_size - U64.v s)) =
  if U64.v s = U64.v a then true
  else if U64.v s + 8 >= heap_size then false
  else
    let wz = getWosize (read_word g s) in
    let next = U64.v s + (U64.v wz + 1) * 8 in
    if next > heap_size || next >= pow2 64 || next >= heap_size then false
    else begin
      aligned_plus_mul8 (U64.v s) (U64.v wz + 1);
      walk_visits_x g (mk_hp_addr next) a
    end
#pop-options
