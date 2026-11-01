/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Exec — executable twins of the sequential mark's ghost spec
///
/// `GC.Spec.Mark.mark` and everything it calls (`is_white`, `makeGray`,
/// `resolve_object`, `HeapGraph.get_field`, ...) are `GTot`, so extraction
/// erases them.  To run the spec, this module gives each one a `Tot` twin
/// built from the same `Tot` primitives (`read_word`, `write_word`,
/// `getColor`, ...), and the twin's return type states that it *is* the
/// ghost original.  The extracted twin therefore computes exactly the spec's
/// value; nothing here is a re-implementation that tests could disagree with
/// silently.
///
/// The parallel model, `GC.Spec.MarkPar`, is built from these twins too.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Exec

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark

/// ---------------------------------------------------------------------------
/// Object primitives
/// ---------------------------------------------------------------------------

let color_x (x: obj_addr) (g: heap)
  : r:color{r == color_of_object x g}
  = color_of_object_spec x g;
    getColor (read_word g (hd_address x))

let is_white_x (x: obj_addr) (g: heap)
  : r:bool{r == is_white x g}
  = is_white_iff x g;
    color_x x g = White

let is_gray_x (x: obj_addr) (g: heap)
  : r:bool{r == is_gray x g}
  = is_gray_iff x g;
    color_x x g = Gray

let is_black_x (x: obj_addr) (g: heap)
  : r:bool{r == is_black x g}
  = is_black_iff x g;
    color_x x g = Black

let is_blue_x (x: obj_addr) (g: heap)
  : r:bool{r == is_blue x g}
  = is_blue_iff x g;
    color_x x g = Blue

let wosize_x (x: obj_addr) (g: heap)
  : r:U64.t{r == wosize_of_object x g}
  = wosize_of_object_spec x g;
    getWosize (read_word g (hd_address x))

let is_no_scan_x (x: obj_addr) (g: heap)
  : r:bool{r == is_no_scan x g}
  = is_no_scan_spec x g;
    tag_of_object_spec x g;
    U64.gte (getTag (read_word g (hd_address x))) no_scan_tag

let is_infix_x (x: obj_addr) (g: heap)
  : r:bool{r == is_infix x g}
  = is_infix_spec x g;
    tag_of_object_spec x g;
    getTag (read_word g (hd_address x)) = infix_tag

let makeGray_x (x: obj_addr) (g: heap)
  : r:heap{r == makeGray x g}
  = makeGray_spec x g;
    write_word g (hd_address x) (colorHeader (read_word g (hd_address x)) Gray)

let makeBlack_x (x: obj_addr) (g: heap)
  : r:heap{r == makeBlack x g}
  = makeBlack_spec x g;
    write_word g (hd_address x) (colorHeader (read_word g (hd_address x)) Black)

let resolve_x (a: obj_addr) (g: heap)
  : r:obj_addr{r == resolve_object a g}
  = if is_infix_x a g then begin
      parent_closure_addr_nat_spec a g;
      let p = U64.v a - U64.v (wosize_x a g) * 8 in
      if p >= 8 && p < heap_size && p % 8 = 0 then begin
        resolve_infix_spec a g;
        U64.uint_to_t p
      end else begin
        resolve_infix_invalid_parent a g;
        a
      end
    end else begin
      resolve_non_infix a g;
      a
    end

let get_field_x (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1})
  : r:U64.t{r == HeapGraph.get_field g obj i}
  = let hd = hd_address obj in
    if U64.v hd + U64.v mword * U64.v i + U64.v mword <= heap_size then
      let field_addr = U64.add hd (U64.mul mword i) in
      read_word g field_addr
    else
      0UL

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
/// The sequential mark
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec push_children_x (g: heap) (st: seq obj_addr) (obj: obj_addr)
    (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Tot (r:(heap & seq obj_addr){r == Mark.push_children g st obj i ws})
        (decreases (U64.v ws - U64.v i))
  = if U64.v i > U64.v ws then (g, st)
    else
      let v = get_field_x g obj i in
      let (g', st') =
        if HeapGraph.is_pointer_field v then begin
          HeapGraph.is_pointer_field_is_obj_addr v;
          let child_raw : obj_addr = v in
          let child = resolve_x child_raw g in
          if is_white_x child g then
            (makeGray_x child g, Seq.cons child st)
          else
            (g, st)
        end else
          (g, st)
      in
      if U64.v i < U64.v ws then
        push_children_x g' st' obj (U64.add i 1UL) ws
      else
        (g', st')
#pop-options

let mark_step_x (g: heap) (st: seq obj_addr)
  : r:(heap & seq obj_addr){r == Mark.mark_step g st}
  = if Seq.length st = 0 then (g, st)
    else
      let obj = Seq.head st in
      let st' = Seq.tail st in
      let g' = makeBlack_x obj g in
      let ws = wosize_x obj g in
      if is_no_scan_x obj g then (g', st')
      else push_children_x g' st' obj 1UL ws

let rec mark_aux_x (g: heap) (st: seq obj_addr) (fuel: nat)
  : Tot (r:heap{r == Mark.mark_aux g st fuel}) (decreases fuel)
  = if Seq.length st = 0 then g
    else if fuel = 0 then g
    else
      let (g', st') = mark_step_x g st in
      mark_aux_x g' st' (fuel - 1)

let mark_x (g: heap) (st: seq obj_addr)
  : r:heap{r == Mark.mark g st}
  = mark_aux_x g st heap_words
