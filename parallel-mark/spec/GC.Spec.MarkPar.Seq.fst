/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Seq — the sequential mark's heap, characterized
///
/// `sequential_mark g roots` greys the root objects and runs
/// `GC.Spec.Mark.mark` from them.  This module shows its heap has the shape
/// `marked_as g h (reachable g roots)`, the same shape `GC.Spec.MarkPar.End`
/// gives the parallel run, so the two heaps are equal.
///
///   * Greying the roots, and every step of `mark`, recolour one enumerated
///     non-blue object to a non-blue colour, so the result is g recoloured
///     (`mark_aux_recoloured`).
///   * The sequential mark's own theorems, `mark_reachable_is_black` and
///     `mark_black_is_reachable`, give: black exactly when reachable.
///   * `mark_no_grey_remains` leaves no grey object, so every other object
///     keeps g's colour.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Seq

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Lib.Header
open GC.Spec.MarkPar.Model
open GC.Spec.MarkPar.Recolour

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module F = GC.Spec.MarkPar.Field
module R = GC.Spec.MarkPar.Roots

let objs (g: heap) = objects zero_addr g

let colors (x: obj_addr) (h: heap)
  : Lemma ((is_white x h ==> ~(is_gray x h) /\ ~(is_black x h) /\ ~(is_blue x h)) /\
           (is_gray x h ==> ~(is_black x h) /\ ~(is_blue x h)) /\
           (is_black x h ==> ~(is_blue x h)) /\
           (is_white x h \/ is_gray x h \/ is_black x h \/ is_blue x h))
  = is_white_iff x h; is_gray_iff x h; is_black_iff x h; is_blue_iff x h

/// ---------------------------------------------------------------------------
/// Greying the roots
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec grey_all_facts (g h: heap) (rs: list obj_addr)
  : Lemma (requires recoloured g h /\
                    (forall (r: obj_addr). L.memP r rs ==> Seq.mem r (objs g) /\ ~(is_blue r g)))
          (ensures recoloured g (grey_all h rs) /\
                   (forall (x: obj_addr). L.memP x rs ==> is_gray x (grey_all h rs)) /\
                   (forall (x: obj_addr). ~(L.memP x rs) ==>
                      color_of_object x (grey_all h rs) == color_of_object x h))
          (decreases rs)
  = match rs with
    | [] -> ()
    | r :: rest ->
      let h' = makeGray r h in
      makeGray_eq r h;
      recoloured_makeGray g h r;
      makeGray_is_gray r h;
      FStar.Classical.forall_intro (fun x ->
        FStar.Classical.move_requires (color_change_preserves_other_color r x h) Gray);
      grey_all_facts g h' rest;
      if L.mem r rest then L.mem_memP r rest
      else begin
        L.mem_memP r rest;
        is_gray_iff r h';
        is_gray_iff r (grey_all h' rest)
      end
#pop-options

/// ---------------------------------------------------------------------------
/// The stack
/// ---------------------------------------------------------------------------

let rec elements_valid (h: heap) (st: seq obj_addr)
  : Lemma (requires forall (x: obj_addr). Seq.mem x st ==> Seq.mem x (objects zero_addr h))
          (ensures Mark.stack_elements_valid h st)
          (decreases Seq.length st)
  = if Seq.length st = 0 then ()
    else begin
      Seq.cons_head_tail st;
      Seq.mem_cons (Seq.head st) (Seq.tail st);
      elements_valid h (Seq.tail st)
    end

let rec no_dups (l: list obj_addr)
  : Lemma (requires L.noRepeats l)
          (ensures Mark.stack_no_dups (Seq.seq_of_list l))
          (decreases l)
  = SP.lemma_seq_of_list_induction l;
    match l with
    | [] -> ()
    | h :: t ->
      no_dups t;
      L.mem_memP h t;
      R.mem_seq_of_list t h

/// The starting heap and stack of the sequential mark.
let start_heap (g: heap) (roots: list obj_addr) : GTot heap = grey_all g (root_objs g roots)
let start_stack (g: heap) (roots: list obj_addr) : GTot (seq obj_addr) = Seq.seq_of_list (root_objs g roots)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let start_facts (g: heap) (roots: list obj_addr)
  : Lemma (requires mark_pre g roots)
          (ensures (let h = start_heap g roots in
                    let st = start_stack g roots in
                    recoloured g h /\ well_formed_heap h /\
                    Mark.stack_props h st /\ Mark.root_props h st /\
                    Mark.no_black_objects h /\ Mark.no_pointer_to_blue h /\
                    create_graph h == create_graph g /\
                    (forall (x: obj_addr). Seq.mem x (objs g) /\ ~(L.memP x (root_objs g roots)) ==>
                       color_of_object x h == color_of_object x g)))
  = let rs = root_objs g roots in
    let h = start_heap g roots in
    let st = start_stack g roots in
    recoloured_refl g;
    let rr (r: obj_addr) : Lemma (requires L.memP r rs) (ensures Seq.mem r (objs g) /\ ~(is_blue r g)) =
      R.root_obj_facts g roots r; colors r g in
    FStar.Classical.forall_intro (FStar.Classical.move_requires rr);
    grey_all_facts g g rs;
    R.dedup_norepeats (resolve_all g roots);
    no_dups rs;
    FStar.Classical.forall_intro (R.mem_seq_of_list rs);
    elements_valid h st;
    let gr (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr h) /\ is_gray x h) (ensures Seq.mem x st)
      = if L.memP x rs then ()
        else begin colors x g; is_gray_iff x h; is_gray_iff x g end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires gr);
    let nb (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr h)) (ensures ~(is_black x h))
      = if L.memP x rs then colors x h
        else begin colors x g; is_black_iff x h; is_black_iff x g end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires nb)
#pop-options

/// ---------------------------------------------------------------------------
/// mark only recolours
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec push_children_recoloured (g h: heap) (st: seq obj_addr) (obj: obj_addr)
    (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires recoloured g h /\ Seq.mem obj (objs g) /\ ~(is_no_scan obj g) /\
                    is_black obj h /\ U64.v ws <= U64.v (wosize_of_object obj g))
          (ensures recoloured g (fst (Mark.push_children h st obj i ws)))
          (decreases (U64.v ws - U64.v i))
  = if U64.v i > U64.v ws then ()
    else begin
      recoloured_wosize g h obj;
      recoloured_no_scan g h obj;
      colors obj h;
      let v = HeapGraph.get_field h obj i in
      let h' =
        if HeapGraph.is_pointer_field v then begin
          HeapGraph.is_pointer_field_is_obj_addr v;
          let child = resolve_object v h in
          F.field_child_facts h obj i;
          if is_white child h then begin
            makeGray_eq child h;
            colors child h;
            recoloured_makeGray g h child;
            color_change_preserves_other_color child obj h Gray;
            is_black_iff obj h; is_black_iff obj (makeGray child h);
            makeGray child h
          end else h
        end else h in
      if U64.v i < U64.v ws then begin
        let (g', st') =
          if HeapGraph.is_pointer_field v then begin
            HeapGraph.is_pointer_field_is_obj_addr v;
            let child = resolve_object v h in
            if is_white child h then (makeGray child h, Seq.cons child st) else (h, st)
          end else (h, st) in
        push_children_recoloured g g' st' obj (U64.add i 1UL) ws
      end
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let mark_step_recoloured (g h: heap) (st: seq obj_addr{Seq.length st > 0})
  : Lemma (requires recoloured g h /\ Mark.stack_props h st)
          (ensures recoloured g (fst (Mark.mark_step h st)))
  = let obj = Seq.head st in
    Seq.cons_head_tail st;
    Seq.mem_cons obj (Seq.tail st);
    assert (Seq.mem obj (objects zero_addr h));
    assert (is_gray obj h);
    colors obj h;
    makeBlack_eq obj h;
    recoloured_makeBlack g h obj;
    makeBlack_is_black obj h;
    recoloured_wosize g h obj;
    recoloured_no_scan g h obj;
    if is_no_scan obj h then ()
    else push_children_recoloured g (makeBlack obj h) (Seq.tail st) obj 1UL (wosize_of_object obj h)
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec mark_aux_recoloured (g h: heap) (st: seq obj_addr) (fuel: nat)
  : Lemma (requires recoloured g h /\ Mark.stack_props h st)
          (ensures recoloured g (Mark.mark_aux h st fuel))
          (decreases fuel)
  = if Seq.length st = 0 then ()
    else if fuel = 0 then ()
    else begin
      mark_step_recoloured g h st;
      Mark.mark_step_preserves_stack_props h st;
      let p = Mark.mark_step h st in
      mark_aux_recoloured g (fst p) (snd p) (fuel - 1)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The sequential mark's heap
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let sequential_marked (g: heap) (roots: list obj_addr)
  : Lemma (requires mark_pre g roots)
          (ensures marked_as g (sequential_mark g roots) (reachable g roots))
  = let rs = root_objs g roots in
    let h = start_heap g roots in
    let st = start_stack g roots in
    let hs = sequential_mark g roots in
    assert (hs == Mark.mark h st);
    start_facts g roots;
    R.graph_pre_holds g roots;
    mark_aux_recoloured g h st heap_words;
    Mark.mark_no_grey_remains h st;
    Mark.mark_reachable_is_black h st st;
    Mark.mark_black_is_reachable h st st;
    let col (x: obj_addr)
      : Lemma (requires Seq.mem x (objs g))
              (ensures (reachable g roots x ==> is_black x hs) /\
                       (~(reachable g roots x) ==> color_of_object x hs == color_of_object x g))
      = graph_vertices_mem g x;
        colors x g; colors x hs;
        recoloured_blue g hs x;
        is_white_iff x g; is_blue_iff x g; is_white_iff x hs; is_blue_iff x hs;
        is_gray_iff x g; is_black_iff x g
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires col);
    recoloured_marked_as g hs (reachable g roots)
#pop-options
