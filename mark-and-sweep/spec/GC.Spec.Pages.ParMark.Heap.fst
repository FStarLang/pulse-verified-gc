/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Heap - the parallel mark's view of a heap
/// ---------------------------------------------------------------------------
///
/// The model (`GC.Spec.Pages.ParMark.Model`) reads the heap through three
/// functions.  Here they are, as the P0 prototype's `visit` computes them
/// (`par_mark_pages.c`): for the word at `a`,
///   - `h_tst a`: if it holds a heap pointer `v`, the address `v - 8` whose
///     bit the bitmap-first test reads;
///   - `h_tgt a`: the object it points to, resolved through an infix header,
///     unless that object is free (blue);
/// and `h_nf y`, the fields pushed for a claimed object: its wosize, or 0
/// for a no-scan or free one.  They are total functions of header words
/// (`hdr`), and agree with the specification's `resolve_object`,
/// `wosize_of_object`, `is_blue` and `is_no_scan` on objects (`tres_eq`,
/// `hw_obj`).
///
/// The claimable objects (`hview`) are the heap's objects that are not free;
/// the root targets (`root_tgts`) the roots, resolved, the free ones
/// skipped, as the prototype's `setup_roots` does.
///
/// **`view_ok_heap`**: from the allocator's `Idle` invariant and the roots'
/// precondition (`par_pre`), the view meets `Reach.view_ok`.
/// **`reach_iff`**: the model's reachability is the heap graph's
/// (`reachable_set`), object for object.
///
/// `par_pre` asks of the roots that they be objects that are not free.  It
/// does not ask them to be grey, as `GcCorrect.mark_pre` does: in the `Idle`
/// state every live object is white (`MarkPhase.live_white`), so with
/// `mark_pre` only an empty root set is possible.  The parallel mark claims
/// its roots in the bitmap; it needs no grey header.

module GC.Spec.Pages.ParMark.Heap

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module L = FStar.List.Tot
module HG = GC.Spec.HeapGraph
module HM = GC.Spec.HeapModel
module G = GC.Spec.Graph
module DFS = GC.Spec.DFS
module R = GC.Spec.Pages.Replace
module PA = GC.Spec.Pages.Allocator
module I = GC.Spec.AllocIface
module MP = GC.Spec.Pages.MarkPhase
module GP = GC.Spec.Pages.GcPillars
module SA = GC.Spec.Pages.SweepAll
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Header words, as total functions
/// ---------------------------------------------------------------------------

/// The header word of the object at `y`.
let hw (h: heap) (y: nat) : U64.t = if y >= 8 then hdr h (y - 8) else 0UL

let tblue (h: heap) (y: nat) : bool = getColor (hw h y) = Blue
let tnoscan (h: heap) (y: nat) : bool = U64.gte (getTag (hw h y)) no_scan_tag
let twz (h: heap) (y: nat) : nat = U64.v (getWosize (hw h y))

/// `resolve_object`, from the header word.
let tres (h: heap) (v: nat) : nat =
  if getTag (hw h v) = infix_tag then begin
    let p : int = v - twz h v * 8 in
    if p >= 8 && p < heap_size && p % 8 = 0 then p else v
  end else v

/// The word at `a`, if `a` is a word of the heap.
let word_at (h: heap) (a: nat) : option U64.t =
  if a < heap_size && a % 8 = 0 then Some (read_word h (mk_hp_addr a)) else None

let h_tst (h: heap) (a: nat) : option nat =
  match word_at h a with
  | Some v -> if HG.is_pointer_field v then Some (U64.v v - 8) else None
  | None -> None

let h_tgt (h: heap) (a: nat) : option nat =
  match word_at h a with
  | Some v ->
    if HG.is_pointer_field v then begin
      let y = tres h (U64.v v) in
      if tblue h y then None else Some y
    end else None
  | None -> None

let h_nf (h: heap) (y: nat) : nat =
  if tnoscan h y || tblue h y then 0 else twz h y

let hparams (h: heap) (k pkt chunk maxlen: pos) (smin: nat) (tickp: pos) : params = {
  k = k; pkt = pkt; chunk = chunk; maxlen = maxlen; smin = smin; tickp = tickp;
  nf = h_nf h; tst = h_tst h; tgt = h_tgt h
}

/// `p` reads the heap `h`.
let hp_of (h: heap) (p: params) : prop = p.nf == h_nf h /\ p.tst == h_tst h /\ p.tgt == h_tgt h

let hparams_of (h: heap) (k pkt chunk maxlen: pos) (smin: nat) (tickp: pos)
  : Lemma (hp_of h (hparams h k pkt chunk maxlen smin tickp))
  = ()

/// On an object, the header views are the specification's.
let hw_obj (h: heap) (x: obj_addr)
  : Lemma (hw h (U64.v x) == read_word h (hd_address x) /\
           (tblue h (U64.v x) <==> is_blue x h) /\
           (tnoscan h (U64.v x) <==> is_no_scan x h) /\
           twz h (U64.v x) == U64.v (wosize_of_object x h) /\
           (getTag (hw h (U64.v x)) = infix_tag <==> is_infix x h))
  = R.hdr_obj h x;
    is_blue_iff x h;
    is_no_scan_spec x h;
    is_infix_spec x h;
    wosize_of_object_spec x h;
    color_of_object_spec x h

let tres_eq (h: heap) (x: obj_addr)
  : Lemma (tres h (U64.v x) == U64.v (resolve_object x h))
  = hw_obj h x;
    parent_closure_addr_nat_spec x h;
    if is_infix x h then begin
      let p = parent_closure_addr_nat x h in
      if p >= 8 && p < heap_size && p % 8 = 0 then resolve_infix_spec x h
      else resolve_infix_invalid_parent x h
    end
    else resolve_non_infix x h

/// ---------------------------------------------------------------------------
/// The view
/// ---------------------------------------------------------------------------

/// `y` is an object of `h`.
let is_obj (h: heap) (y: nat) : prop =
  y >= 8 /\ y < heap_size /\ y % 8 == 0 /\
  (y < heap_size ==> Seq.mem (U64.uint_to_t y) (objects zero_addr h))

/// The claimable objects: objects that are not free, with their header's
/// bit in the bitmap.
let hok (h: heap) (y: nat) : prop =
  is_obj h y /\ not (tblue h y) /\ in_pages (y - 8)

let u64v (x: hp_addr) : nat = U64.v x

let obj_list (h: heap) : GTot (list nat) = L.map u64v (Seq.seq_to_list (objects zero_addr h))

let hview (h: heap) : GTot view = { ok = hok h; univ = obj_list h; maxnf = pow2 54 }

/// The root targets: each root resolved, skipped if free.
let rec rt_list (h: heap) (rs: list obj_addr) : list nat =
  match rs with
  | [] -> []
  | r :: rest ->
    let y = tres h (U64.v r) in
    if tblue h y then rt_list h rest else y :: rt_list h rest

let root_tgts (h: heap) (roots: Seq.seq obj_addr) : list nat = rt_list h (Seq.seq_to_list roots)

/// What the parallel mark needs of the heap and its roots.
let par_pre (h: heap) (st: pstate) (roots: Seq.seq obj_addr) : prop =
  PA.inv I.Idle h st /\
  (forall (r: obj_addr). Seq.mem r roots ==> Seq.mem r (objects zero_addr h) /\ ~(is_blue r h)) /\
  GP.graph_pre h roots

/// ---------------------------------------------------------------------------
/// Facts of the Idle state
/// ---------------------------------------------------------------------------

let idle_facts (h: heap) (st: pstate)
  : Lemma (requires PA.inv I.Idle h st)
          (ensures well_formed_heap h /\ pages_ok h st /\ MP.all_swept st /\ shape_ok h st.pm /\
                   map_ok st.pm /\ Mark.no_pointer_to_blue h)
  = GC.Spec.Pages.Step.pages_ok_elim h st

/// A live object's header lies in the pages.
let obj_in_pages (h: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires PA.inv I.Idle h st /\ Seq.mem x (objects zero_addr h) /\ ~(is_blue x h))
          (ensures in_pages (U64.v x - 8))
  = idle_facts h st;
    let b = U64.v x - 8 in
    R.obj_iff h x;
    R.hdr_obj h x;
    is_blue_iff x h;
    SA.not_tail h st.pm b;
    steps_to_le h (U64.v zero_addr) b;
    hd_address_spec x

/// An object, by its address.
let as_obj (h: heap) (y: nat{is_obj h y}) : (x: obj_addr{U64.v x == y /\ Seq.mem x (objects zero_addr h)}) =
  U64.uint_to_t y

/// The fields the model scans of a claimable object are its fields.
#push-options "--z3rlimit 40"
let field_facts (h: heap) (st: pstate) (p: params) (x a: nat)
  : Lemma (requires PA.inv I.Idle h st /\ is_obj h x /\
                    hp_of h p /\ field_of p x a)
          (ensures (let xo = as_obj h x in
                    let j = (a - x) / 8 + 1 in
                    a < heap_size /\ a % 8 == 0 /\ ~(is_no_scan xo h) /\ ~(is_blue xo h) /\
                    1 <= j /\ j <= U64.v (wosize_of_object xo h) /\
                    HG.get_field h xo (U64.uint_to_t j) == read_word h (mk_hp_addr a) /\
                    HG.object_fits_in_heap xo h))
  = idle_facts h st;
    let xo = as_obj h x in
    hw_obj h xo;
    wf_object_bound h xo;
    Mark.wf_implies_object_fits h xo;
    hd_address_spec xo;
    let j = (a - x) / 8 + 1 in
    FStar.Math.Lemmas.lemma_div_mod (a - x) 8;
    assert (a == x + 8 * (j - 1));
    div_lt (a - x) 8 (U64.v (wosize_of_object xo h));
    assert (U64.v (hd_address xo) + 8 * j == a);
    FStar.Math.Lemmas.lemma_mod_plus x (j - 1) 8
#pop-options

/// A pointer word, as an object address.
let ptr_obj (v: U64.t{HG.is_pointer_field v}) : obj_addr = v

/// The target of a scanned field is a graph successor, and claimable.
#push-options "--z3rlimit 40"
let tgt_facts (h: heap) (st: pstate) (roots: Seq.seq obj_addr)
  (p: params) (x a y: nat)
  : Lemma (requires par_pre h st roots /\ is_obj h x /\
                    hp_of h p /\ field_of p x a /\
                    h_tgt h a == Some y)
          (ensures (let v = read_word h (mk_hp_addr a) in
                    HG.is_pointer_field v /\
                    y == U64.v (resolve_object (ptr_obj v) h) /\
                    G.mem_graph_edge (HM.create_graph h) (as_obj h x) (resolve_object (ptr_obj v) h) /\
                    hok h y))
  = idle_facts h st;
    field_facts h st p x a;
    let xo = as_obj h x in
    let j = (a - x) / 8 + 1 in
    let v = read_word h (mk_hp_addr a) in
    let vo = ptr_obj v in
    tres_eq h vo;
    HM.objects_is_vertex_set h;
    HG.pointer_field_is_graph_edge h (objects zero_addr h) xo (U64.uint_to_t j);
    let rv = resolve_object vo h in
    assert (G.mem_graph_edge (HM.create_graph h) xo rv);
    assert (Seq.mem (xo, rv) (HM.create_graph h).edges);
    HM.graph_vertices_mem h rv;
    hw_obj h rv;
    obj_in_pages h st rv
#pop-options

/// ---------------------------------------------------------------------------
/// The view is a view
/// ---------------------------------------------------------------------------

let seq_list_mem (#a: eqtype) (s: Seq.seq a) (x: a)
  : Lemma (Seq.mem x s <==> L.mem x (Seq.seq_to_list s))
  = SP.lemma_seq_list_bij s;
    SP.mem_seq_of_list x (Seq.seq_to_list s)

let univ_mem (h: heap) (y: nat)
  : Lemma (requires is_obj h y) (ensures L.mem y (obj_list h))
  = let yo = as_obj h y in
    seq_list_mem (objects zero_addr h) yo;
    L.mem_memP yo (Seq.seq_to_list (objects zero_addr h));
    L.memP_map_intro u64v yo (Seq.seq_to_list (objects zero_addr h));
    L.mem_memP y (obj_list h)

#push-options "--fuel 1"
let rec rt_mem (h: heap) (rs: list obj_addr) (y: nat)
  : Lemma (requires L.mem y (rt_list h rs))
          (ensures exists (r: obj_addr). L.mem r rs /\ y == tres h (U64.v r) /\ not (tblue h y))
          (decreases rs)
  = match rs with
    | r :: rest -> if tblue h (tres h (U64.v r)) || y <> tres h (U64.v r) then rt_mem h rest y

let rec rt_mem_intro (h: heap) (rs: list obj_addr) (r: obj_addr)
  : Lemma (requires L.mem r rs /\ not (tblue h (tres h (U64.v r))))
          (ensures L.mem (tres h (U64.v r)) (rt_list h rs))
          (decreases rs)
  = match rs with
    | r' :: rest -> if r' <> r then rt_mem_intro h rest r
#pop-options

/// A root target is a root.
let root_tgt_root (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (y: nat)
  : Lemma (requires par_pre h st roots /\ L.mem y (root_tgts h roots))
          (ensures exists (r: obj_addr). Seq.mem r roots /\ U64.v r == y /\ hok h y)
  = idle_facts h st;
    rt_mem h (Seq.seq_to_list roots) y;
    eliminate exists (r: obj_addr). L.mem r (Seq.seq_to_list roots) /\ y == tres h (U64.v r) /\ not (tblue h y)
    with begin
      seq_list_mem roots r;
      tres_eq h r;
      wf_resolve_identity h r;
      obj_in_pages h st r
    end

/// A root is a root target.
let root_root_tgt (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (r: obj_addr)
  : Lemma (requires par_pre h st roots /\ Seq.mem r roots)
          (ensures L.mem (U64.v r) (root_tgts h roots))
  = idle_facts h st;
    seq_list_mem roots r;
    tres_eq h r;
    wf_resolve_identity h r;
    hw_obj h r;
    rt_mem_intro h (Seq.seq_to_list roots) r

#push-options "--z3rlimit 40"
let view_ok_heap (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params)
  : Lemma (requires par_pre h st roots /\ hp_of h p)
          (ensures view_ok p (hview h) (root_tgts h roots))
  = let v = hview h in
    idle_facts h st;
    let v1 (y: nat) : Lemma (v.ok y ==> y >= 8 /\ in_pages (y - 8) /\ p.nf y <= v.maxnf /\ L.mem y v.univ)
      = if FStar.IndefiniteDescription.strong_excluded_middle (v.ok y) then begin
          univ_mem h y;
          getWosize_bound (hw h y)
        end
    in
    let v2 (x a y: nat) : Lemma (v.ok x /\ field_of p x a /\ p.tgt a == Some y ==> v.ok y)
      = if FStar.IndefiniteDescription.strong_excluded_middle (v.ok x /\ field_of p x a /\ p.tgt a == Some y)
        then tgt_facts h st roots p x a y
    in
    let v3 (x a y: nat)
      : Lemma (v.ok x /\ field_of p x a /\ v.ok y /\ p.tst a == Some (y - 8) ==> p.tgt a == Some y)
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (v.ok x /\ field_of p x a /\ v.ok y /\ p.tst a == Some (y - 8)) then begin
          let yo = as_obj h y in
          field_facts h st p x a;
          let w = read_word h (mk_hp_addr a) in
          assert (HG.is_pointer_field w /\ U64.v w - 8 == y - 8);
          assert (w == yo);
          tres_eq h yo;
          wf_resolve_identity h yo
        end
    in
    let v5 (y: nat) : Lemma (L.mem y (root_tgts h roots) ==> v.ok y)
      = if L.mem y (root_tgts h roots) then root_tgt_root h st roots y
    in
    FStar.Classical.forall_intro v1;
    FStar.Classical.forall_intro_3 v2;
    FStar.Classical.forall_intro_3 v3;
    FStar.Classical.forall_intro v5
#pop-options

/// ---------------------------------------------------------------------------
/// The model's reachability is the graph's
/// ---------------------------------------------------------------------------

/// The graph's reachable set (empty if the graph facts fail).
let rset (h: heap) (roots: Seq.seq obj_addr) : GTot G.vertex_list =
  if FStar.IndefiniteDescription.strong_excluded_middle (GP.graph_pre h roots)
  then DFS.reachable_set (HM.create_graph h) (HG.coerce_to_vertex_list roots)
  else Seq.empty

/// A pointer field of an object, from a member of its pointer fields.
#push-options "--fuel 1 --z3rlimit 40"
let rec gpf_aux_mem (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t) (y: G.vertex_id)
  : Lemma (requires Seq.mem y (HG.get_pointer_fields_aux g obj i ws))
          (ensures exists (j: nat). U64.v i <= j /\ j <= U64.v ws /\
                     HG.is_pointer_field (HG.get_field g obj (U64.uint_to_t j)) /\
                     y == HG.resolve_field g (HG.get_field g obj (U64.uint_to_t j)))
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else begin
      let v = HG.get_field g obj i in
      let rest =
        if U64.v i < U64.v ws then HG.get_pointer_fields_aux g obj (U64.add i 1UL) ws
        else Seq.empty in
      assert (HG.get_pointer_fields_aux g obj i ws ==
              (if HG.is_pointer_field v then Seq.cons (HG.resolve_field g v) rest else rest));
      if HG.is_pointer_field v then Seq.mem_cons (HG.resolve_field g v) rest;
      if HG.is_pointer_field v && y = HG.resolve_field g v then
        assert (U64.uint_to_t (U64.v i) == i)
      else if U64.v i < U64.v ws then gpf_aux_mem g obj (U64.add i 1UL) ws y
    end
#pop-options

/// A graph edge is a pointer field of a scannable object.
#push-options "--z3rlimit 40"
let edge_field (h: heap) (x: obj_addr) (z: G.vertex_id)
  : Lemma (requires Seq.mem x (objects zero_addr h) /\ G.mem_graph_edge (HM.create_graph h) x z)
          (ensures HG.object_fits_in_heap x h /\ ~(is_no_scan x h) /\ ~(is_blue x h) /\
                   (exists (j: nat). 1 <= j /\ j <= U64.v (wosize_of_object x h) /\
                     HG.is_pointer_field (HG.get_field h x (U64.uint_to_t j)) /\
                     z == HG.resolve_field h (HG.get_field h x (U64.uint_to_t j))))
  = G.edge_mem_successors (HM.create_graph h) x z;
    HM.objects_is_vertex_set h;
    HG.successors_eq_pointer_fields h (objects zero_addr h) x;
    assert (Seq.mem z (HG.get_pointer_fields h x));
    if not (HG.object_fits_in_heap x h) || is_no_scan x h || is_blue x h then begin
      assert (HG.get_pointer_fields h x == Seq.empty);
      SP.mem_index z (HG.get_pointer_fields h x)
    end else begin
      assert (HG.get_pointer_fields h x == HG.get_pointer_fields_aux h x 1UL (wosize_of_object x h));
      gpf_aux_mem h x 1UL (wosize_of_object x h) z
    end
#pop-options

let graph_facts (h: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires par_pre h st roots)
          (ensures G.graph_wf (HM.create_graph h) /\
                   G.is_vertex_set (HG.coerce_to_vertex_list roots) /\
                   G.subset_vertices (HG.coerce_to_vertex_list roots) (HM.create_graph h).vertices /\
                   rset h roots == DFS.reachable_set (HM.create_graph h) (HG.coerce_to_vertex_list roots))
  = ()

/// Model to graph.
#push-options "--z3rlimit 40"
let gen_to_graph (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (y: nat)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ reach p (root_tgts h roots) y)
          (ensures is_obj h y /\ Seq.mem (as_obj h y) (rset h roots))
  = let gr = HM.create_graph h in
    let rs = HG.coerce_to_vertex_list roots in
    graph_facts h st roots;
    view_ok_heap h st roots p;
    let m (z: nat) : prop = is_obj h z /\ (is_obj h z ==> Seq.mem (as_obj h z) (rset h roots)) in
    let roots_in (z: nat) : Lemma (L.mem z (root_tgts h roots) ==> m z)
      = if L.mem z (root_tgts h roots) then begin
          root_tgt_root h st roots z;
          eliminate exists (r: obj_addr). Seq.mem r roots /\ U64.v r == z /\ hok h z
          with begin
            HG.coerce_mem_lemma roots r;
            HM.graph_vertices_mem h r;
            G.reach_refl gr r;
            DFS.reachable_set_correct gr rs
          end
        end
    in
    let closed (x a z: nat) : Lemma (m x /\ field_of p x a /\ p.tgt a == Some z ==> m z)
      = if FStar.IndefiniteDescription.strong_excluded_middle (m x /\ field_of p x a /\ p.tgt a == Some z)
        then begin
          tgt_facts h st roots p x a z;
          let xo = as_obj h x in
          let v = read_word h (mk_hp_addr a) in
          let rv = resolve_object (ptr_obj v) h in
          assert (Seq.mem (xo, rv) gr.edges);
          HM.graph_vertices_mem h xo;
          HM.graph_vertices_mem h rv;
          DFS.reachable_successor_closed gr rs xo rv
        end
    in
    FStar.Classical.forall_intro roots_in;
    FStar.Classical.forall_intro_3 closed;
    closed_reach p (root_tgts h roots) m y
#pop-options

/// One graph edge from a model-reachable object is a model edge.
#push-options "--z3rlimit 40"
let edge_gen (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (y: obj_addr) (z: G.vertex_id)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.mem y (objects zero_addr h) /\
                    G.mem_graph_edge (HM.create_graph h) y z /\ reach p (root_tgts h roots) (U64.v y))
          (ensures reach p (root_tgts h roots) (U64.v z))
  = idle_facts h st;
    edge_field h y z;
    hw_obj h y;
    wf_object_bound h y;
    hd_address_spec y;
    eliminate exists (j: nat). 1 <= j /\ j <= U64.v (wosize_of_object y h) /\
                     HG.is_pointer_field (HG.get_field h y (U64.uint_to_t j)) /\
                     z == HG.resolve_field h (HG.get_field h y (U64.uint_to_t j))
    with begin
      let jj = U64.uint_to_t j in
      let v = HG.get_field h y jj in
      let vo = ptr_obj v in
      getWosize_bound (read_word h (hd_address y));
      wosize_of_object_spec y h;
      HG.get_field_addr_eq h y jj;
      let far = U64.add_mod y (U64.mul_mod (U64.sub jj 1UL) mword) in
      let a = U64.v far in
      assert (word_at h a == Some v);
      assert (field_of p (U64.v y) a);
      tres_eq h vo;
      wosize_of_object_bound y h;
      FStar.Math.Lemmas.pow2_lt_compat 61 54;
      field_read_implies_exists_pointing h y (wosize_of_object y h) (U64.sub jj 1UL) vo;
      assert (points_to h y vo);
      hw_obj h (resolve_object vo h);
      assert (h_tgt h a == Some (U64.v z));
      reach_step p (root_tgts h roots) (U64.v y) a (U64.v z)
    end
#pop-options

let rec greach_gen (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params)
  (r: G.vertex_id{G.mem_graph_vertex (HM.create_graph h) r})
  (x: G.vertex_id{G.mem_graph_vertex (HM.create_graph h) x})
  (w: G.reach (HM.create_graph h) r x)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.mem r (HG.coerce_to_vertex_list roots))
          (ensures reach p (root_tgts h roots) (U64.v x))
          (decreases w)
  = match w with
    | G.ReachRefl _ ->
      Mark.vertex_is_obj_addr h r;
      let ro : obj_addr = r in
      HG.coerce_mem_lemma roots ro;
      root_root_tgt h st roots ro;
      reach_root p (root_tgts h roots) (U64.v r)
    | G.ReachTrans _ y z w' ->
      greach_gen h st roots p r y w';
      Mark.vertex_is_obj_addr h y;
      let yo : obj_addr = y in
      HM.graph_vertices_mem h yo;
      edge_gen h st roots p yo z

/// Graph to model.
let graph_to_gen (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (y: nat)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ is_obj h y /\ Seq.mem (as_obj h y) (rset h roots))
          (ensures reach p (root_tgts h roots) y)
  = let gr = HM.create_graph h in
    let rs = HG.coerce_to_vertex_list roots in
    graph_facts h st roots;
    DFS.reachable_set_correct gr rs;
    let x = as_obj h y in
    HM.graph_vertices_mem h x;
    eliminate exists (r: G.vertex_id{G.mem_graph_vertex gr r}). Seq.mem r rs /\ G.reachable gr r x
    with eliminate exists (w: G.reach gr r x). True
         with greach_gen h st roots p r x w

/// **The model's reachability is the graph's.**
let reach_iff (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (y: nat)
  : Lemma (requires par_pre h st roots /\ hp_of h p)
          (ensures reach p (root_tgts h roots) y <==> (is_obj h y /\ Seq.mem (as_obj h y) (rset h roots)))
  = FStar.Classical.move_requires (gen_to_graph h st roots p) y;
    FStar.Classical.move_requires (graph_to_gen h st roots p) y

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
/// The hypotheses of `view_ok_heap` and `reach_iff` are not refutable (a
/// witness, with no roots, is `GC.Impl.Pages.ParMarkCorrect.par_witness`).
[@@expect_failure [19]]
let par_pre_not_false (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params)
  : Lemma (requires par_pre h st roots /\ hp_of h p) (ensures False)
  = ()

/// Nor with a root.
[@@expect_failure [19]]
let par_pre_root_not_false (h: heap) (st: pstate) (roots: Seq.seq obj_addr) (p: params) (r: obj_addr)
  : Lemma (requires par_pre h st roots /\ hp_of h p /\ Seq.mem r roots) (ensures False)
  = ()
#pop-options
