/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.HeapGraph - Bridge between concrete heap and abstract graph
/// ---------------------------------------------------------------------------
///
/// This module provides:
/// - Field access (get_field, set_field)
/// - Pointer field extraction (get_pointer_fields)
/// - Graph construction from heap (create_graph_from_heap)
///
/// Parameterized by object list (callers provide their own `objects` enumeration).

module Pulse.Spec.GC.HeapGraph

open FStar.Seq
open FStar.Seq.Properties
open FStar.Mul

module U64 = FStar.UInt64

open Pulse.Spec.GC.Base
open Pulse.Spec.GC.Heap
open Pulse.Spec.GC.Object
open Pulse.Spec.GC.Graph

/// ---------------------------------------------------------------------------
/// Field Access
/// ---------------------------------------------------------------------------

/// Get i-th field of object (1-indexed; fields start at obj_addr)
/// Field i is at hd_address(obj) + mword * i = obj + mword * (i-1)
let get_field (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) : GTot U64.t =
  let hd = hd_address obj in
  if U64.v hd + U64.v mword * U64.v i + U64.v mword <= heap_size then
    let field_addr = U64.add hd (U64.mul mword i) in
    read_word g field_addr
  else
    0UL

/// Set i-th field of object
let set_field (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (v: U64.t)
  : Ghost heap
         (requires U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= heap_size)
         (ensures fun _ -> True)
  =
  let field_addr = U64.add (hd_address obj) (U64.mul mword i) in
  write_word g field_addr v

/// ---------------------------------------------------------------------------
/// Pointer Fields (for graph construction)
/// ---------------------------------------------------------------------------

/// Check if field value looks like a valid heap pointer
let is_pointer_field (v: U64.t) : bool =
  U64.v v % U64.v mword = 0 &&
  U64.v v > 0 &&
  U64.v v < heap_size

/// is_pointer_field implies obj_addr refinement (needed for hd_address)
let is_pointer_field_is_obj_addr (v: U64.t)
  : Lemma (requires is_pointer_field v)
          (ensures U64.v v >= U64.v mword)
  = ()

/// get_field reads from the same address as add_mod(obj, mul_mod(i-1, mword))
/// when the object is well-formed (field fits in heap)
let get_field_addr_eq (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma (requires U64.v (hd_address obj) + U64.v mword * U64.v i + U64.v mword <= heap_size /\
                    U64.v i < pow2 54)
          (ensures (let k = U64.sub i 1UL in
                    let far = U64.add_mod obj (U64.mul_mod k mword) in
                    U64.v far = U64.v obj + U64.v k * U64.v mword /\
                    U64.v far < heap_size /\
                    U64.v far % U64.v mword = 0 /\
                    get_field g obj i == read_word g (far <: hp_addr)))
  = let k = U64.sub i 1UL in
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    hd_address_spec obj;
    assert (U64.v (hd_address obj) = U64.v obj - U64.v mword);
    // mul_mod k mword: k < pow2 54 < pow2 61, so k * 8 < pow2 64
    assert (U64.v k * U64.v mword < pow2 64);
    FStar.Math.Lemmas.modulo_lemma (U64.v k * U64.v mword) (pow2 64);
    assert (U64.v (U64.mul_mod k mword) = U64.v k * U64.v mword);
    // add_mod obj (k*8): obj + k*8 < heap_size < pow2 64
    assert (U64.v obj + U64.v k * U64.v mword < heap_size);
    FStar.Math.Lemmas.modulo_lemma (U64.v obj + U64.v k * U64.v mword) (pow2 64);
    let far = U64.add_mod obj (U64.mul_mod k mword) in
    assert (U64.v far = U64.v obj + U64.v k * U64.v mword);
    // far = obj + (i-1)*8 and get_field reads from (obj-8) + 8*i = obj + 8*(i-1)
    assert (U64.v far = U64.v (hd_address obj) + U64.v mword * U64.v i);
    // So far = field_addr used by get_field
    let field_addr = U64.add (hd_address obj) (U64.mul mword i) in
    assert (U64.v far = U64.v field_addr);
    // Alignment
    FStar.Math.Lemmas.lemma_mod_plus_distr_l (U64.v obj) (U64.v k * U64.v mword) (U64.v mword);
    ()

/// Object fits in heap: header + fields all within bounds
let object_fits_in_heap (h_addr: obj_addr) (g: heap) : GTot bool =
  U64.v (hd_address h_addr) + U64.v mword + U64.v (wosize_of_object h_addr g) * U64.v mword <= heap_size

/// Intro lemma for object_fits_in_heap (use from outside the module)
let object_fits_in_heap_intro (h: obj_addr) (g: heap) : Lemma
  (requires U64.v (hd_address h) + 8 + Prims.op_Multiply (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  (ensures object_fits_in_heap h g) 
  = assert_norm (U64.v mword == 8)

/// Intro lemma without hd_address: v h + wosize*8 <= Seq.length g suffices
/// (Since hd_address h = h - 8, we have hd_address h + 8 = h)
let object_fits_from_bound (h: obj_addr) (g: heap) : Lemma
  (requires U64.v h + Prims.op_Multiply (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  (ensures object_fits_in_heap h g)
  = hd_address_spec h;
    assert_norm (U64.v mword == 8)

/// Elim lemma: extract hd_address-free bound from object_fits_in_heap
let object_fits_to_bound (h: obj_addr) (g: heap) : Lemma
  (requires object_fits_in_heap h g)
  (ensures U64.v h + Prims.op_Multiply (U64.v (wosize_of_object h g)) 8 <= Seq.length g)
  = hd_address_spec h;
    assert_norm (U64.v mword == 8)

/// Get all pointer fields of an object (for edges)
let rec get_pointer_fields_aux (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : GTot (seq vertex_id) (decreases (U64.v ws - U64.v i + 1))
  =
  if U64.v i > U64.v ws then Seq.empty
  else
    let v = get_field g obj i in
    let rest = 
      if U64.v i < U64.v ws then 
        get_pointer_fields_aux g obj (U64.add i 1UL) ws
      else 
        Seq.empty 
    in
    if is_pointer_field v then begin
      is_pointer_field_is_obj_addr v;
      // v is an obj_addr (pointer fields store object addresses in OCaml)
      // Return v directly — vertices are obj_addrs, so edges should be too
      Seq.cons v rest
    end
    else rest

let get_pointer_fields (g: heap) (h_addr: obj_addr) : GTot (seq vertex_id) =
  if not (object_fits_in_heap h_addr g) then Seq.empty
  else
    let ws = wosize_of_object h_addr g in
    if is_no_scan h_addr g then Seq.empty
    else get_pointer_fields_aux g h_addr 1UL ws

/// ---------------------------------------------------------------------------
/// Graph Construction from Heap
/// ---------------------------------------------------------------------------

/// Build edge tuples from successors
let rec make_edges (h_addr: vertex_id) (succs: seq vertex_id)
  : Tot edge_list (decreases Seq.length succs)
  =
  if Seq.length succs = 0 then Seq.empty
  else
    let dst = Seq.head succs in
    Seq.cons (h_addr, dst) (make_edges h_addr (Seq.tail succs))

/// Build edges from one object to its successors
let object_edges (g: heap) (h_addr: obj_addr) : GTot edge_list =
  let succs = get_pointer_fields g h_addr in
  make_edges h_addr succs

/// Build all edges from objects list
let rec all_edges (g: heap) (objs: seq obj_addr) 
  : GTot edge_list (decreases Seq.length objs)
  =
  if Seq.length objs = 0 then Seq.empty
  else
    let h_addr = Seq.head objs in
    let edges1 = object_edges g h_addr in
    Seq.append edges1 (all_edges g (Seq.tail objs))

/// ---------------------------------------------------------------------------
/// Coercion: obj_addr seq → vertex_id seq
/// ---------------------------------------------------------------------------

/// Since vertex_id = hp_addr and obj_addr <: hp_addr, coercion is identity
/// but F* needs explicit conversion for sequences of refined types
let rec coerce_to_vertex_list (s: seq obj_addr) : Tot vertex_list (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else Seq.cons (Seq.head s) (coerce_to_vertex_list (Seq.tail s))

/// coerce preserves membership
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let rec coerce_mem_lemma (s: seq obj_addr) (x: obj_addr)
  : Lemma (ensures Seq.mem x s <==> Seq.mem x (coerce_to_vertex_list s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      mem_cons (Seq.head s) (coerce_to_vertex_list (Seq.tail s));
      coerce_mem_lemma (Seq.tail s) x
    end
#pop-options

/// coerce preserves cons structure
#push-options "--z3rlimit 50 --fuel 2 --ifuel 1"
let coerce_cons_lemma (hd: obj_addr) (tl: seq obj_addr)
  : Lemma (coerce_to_vertex_list (Seq.cons hd tl) == Seq.cons hd (coerce_to_vertex_list tl))
  = assert (Seq.length (Seq.cons hd tl) > 0);
    assert (Seq.head (Seq.cons hd tl) == hd);
    assert (Seq.equal (Seq.tail (Seq.cons hd tl)) tl)
#pop-options

/// ---------------------------------------------------------------------------
/// Create Graph from Heap
/// ---------------------------------------------------------------------------
///
/// Takes object list as parameter — callers provide their own enumeration.
/// This avoids HeapGraph depending on any specific `objects` function.

let create_graph_from_heap (g: heap) (objs: seq obj_addr)
  : Ghost graph_state
         (requires is_vertex_set (coerce_to_vertex_list objs))
         (ensures fun _ -> True)
  =
  let verts = coerce_to_vertex_list objs in
  let edges = all_edges g objs in
  { vertices = verts; edges = edges }

/// graph_vertices_mem: object membership ↔ vertex membership
let graph_vertices_mem (g: heap) (objs: seq obj_addr{is_vertex_set (coerce_to_vertex_list objs)}) (h_addr: obj_addr) 
  : Lemma (Seq.mem h_addr objs <==> 
           Seq.mem h_addr (create_graph_from_heap g objs).vertices)
  = coerce_mem_lemma objs h_addr

/// ---------------------------------------------------------------------------
/// Field/Color Preservation Lemmas
/// ---------------------------------------------------------------------------

module Addr = Pulse.Lib.Address

/// set_field preserves header color (field is at offset >= mword from header)
val set_field_preserves_color : (g: heap) -> (obj: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (v: U64.t) ->
  Lemma (requires U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= heap_size)
        (ensures color_of_object obj (set_field g obj i v) == color_of_object obj g)

let set_field_preserves_color g obj i v =
  let hd = hd_address obj in
  Addr.field_header_separated_heap hd i;
  let fa = U64.add hd (U64.mul mword i) in
  read_write_different g fa hd v;
  color_of_object_spec obj g;
  color_of_object_spec obj (set_field g obj i v)

/// set_field preserves color at a different address
val set_field_preserves_other_color : (g: heap) -> (obj: obj_addr) -> (obj2: obj_addr) -> (i: U64.t{U64.v i >= 1}) -> (v: U64.t) ->
  Lemma (requires U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= heap_size /\
                  obj <> obj2 /\
                  (U64.v (hd_address obj) + U64.v mword * (U64.v i + 1) <= U64.v (hd_address obj2) \/
                   U64.v (hd_address obj2) + U64.v mword <= U64.v (hd_address obj) + U64.v mword * U64.v i))
        (ensures color_of_object obj2 (set_field g obj i v) == color_of_object obj2 g)

let set_field_preserves_other_color g obj obj2 i v =
  let hd = hd_address obj in
  let hd2 = hd_address obj2 in
  hd_address_injective obj obj2;
  Addr.field_disjoint_from_other2 hd hd2 i;
  let fa = U64.add hd (U64.mul mword i) in
  read_write_different g fa hd2 v;
  color_of_object_spec obj2 g;
  color_of_object_spec obj2 (set_field g obj i v)

/// ---------------------------------------------------------------------------
/// Edge Membership Lemmas
/// ---------------------------------------------------------------------------

/// If v is in succs, then (h_addr, v) is in make_edges h_addr succs
let rec make_edges_mem (h_addr: vertex_id) (succs: seq vertex_id) (v: vertex_id)
  : Lemma (requires Seq.mem v succs)
          (ensures Seq.mem (h_addr, v) (make_edges h_addr succs))
          (decreases Seq.length succs)
  = if Seq.length succs = 0 then ()
    else if Seq.head succs = v then 
      Seq.mem_cons (h_addr, v) (make_edges h_addr (Seq.tail succs))
    else begin
      make_edges_mem h_addr (Seq.tail succs) v;
      let hd = Seq.head succs in
      Seq.mem_cons (h_addr, hd) (make_edges h_addr (Seq.tail succs))
    end

/// If a pointer field at index j (i <= j <= ws) exists, it's in get_pointer_fields_aux
let rec get_pointer_fields_aux_mem (g: heap) (obj: obj_addr) (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  (j: U64.t{U64.v j >= 1})
  : Lemma (requires U64.v j >= U64.v i /\ U64.v j <= U64.v ws /\
                    is_pointer_field (get_field g obj j))
          (ensures Seq.mem (get_field g obj j) (get_pointer_fields_aux g obj i ws))
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else begin
      let v = get_field g obj i in
      let rest = 
        if U64.v i < U64.v ws then get_pointer_fields_aux g obj (U64.add i 1UL) ws
        else Seq.empty
      in
      if U64.v i = U64.v j then begin
        assert (v == get_field g obj j);
        if is_pointer_field v then begin
          is_pointer_field_is_obj_addr v;
          Seq.mem_cons v rest
        end else ()
      end else begin
        assert (U64.v j > U64.v i);
        assert (U64.v i < U64.v ws);
        get_pointer_fields_aux_mem g obj (U64.add i 1UL) ws j;
        assert (Seq.mem (get_field g obj j) rest);
        if is_pointer_field v then begin
          is_pointer_field_is_obj_addr v;
          Seq.mem_cons v rest
        end else ()
      end
    end

/// object_edges of obj ⊆ all_edges when obj ∈ objs
let rec all_edges_superset (g: heap) (objs: seq obj_addr) (obj: obj_addr)
  : Lemma (requires Seq.mem obj objs)
          (ensures (forall e. Seq.mem e (object_edges g obj) ==> Seq.mem e (all_edges g objs)))
          (decreases Seq.length objs)
  = if Seq.length objs = 0 then ()
    else if Seq.head objs = obj then
      let aux (e: edge) : Lemma (requires Seq.mem e (object_edges g obj))
                                (ensures Seq.mem e (all_edges g objs))
        = Seq.lemma_mem_append (object_edges g obj) (all_edges g (Seq.tail objs))
      in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    else begin
      all_edges_superset g (Seq.tail objs) obj;
      let edges1 = object_edges g (Seq.head objs) in
      let aux (e: edge) : Lemma (requires Seq.mem e (object_edges g obj))
                                (ensures Seq.mem e (all_edges g objs))
        = Seq.lemma_mem_append edges1 (all_edges g (Seq.tail objs))
      in FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end

/// Combined: pointer field at index j → graph edge
let pointer_field_is_graph_edge (g: heap) (objs: seq obj_addr) (obj: obj_addr)
    (j: U64.t{U64.v j >= 1})
  : Lemma (requires Seq.mem obj objs /\ is_vertex_set (coerce_to_vertex_list objs) /\
                    object_fits_in_heap obj g /\ ~(is_no_scan obj g) /\
                    U64.v j <= U64.v (wosize_of_object obj g) /\
                    is_pointer_field (get_field g obj j))
          (ensures mem_graph_edge (create_graph_from_heap g objs) obj (get_field g obj j))
  = let ws = wosize_of_object obj g in
    let v = get_field g obj j in
    get_pointer_fields_aux_mem g obj 1UL ws j;
    assert (Seq.mem v (get_pointer_fields_aux g obj 1UL ws));
    assert (Seq.mem v (get_pointer_fields g obj));
    make_edges_mem obj (get_pointer_fields g obj) v;
    assert (Seq.mem (obj, v) (object_edges g obj));
    all_edges_superset g objs obj

/// ---------------------------------------------------------------------------
/// Successors Bridge: successors(create_graph g) x == get_pointer_fields g x
/// ---------------------------------------------------------------------------

/// Helper: tail of coerce = coerce of tail
#push-options "--fuel 2 --ifuel 1"
let coerce_tail_lemma (objs: seq obj_addr)
  : Lemma (requires Seq.length objs > 0)
          (ensures Seq.equal (Seq.tail (coerce_to_vertex_list objs))
                             (coerce_to_vertex_list (Seq.tail objs)))
  = assert (coerce_to_vertex_list objs == 
            Seq.cons (Seq.head objs) (coerce_to_vertex_list (Seq.tail objs)))
#pop-options

/// successors_aux of make_edges: filtering for the source vertex returns all successors
val successors_aux_make_edges_self : (h: vertex_id) -> (succs: seq vertex_id) ->
  Lemma (ensures Seq.equal (successors_aux (make_edges h succs) h) succs)
        (decreases Seq.length succs)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
let rec successors_aux_make_edges_self h succs =
  if Seq.length succs = 0 then ()
  else begin
    let dst = Seq.head succs in
    let tl = Seq.tail succs in
    // make_edges h succs = cons (h, dst) (make_edges h tl)
    // Use successors_aux_cons to unfold successors_aux on this cons
    successors_aux_cons (h, dst) (make_edges h tl) h;
    // Now: successors_aux (make_edges h succs) h == cons dst (successors_aux (make_edges h tl) h)
    successors_aux_make_edges_self h tl
    // IH: successors_aux (make_edges h tl) h == tl
    // So: successors_aux (make_edges h succs) h == cons dst tl == succs
  end
#pop-options

/// successors_aux of make_edges: filtering for a different vertex returns empty
val successors_aux_make_edges_other : (h: vertex_id) -> (succs: seq vertex_id) -> (v: vertex_id) ->
  Lemma (requires v <> h)
        (ensures Seq.equal (successors_aux (make_edges h succs) v) Seq.empty)
        (decreases Seq.length succs)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
let rec successors_aux_make_edges_other h succs v =
  if Seq.length succs = 0 then ()
  else begin
    let dst = Seq.head succs in
    successors_aux_cons (h, dst) (make_edges h (Seq.tail succs)) v;
    successors_aux_make_edges_other h (Seq.tail succs) v
  end
#pop-options

/// successors_aux distributes over append (local proof)
private val successors_aux_append : (e1: edge_list) -> (e2: edge_list) -> (v: vertex_id) ->
  Lemma (ensures Seq.equal (successors_aux (Seq.append e1 e2) v)
                           (Seq.append (successors_aux e1 v) (successors_aux e2 v)))
        (decreases Seq.length e1)

#push-options "--z3rlimit 400 --fuel 4 --ifuel 2 --split_queries always"
private let rec successors_aux_append e1 e2 v =
  if Seq.length e1 = 0 then begin
    assert (Seq.equal (Seq.append e1 e2) e2);
    Seq.lemma_eq_elim (Seq.append e1 e2) e2;
    assert (successors_aux (Seq.append e1 e2) v == successors_aux e2 v);
    assert (Seq.equal (successors_aux e1 v) Seq.empty);
    Seq.lemma_eq_elim (successors_aux e1 v) Seq.empty;
    assert (Seq.equal (Seq.append Seq.empty (successors_aux e2 v)) (successors_aux e2 v));
    Seq.lemma_eq_elim (Seq.append Seq.empty (successors_aux e2 v)) (successors_aux e2 v)
  end
  else begin
    let hd = Seq.head e1 in
    let (src, dst) = hd in
    let tl1 = Seq.tail e1 in
    // Establish: append e1 e2 == cons hd (append tl1 e2)
    assert (Seq.equal (Seq.append e1 e2) (Seq.cons hd (Seq.append tl1 e2)));
    Seq.lemma_eq_elim (Seq.append e1 e2) (Seq.cons hd (Seq.append tl1 e2));
    assert (Seq.append e1 e2 == Seq.cons hd (Seq.append tl1 e2));
    // Unfold successors_aux on combined
    successors_aux_cons hd (Seq.append tl1 e2) v;
    // Unfold successors_aux on e1
    assert (Seq.equal e1 (Seq.cons hd tl1));
    Seq.lemma_eq_elim e1 (Seq.cons hd tl1);
    successors_aux_cons hd tl1 v;
    // IH
    successors_aux_append tl1 e2 v;
    if src = v then begin
      FStar.Seq.Properties.append_cons dst (successors_aux tl1 v) (successors_aux e2 v);
      assert (Seq.equal (successors_aux (Seq.append e1 e2) v)
                         (Seq.append (successors_aux e1 v) (successors_aux e2 v)));
      Seq.lemma_eq_elim (successors_aux (Seq.append e1 e2) v)
                         (Seq.append (successors_aux e1 v) (successors_aux e2 v))
    end else begin
      assert (Seq.equal (successors_aux (Seq.append e1 e2) v)
                         (Seq.append (successors_aux e1 v) (successors_aux e2 v)));
      Seq.lemma_eq_elim (successors_aux (Seq.append e1 e2) v)
                         (Seq.append (successors_aux e1 v) (successors_aux e2 v))
    end
  end
#pop-options

/// Helper: successors_aux of all_edges for x ∉ objs = empty
val successors_aux_all_edges_nonmember : (g: heap) -> (objs: seq obj_addr) -> (x: obj_addr) ->
  Lemma (requires ~(Seq.mem x objs) /\ is_vertex_set (coerce_to_vertex_list objs))
        (ensures Seq.equal (successors_aux (all_edges g objs) x) Seq.empty)
        (decreases Seq.length objs)

let rec successors_aux_all_edges_nonmember g objs x =
  if Seq.length objs = 0 then ()
  else begin
    let h_addr = Seq.head objs in
    let edges1 = object_edges g h_addr in
    let rest = all_edges g (Seq.tail objs) in
    successors_aux_append edges1 rest x;
    successors_aux_make_edges_other h_addr (get_pointer_fields g h_addr) x;
    is_vertex_set_tail (coerce_to_vertex_list objs);
    coerce_tail_lemma objs;
    successors_aux_all_edges_nonmember g (Seq.tail objs) x
  end

/// successors_aux of all_edges for x ∈ objs (vertex set) = get_pointer_fields g x
val successors_aux_all_edges : (g: heap) -> (objs: seq obj_addr) -> (x: obj_addr) ->
  Lemma (requires Seq.mem x objs /\ is_vertex_set (coerce_to_vertex_list objs))
        (ensures Seq.equal (successors_aux (all_edges g objs) x)
                           (get_pointer_fields g x))
        (decreases Seq.length objs)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec successors_aux_all_edges g objs x =
  if Seq.length objs = 0 then ()
  else begin
    let h_addr = Seq.head objs in
    let edges1 = object_edges g h_addr in
    let rest = all_edges g (Seq.tail objs) in
    successors_aux_append edges1 rest x;
    if h_addr = x then begin
      successors_aux_make_edges_self x (get_pointer_fields g x);
      // is_vertex_set → head ∉ tail
      coerce_tail_lemma objs;
      coerce_mem_lemma (Seq.tail objs) x;
      assert (~(Seq.mem x (Seq.tail objs)));
      is_vertex_set_tail (coerce_to_vertex_list objs);
      successors_aux_all_edges_nonmember g (Seq.tail objs) x
    end else begin
      successors_aux_make_edges_other h_addr (get_pointer_fields g h_addr) x;
      is_vertex_set_tail (coerce_to_vertex_list objs);
      coerce_tail_lemma objs;
      Seq.lemma_mem_inversion objs;
      successors_aux_all_edges g (Seq.tail objs) x
    end
  end
#pop-options

/// Top-level: successors in created graph = get_pointer_fields
val successors_eq_pointer_fields : (g: heap) -> (objs: seq obj_addr) -> (x: obj_addr) ->
  Lemma (requires Seq.mem x objs /\ is_vertex_set (coerce_to_vertex_list objs))
        (ensures Seq.equal (successors (create_graph_from_heap g objs) x)
                           (get_pointer_fields g x))

let successors_eq_pointer_fields g objs x =
  successors_aux_all_edges g objs x
