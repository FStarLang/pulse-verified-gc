module GC.Gen.Run.Simulation.Collector

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MPC = GC.Spec.MarkPhase.Completeness
module GMC = GC.Gen.MarkPhase.Completeness
module GMM = GC.Gen.MarkPhase.Minor
module GI = GC.Gen.Incremental
module GenInv = GC.Gen.HeapInvariant
module HG = GC.Spec.HeapGraph
module SPI = GC.Spec.SweepPhase.Intrinsic
module SL = GC.Spec.SweepPhase.Slice
module W = GC.Spec.Walk
module GW = GC.Spec.Graph.Within
module I = GC.Model.Ideal

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Blocks of a well-formed heap
/// ---------------------------------------------------------------------------

let obj_bounds (g: heap) (y: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem y (objects zero_addr g))
          (ensures U64.v y >= U64.v zero_addr + 8 /\
                   U64.v y + 8 * U64.v (wosize_of_object y g) <= heap_size /\
                   ~(is_infix y g))
  = wf_with_parts ();
    objects_addresses_gt_start zero_addr g y;
    hd_address_spec y

/// A pointer `k` words into the allocated major block `y`, which holds the
/// ideal object `o`, where `Ptr { head; k }` is valid: a pointer
/// that resolves to `y`.
let ptr_resolves (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                 (y: obj_addr) (id: I.obj_id) (k: nat)
  : Lemma (requires well_formed_heap m.major /\ copies_faithful m h im ids /\
                    ids (Major y) == Some id /\ is_allocated m (Major y) /\ kept h y /\
                    I.valid_value im (I.Ptr { head = id; infix_offset = k }) /\
                    (k == 0 \/ k < block_size m (Major y)))
          (ensures (let w = ptr_value (Major y) k in
                    is_pointer w /\ resolve_object (w <: obj_addr) m.major == y))
  = let g = m.major in
    obj_bounds g y;
    let w = ptr_value (Major y) k in
    assert (U64.v w == U64.v y + 8 * k);
    if k = 0 then begin
      assert (w == y);
      resolve_non_infix y g
    end else begin
      let p (id: I.obj_id) : prop =
        I.valid_id im id /\ block_header_rep m (Major y) (Seq.index im.I.objects id) /\
        (faithful_block h (Major y) ==> block_rep m ids (Major y) (Seq.index im.I.objects id)) in
      assert (p id);
      let o = Seq.index im.I.objects id in
      assert (block_rep m ids (Major y) o);
      assert (content_rep ids (I.field_at o (k - 1)) (block_field m (Major y) (k - 1)));
      let I.FValue (I.Word hdr) = I.field_at o (k - 1) in
      assert (block_field m (Major y) (k - 1) == hdr);
      hd_address_spec (w <: obj_addr);
      assert (U64.v (hd_address (w <: obj_addr)) == U64.v y + 8 * (k - 1));
      assert (read_word g (hd_address (w <: obj_addr)) == hdr);
      tag_of_object_spec (w <: obj_addr) g;
      wosize_of_object_spec (w <: obj_addr) g;
      is_infix_spec (w <: obj_addr) g;
      assert (is_infix (w <: obj_addr) g);
      parent_closure_addr_nat_spec (w <: obj_addr) g;
      assert (parent_closure_addr_nat (w <: obj_addr) g == U64.v y);
      resolve_infix_spec (w <: obj_addr) g
    end

/// ---------------------------------------------------------------------------
/// The context: a well-formed real memory with an empty nursery, representing
/// a well-formed ideal memory, every allocated major block kept (idle)
/// ---------------------------------------------------------------------------

let ctx (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) : prop =
  well_formed_heap m.major /\ keyed m ids /\ copies_faithful m h im ids /\
  I.wf_memory im /\ I.wf_objects im /\ m.nursery == minor_reset m.nursery /\
  (forall (x: obj_addr). is_allocated m (Major x) ==> kept h x)

/// With the nursery empty, only major blocks have ids.
let no_nursery_ids (m: real_memory) (ids: block_id_map) (o: U64.t)
  : Lemma (requires keyed m ids /\ m.nursery == minor_reset m.nursery)
          (ensures None? (ids (Nursery o)))
  = minor_reset_objects_not_mem m.nursery o

/// A pointer value held by a word: some major block holds its head.
let ptr_rep_major (m: real_memory) (ids: block_id_map) (head: I.obj_id) (k: nat) (w: U64.t)
  : Lemma (requires keyed m ids /\ m.nursery == minor_reset m.nursery /\
                    value_rep ids (I.Ptr { head; infix_offset = k }) w)
          (ensures exists (y: obj_addr). ids (Major y) == Some head /\ is_allocated m (Major y) /\
                     w == ptr_value (Major y) k)
  = eliminate exists (b: block_addr). ids b == Some head /\ w == ptr_value b k
    with begin
      match b with
      | Nursery o -> no_nursery_ids m ids o
      | Major y -> ()
    end

/// `copies_faithful` at one block.
let faithful_at (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (b: block_addr) (id: I.obj_id)
  : Lemma (requires copies_faithful m h im ids /\ ids b == Some id /\ faithful_block h b)
          (ensures I.valid_id im id /\ block_rep m ids b (Seq.index im.I.objects id))
  = let p (id: I.obj_id) : prop =
      I.valid_id im id /\ block_header_rep m b (Seq.index im.I.objects id) /\
      (faithful_block h b ==> block_rep m ids b (Seq.index im.I.objects id)) in
    assert (p id)

/// ... and its header, at any block with an id.
let header_at (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (b: block_addr) (id: I.obj_id)
  : Lemma (requires copies_faithful m h im ids /\ ids b == Some id)
          (ensures I.valid_id im id /\ block_header_rep m b (Seq.index im.I.objects id))
  = let p (id: I.obj_id) : prop =
      I.valid_id im id /\ block_header_rep m b (Seq.index im.I.objects id) /\
      (faithful_block h b ==> block_rep m ids b (Seq.index im.I.objects id)) in
    assert (p id)

/// A field value of the ideal memory is valid.
let field_value_ok (im: I.ideal_memory) (id: I.obj_id) (i: nat)
  : Lemma (requires I.wf_memory im /\ I.valid_id im id /\
                    i < Seq.length (I.field_values (Seq.index im.I.objects id)))
          (ensures I.valid_value im (Seq.index (I.field_values (Seq.index im.I.objects id)) i))
  = let p (id: I.obj_id) (i: nat) : prop =
      I.valid_id im id /\ i < Seq.length (I.field_values (Seq.index im.I.objects id)) /\
      I.valid_value im (Seq.index (I.field_values (Seq.index im.I.objects id)) i) in
    assert (p id i)

/// A root of the ideal memory is valid.
let root_value_ok (im: I.ideal_memory) (i: nat)
  : Lemma (requires I.wf_memory im /\ i < Seq.length im.I.roots)
          (ensures I.valid_value im (Seq.index im.I.roots i))
  = ()

/// A block with an id that is scannable in the real heap holds a scannable
/// object, and the other way round.
#push-options "--ifuel 1"
let scannable_iff (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (x: obj_addr) (id: I.obj_id)
  : Lemma (requires copies_faithful m h im ids /\ I.wf_objects im /\ ids (Major x) == Some id)
          (ensures I.valid_id im id /\
                   (~(is_no_scan x m.major) <==> I.Scannable? (Seq.index im.I.objects id).I.fields) /\
                   U64.v (wosize_of_object x m.major) == (Seq.index im.I.objects id).I.size)
  = is_no_scan_spec x m.major;
    header_at m h im ids (Major x) id;
    let o = Seq.index im.I.objects id in
    assert (U64.v (tag_of_object x m.major) == U64.v o.I.tag);
    assert (I.Scannable? o.I.fields <==> I.tag_scannable o.I.tag)
#pop-options

/// The `i`-th field of a block read through the graph model's `get_field`.
let get_field_major (g: heap) (x: obj_addr) (i: nat)
  : Lemma (requires blocks_fit g /\ Seq.mem x (objects zero_addr g) /\ i < U64.v (wosize_of_object x g))
          (ensures HG.get_field g x (U64.uint_to_t (i + 1)) == major_field g x i)
  = MP.get_field_word g x (i + 1)

/// The pointer roots are exactly the roots that are pointers.
#push-options "--fuel 1 --ifuel 1"
let rec mem_ptr_values (vs: seq I.value) (x: I.value)
  : Lemma (ensures Seq.mem x (ptr_values vs) <==> I.Ptr? x /\ Seq.mem x vs)
          (decreases Seq.length vs)
  = if Seq.length vs = 0 then ()
    else begin
      mem_ptr_values (Seq.tail vs) x;
      FStar.Seq.Properties.lemma_mem_inversion vs;
      FStar.Seq.Properties.mem_cons (Seq.head vs) (ptr_values (Seq.tail vs))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Real edges are ideal edges
/// ---------------------------------------------------------------------------

#push-options "--ifuel 1 --z3rlimit 20"
let field_edge_ideal_at (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                        (u v: obj_addr) (idu: I.obj_id) (k: nat)
  : Lemma (requires ctx m h im ids /\ ids (Major u) == Some idu /\ MP.field_edge_at m.major u k v)
          (ensures exists (idv: I.obj_id). ids (Major v) == Some idv /\ I.points_to im idu idv)
  = let g = m.major in
    wf_with_parts ();
    scannable_iff m h im ids u idu;
    let o = Seq.index im.I.objects idu in
    get_field_major g u (k - 1);
    let fv = major_field g u (k - 1) in
    faithful_at m h im ids (Major u) idu;
    assert (content_rep ids (I.field_at o (k - 1)) fv);
    let I.Scannable vs = o.I.fields in
    let val_ = Seq.index vs (k - 1) in
    assert (I.field_at o (k - 1) == I.FValue val_);
    field_value_ok im idu (k - 1);
    match val_ with
    | I.Word w0 -> ()
    | I.Ptr { head; infix_offset } ->
        ptr_rep_major m ids head infix_offset fv;
        eliminate exists (y: obj_addr). ids (Major y) == Some head /\ is_allocated m (Major y) /\
                    fv == ptr_value (Major y) infix_offset
        with begin
          scannable_iff m h im ids y head;
          faithful_at m h im ids (Major y) head;
          ptr_resolves m h im ids y head infix_offset;
          assert (v == y);
          assert (I.target (Seq.index vs (k - 1)) == Some head);
          assert (I.points_to im idu head)
        end
#pop-options

let field_edge_ideal (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                     (u v: obj_addr) (idu: I.obj_id)
  : Lemma (requires ctx m h im ids /\ ids (Major u) == Some idu /\ MP.field_edge m.major u v)
          (ensures exists (idv: I.obj_id). ids (Major v) == Some idv /\ I.points_to im idu idv)
  = wf_with_parts ();
    MP.field_edge_fields m.major u v;
    eliminate exists (k: nat). MP.field_edge_at m.major u k v
    with field_edge_ideal_at m h im ids u v idu k

/// A real root names an object the program's roots name.
#push-options "--ifuel 1 --z3rlimit 20"
let root_ideal (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (rs: seq U64.t) (w: obj_addr)
  : Lemma (requires ctx m h im ids /\ roots_represented ids (ptr_values im.I.roots) rs /\ GMM.root_refs m.major rs w)
          (ensures exists (id: I.obj_id). ids (Major w) == Some id /\ I.root_names im id)
  = let g = m.major in
    eliminate exists (r: U64.t). Seq.mem r rs /\ is_pointer r /\ resolve_object (r <: obj_addr) g == w
    with begin
      let i = FStar.Seq.Properties.index_mem r rs in
      let v = Seq.index (ptr_values im.I.roots) i in
      assert (value_rep ids v r);
      mem_ptr_values im.I.roots v;
      let j = FStar.Seq.Properties.index_mem v im.I.roots in
      root_value_ok im j;
      match v with
      | I.Word _ -> ()
      | I.Ptr { head; infix_offset } ->
          ptr_rep_major m ids head infix_offset r;
          eliminate exists (y: obj_addr). ids (Major y) == Some head /\ is_allocated m (Major y) /\
                      r == ptr_value (Major y) infix_offset
          with begin
            scannable_iff m h im ids y head;
            faithful_at m h im ids (Major y) head;
            ptr_resolves m h im ids y head infix_offset;
            assert (w == y);
            assert (I.root_names im head)
          end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Ideal edges are real edges
/// ---------------------------------------------------------------------------

#push-options "--ifuel 1 --z3rlimit 20"
let ideal_edge_real (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                    (x: obj_addr) (src id: I.obj_id) (i: nat)
  : Lemma (requires ctx m h im ids /\ ids (Major x) == Some src /\ I.valid_id im src /\
                    i < Seq.length (I.field_values (Seq.index im.I.objects src)) /\
                    I.target (Seq.index (I.field_values (Seq.index im.I.objects src)) i) == Some id)
          (ensures exists (y: obj_addr). ids (Major y) == Some id /\ MP.field_edge m.major x y)
  = let g = m.major in
    wf_with_parts ();
    faithful_at m h im ids (Major x) src;
    scannable_iff m h im ids x src;
    let o = Seq.index im.I.objects src in
    let I.Scannable vs = o.I.fields in
    let v = Seq.index vs i in
    field_value_ok im src i;
    assert (I.field_at o i == I.FValue v);
    let fv = major_field g x i in
    assert (content_rep ids (I.field_at o i) fv);
    let I.Ptr { head; infix_offset } = v in
    ptr_rep_major m ids head infix_offset fv;
    eliminate exists (y: obj_addr). ids (Major y) == Some head /\ is_allocated m (Major y) /\
                fv == ptr_value (Major y) infix_offset
    with begin
      faithful_at m h im ids (Major y) head;
      ptr_resolves m h im ids y head infix_offset;
      get_field_major g x i;
      assert (MP.field_edge_at g x (i + 1) y);
      MP.field_edge_fields g x y
    end
#pop-options

/// Reachability in the real heap, one more edge.
let reachable_snoc (g: heap) (refs: obj_addr -> prop) (x y: obj_addr)
  : Lemma (requires MPC.reachable g refs x /\ MP.field_edge g x y)
          (ensures MPC.reachable g refs y)
  = eliminate exists (r0: obj_addr). refs r0 /\ GW.reach_within (MP.field_edge g) (fun _ -> True) r0 x
    with begin
      GW.reach_within_edge (MP.field_edge g) (fun _ -> True) x y;
      GW.reach_within_trans (MP.field_edge g) (fun _ -> True) r0 x y
    end

/// **What the program can reach is reachable from the real roots**, in the
/// real heap, through the blocks holding it.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let rec ideal_reaches_real (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (rs: seq U64.t)
                           (n: nat) (id: I.obj_id)
  : Lemma (requires ctx m h im ids /\ roots_represented ids (ptr_values im.I.roots) rs /\ I.reach_within im n id)
          (ensures exists (x: obj_addr). ids (Major x) == Some id /\
                     MPC.reachable m.major (GMM.root_refs m.major rs) x)
          (decreases n)
  = let g = m.major in
    let refs = GMM.root_refs g rs in
    if n = 0 then begin
      eliminate exists (i: nat). i < Seq.length im.I.roots /\ I.target (Seq.index im.I.roots i) == Some id
      with begin
        root_value_ok im i;
        let v = Seq.index im.I.roots i in
        let I.Ptr { head; infix_offset } = v in
        mem_ptr_values im.I.roots v;
        let i' = FStar.Seq.Properties.index_mem v (ptr_values im.I.roots) in
        let r = Seq.index rs i' in
        ptr_rep_major m ids head infix_offset r;
        eliminate exists (y: obj_addr). ids (Major y) == Some head /\ is_allocated m (Major y) /\
                    r == ptr_value (Major y) infix_offset
        with begin
          faithful_at m h im ids (Major y) head;
          ptr_resolves m h im ids y head infix_offset;
          assert (refs y);
          MPC.reachable_outside_refs g refs y
        end
      end
    end else begin
      eliminate I.reach_within im (n - 1) id \/
                (exists (src: I.obj_id). I.reach_within im (n - 1) src /\ I.points_to im src id)
      with ideal_reaches_real m h im ids rs (n - 1) id
      and begin
        eliminate exists (src: I.obj_id). I.reach_within im (n - 1) src /\ I.points_to im src id
        with begin
          ideal_reaches_real m h im ids rs (n - 1) src;
          eliminate exists (xs: obj_addr). ids (Major xs) == Some src /\ MPC.reachable g refs xs
          with begin
            eliminate exists (i: nat). i < Seq.length (I.field_values (Seq.index im.I.objects src)) /\
                        I.target (Seq.index (I.field_values (Seq.index im.I.objects src)) i) == Some id
            with begin
              ideal_edge_real m h im ids xs src id i;
              eliminate exists (y: obj_addr). ids (Major y) == Some id /\ MP.field_edge g xs y
              with reachable_snoc g refs xs y
            end
          end
        end
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Idle: the heap is well formed
/// ---------------------------------------------------------------------------

let idle_wf (r: real_state)
  : Lemma (requires phase_shape r /\ r.phase == Ph.Idle)
          (ensures GenInv.collection_heap_shape r.memory.nursery r.memory.major r.free_list /\
                   well_formed_heap r.memory.major)
  = GI.phase_shape_idle r.memory.nursery r.memory.major r.free_list r.scan_pos;
    GenInv.collection_heap_shape_elim r.memory.nursery r.memory.major r.free_list;
    GenInv.major_heap_shape_elim r.memory.major r.free_list

/// ---------------------------------------------------------------------------
/// A recolouring keeps the map and the copies
/// ---------------------------------------------------------------------------

/// The same allocated blocks, each with the same tag, size and fields.
let same_blocks (m m': real_memory) : prop =
  (forall (b: block_addr). is_allocated m' b <==> is_allocated m b) /\
  (forall (b: block_addr). is_allocated m b ==>
     block_tag m' b == block_tag m b /\ block_size m' b == block_size m b /\
     (forall (i: nat). i < block_size m b ==> block_field m' b i == block_field m b i))

/// Two maps that agree everywhere.
let same_ids (ids ids': block_id_map) : prop = forall (b: block_addr). ids' b == ids b

#push-options "--ifuel 1"
let restrict_same (m m': real_memory) (ids: block_id_map)
  : Lemma (requires keyed m ids /\ (forall (b: block_addr). is_allocated m' b <==> is_allocated m b))
          (ensures same_ids ids (restrict m' ids))
  = let aux (b: block_addr) : Lemma (restrict m' ids b == ids b) =
      if FStar.IndefiniteDescription.strong_excluded_middle (is_allocated m' b) then () else ()
    in
    FStar.Classical.forall_intro aux

let content_rep_same (ids ids': block_id_map) (c: I.field_content) (w: U64.t)
  : Lemma (requires same_ids ids ids' /\ content_rep ids c w)
          (ensures content_rep ids' c w)
  = match c with
    | I.FValue (I.Ptr { head; infix_offset }) ->
        eliminate exists (b: block_addr). ids b == Some head /\ w == ptr_value b infix_offset
        with assert (ids' b == Some head)
    | _ -> ()
#pop-options

let block_rep_same (m m': real_memory) (ids ids': block_id_map) (b: block_addr) (o: I.ideal_object)
  : Lemma (requires same_blocks m m' /\ same_ids ids ids' /\ is_allocated m b /\ block_rep m ids b o)
          (ensures block_rep m' ids' b o)
  = let aux (i: nat{i < o.I.size})
      : Lemma (content_rep ids' (I.field_at o i) (block_field m' b i))
      = content_rep_same ids ids' (I.field_at o i) (block_field m b i)
    in
    FStar.Classical.forall_intro aux

/// `represents`' first three clauses carry over, when every block faithful
/// for the new history was faithful for the old one.
#push-options "--ifuel 1"
let represents_same (m m': real_memory) (h h': cycle_history) (im: I.ideal_memory) (ids ids': block_id_map)
  : Lemma (requires same_blocks m m' /\ same_ids ids ids' /\ keyed m ids /\
                    copies_faithful m h im ids /\ covers_reachable im ids /\
                    (forall (b: block_addr). is_allocated m b /\ faithful_block h' b ==> faithful_block h b))
          (ensures keyed m' ids' /\ copies_faithful m' h' im ids' /\ covers_reachable im ids')
  = let aux (b: block_addr) (id: I.obj_id)
      : Lemma (requires ids' b == Some id)
              (ensures I.valid_id im id /\ block_header_rep m' b (Seq.index im.I.objects id) /\
                       (faithful_block h' b ==> block_rep m' ids' b (Seq.index im.I.objects id)))
      = header_at m h im ids b id;
        if FStar.IndefiniteDescription.strong_excluded_middle (faithful_block h' b) then begin
          faithful_at m h im ids b id;
          block_rep_same m m' ids ids' b (Seq.index im.I.objects id)
        end
    in
    introduce forall (b: block_addr) (id: I.obj_id).
        ids' b == Some id ==>
          I.valid_id im id /\ block_header_rep m' b (Seq.index im.I.objects id) /\
          (faithful_block h' b ==> block_rep m' ids' b (Seq.index im.I.objects id))
    with introduce _ ==> _ with aux b id;
    assert (copies_faithful m' h' im ids');
    assert (keyed m' ids');
    let cov (id: I.obj_id)
      : Lemma (requires I.reachable im id) (ensures exists (b: block_addr). ids' b == Some id)
      = eliminate exists (b: block_addr). ids b == Some id with assert (ids' b == Some id)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires cov)
#pop-options

/// ---------------------------------------------------------------------------
/// The start of a cycle
/// ---------------------------------------------------------------------------

#push-options "--ifuel 1 --z3rlimit 20"
let start_same_blocks (r: real_state) (roots: seq U64.t) (r': real_state)
  : Lemma (requires phase_shape r /\ start_step r roots r')
          (ensures same_blocks r.memory r'.memory /\ well_formed_heap r.memory.major)
  = idle_wf r;
    let g = r.memory.major in
    let g' = r'.memory.major in
    GC.Gen.MarkPhase.Safety.start_keeps_blocks r.memory.nursery g r.free_list roots;
    wf_with_parts ();
    let aux (b: block_addr)
      : Lemma (requires is_allocated r.memory b)
              (ensures block_tag r'.memory b == block_tag r.memory b /\
                       block_size r'.memory b == block_size r.memory b /\
                       (forall (i: nat). i < block_size r.memory b ==>
                          block_field r'.memory b i == block_field r.memory b i))
      = match b with
        | Nursery _ -> ()
        | Major x ->
            assert (SPI.same_block g g' (hd_address x));
            hd_address_spec x;
            tag_of_object_spec x g; tag_of_object_spec x g';
            wosize_of_object_spec x g; wosize_of_object_spec x g';
            obj_bounds g x;
            let f (i: nat)
              : Lemma (requires i < block_size r.memory b)
                      (ensures block_field r'.memory b i == block_field r.memory b i)
              = ()
            in
            FStar.Classical.forall_intro (FStar.Classical.move_requires f)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--ifuel 1 --z3rlimit 30"
let start_keeps r h im ids roots r' =
  let g = r.memory.major in
  let h' = update_history h r (StartCycle roots) r' in
  let ids' = update_block_ids ids (Seq.length im.I.objects) r (StartCycle roots) r' in
  assert (start_step r roots r');
  start_keeps_run_invariant r h roots r';
  start_same_blocks r roots r';
  restrict_same r.memory r'.memory ids;
  represents_same r.memory r'.memory h h' im ids ids';
  assert (ctx r.memory h im ids);
  let aux (x: obj_addr) (id: I.obj_id)
    : Lemma (requires ids' (Major x) == Some id /\ I.reachable im id) (ensures kept h' x)
    = eliminate exists (n: nat). I.reach_within im n id
      with begin
        ideal_reaches_real r.memory h im ids roots n id;
        eliminate exists (x': obj_addr). ids (Major x') == Some id /\ MPC.reachable g (GMM.root_refs g roots) x'
        with begin
          assert (Major x' == Major x);
          GMC.reachable_at_start_eq g roots;
          assert (snapshot h' x)
        end
      end
  in
  introduce forall (x: obj_addr) (id: I.obj_id). ids' (Major x) == Some id /\ I.reachable im id ==> kept h' x
  with introduce _ ==> _ with aux x id;
  assert (represents r' h' im ids')
#pop-options

/// ---------------------------------------------------------------------------
/// What the real roots reach, the program reaches
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let ideal_reachable_step (im: I.ideal_memory) (src dst: I.obj_id)
  : Lemma (requires I.reachable im src /\ I.points_to im src dst) (ensures I.reachable im dst)
  = eliminate exists (n: nat). I.reach_within im n src
    with assert (I.reach_within im (n + 1) dst)

let ideal_reachable_root (im: I.ideal_memory) (id: I.obj_id)
  : Lemma (requires I.root_names im id) (ensures I.reachable im id)
  = assert (I.reach_within im 0 id)
#pop-options

let held_reachable (im: I.ideal_memory) (ids: block_id_map) (x: obj_addr) : prop =
  exists (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id

let real_reaches_ideal (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (rs: seq U64.t) (x: obj_addr)
  : Lemma (requires ctx m h im ids /\ roots_represented ids (ptr_values im.I.roots) rs /\
                    MPC.reachable m.major (GMM.root_refs m.major rs) x)
          (ensures held_reachable im ids x)
  = let g = m.major in
    let c = held_reachable im ids in
    let roots_in (w: obj_addr) : Lemma (requires GMM.root_refs g rs w) (ensures c w) =
      root_ideal m h im ids rs w;
      eliminate exists (id: I.obj_id). ids (Major w) == Some id /\ I.root_names im id
      with ideal_reachable_root im id
    in
    let closed (u v: obj_addr) : Lemma (requires c u /\ MP.field_edge g u v) (ensures c v) =
      eliminate exists (idu: I.obj_id). ids (Major u) == Some idu /\ I.reachable im idu
      with begin
        field_edge_ideal m h im ids u v idu;
        eliminate exists (idv: I.obj_id). ids (Major v) == Some idv /\ I.points_to im idu idv
        with ideal_reachable_step im idu idv
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires roots_in);
    FStar.Classical.forall_intro_2 (fun u -> FStar.Classical.move_requires (closed u));
    MPC.reachable_closed g (GMM.root_refs g rs) c x

/// ---------------------------------------------------------------------------
/// full_gc
/// ---------------------------------------------------------------------------

#push-options "--fuel 2 --ifuel 1"
let rec snoc_inj (l1 l2: list event) (a b: event)
  : Lemma (requires l1 @ [a] == l2 @ [b]) (ensures l1 == l2 /\ a == b) (decreases l1)
  = match l1, l2 with
    | [], [] -> ()
    | [], _ :: t2 -> append_length t2 [b]
    | _ :: t1, [] -> append_length t1 [a]
    | _ :: t1, _ :: t2 -> snoc_inj t1 t2 a b

let snoc_nonempty (l: list event) (a: event)
  : Lemma (~(l @ [a] == [])) = append_length l [a]
#pop-options

/// The phases `full_gc`'s two unbounded slices leave.
#push-options "--ifuel 1 --z3rlimit 20"
let full_gc_phases (r1 r2 r3 r: real_state) (rs': seq U64.t)
  : Lemma (requires start_step r1 rs' r2 /\ slice_step r2 unbounded_budget r3 /\
                    slice_step r3 unbounded_budget r /\ phase_shape r3)
          (ensures r.phase == Ph.Idle /\ r.memory.nursery == r1.memory.nursery)
  = assert (Ph.Sweeping? r3.phase);
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    assert (unbounded_budget > heap_words);
    GI.phase_slice_finishes r3.memory.nursery r3.memory.major r3.free_list r3.phase unbounded_budget r3.scan_pos
#pop-options

/// What `full_gc` leaves, from the states along it.
#push-options "--ifuel 1 --z3rlimit 20"
let full_gc_end (r1 r2 r3 r: real_state) (rs': seq U64.t) (h1 h: cycle_history) (im: I.ideal_memory)
                (ids1 ids: block_id_map)
  : Lemma (requires run_invariant r1 h1 /\ represents r1 h1 im ids1 /\ I.wf_memory im /\ I.wf_objects im /\
                    start_step r1 rs' r2 /\
                    slice_step r2 unbounded_budget r3 /\ slice_step r3 unbounded_budget r /\
                    phase_shape r3 /\ run_invariant r h /\ represents r h im ids /\
                    h.start_memory == r1.memory /\ h.start_roots == rs' /\
                    (forall (x: obj_addr). ~(h.allocated_during_cycle x)) /\
                    roots_represented ids1 (ptr_values im.I.roots) rs' /\
                    (forall (b: block_addr) (id: I.obj_id). ids b == Some id ==> ids1 b == Some id))
          (ensures r.phase == Ph.Idle /\ r.memory.nursery == minor_reset r.memory.nursery /\
                   (forall (b: block_addr) (id: I.obj_id). ids b == Some id ==> I.reachable im id))
  = full_gc_phases r1 r2 r3 r rs';
    idle_wf r1;
    assert (ctx r1.memory h1 im ids1);
    let g1 = r1.memory.major in
    let aux (b: block_addr) (id: I.obj_id)
      : Lemma (requires ids b == Some id) (ensures I.reachable im id)
      = match b with
        | Nursery o -> no_nursery_ids r.memory ids o
        | Major x ->
            assert (is_allocated r.memory (Major x));
            assert (kept h x);
            assert (snapshot h x);
            GMC.reachable_at_start_eq g1 rs';
            assert (MPC.reachable g1 (GMM.root_refs g1 rs') x);
            assert (ids1 (Major x) == Some id);
            real_reaches_ideal r1.memory h1 im ids1 rs' x
    in
    introduce forall (b: block_addr) (id: I.obj_id). ids b == Some id ==> I.reachable im id
    with introduce _ ==> _ with aux b id
#pop-options

#push-options "--fuel 5 --ifuel 1"
let full_gc_events_snoc (es0: list event) (rs rs': seq U64.t)
  : Lemma (es0 @ full_gc_events rs rs' ==
           (((es0 @ [Minor rs]) @ [StartCycle rs']) @ [Slice unbounded_budget]) @ [Slice unbounded_budget])
  = append_assoc es0 [Minor rs] [StartCycle rs'];
    append_assoc es0 [Minor rs; StartCycle rs'] [Slice unbounded_budget];
    append_assoc es0 [Minor rs; StartCycle rs'; Slice unbounded_budget] [Slice unbounded_budget]
#pop-options


/// ---------------------------------------------------------------------------
/// A slice
/// ---------------------------------------------------------------------------

/// The blocks a step leaves allocated were allocated, with their headers
/// and fields; and a kept allocated block stays allocated.
let slice_blocks_post (r r': real_state) (h: cycle_history) : prop =
  r'.memory.nursery == r.memory.nursery /\
  (forall (x: obj_addr). is_allocated r'.memory (Major x) ==>
     is_allocated r.memory (Major x) /\ SPI.same_block r.memory.major r'.memory.major (hd_address x)) /\
  (forall (x: obj_addr). kept h x /\ is_allocated r.memory (Major x) ==> is_allocated r'.memory (Major x))

#push-options "--ifuel 1 --z3rlimit 20"
let slice_blocks_idle (r: real_state) (h: cycle_history) (budget: nat) (r': real_state)
  : Lemma (requires slice_step r budget r' /\ r.phase == Ph.Idle)
          (ensures slice_blocks_post r r' h)
  = assert (r'.memory.major == r.memory.major);
    let aux (x: obj_addr) : Lemma (SPI.same_block r.memory.major r.memory.major (hd_address x)) =
      () in
    FStar.Classical.forall_intro aux

let slice_blocks_marking (r: real_state) (h: cycle_history) (budget: nat) (r': real_state)
  : Lemma (requires phase_shape r /\ slice_step r budget r' /\ r.phase == Ph.Marking)
          (ensures slice_blocks_post r r' h)
  = let g = r.memory.major in
    GI.phase_shape_marking r.memory.nursery g r.free_list r.scan_pos;
    GenInv.collection_shape_with_elim Ph.Marking free_stw r.memory.nursery g r.free_list;
    GenInv.major_shape_with_elim Ph.Marking free_stw g r.free_list;
    MPC.mark_steps_keep_blocks g r'.memory.major r.scan_pos r'.scan_pos
#pop-options

/// **The frame of the sweep**: a slice leaves the heap from its new cursor on
/// unchanged, so the blocks still pending free keep their headers and
/// fields.  (A fact of `GC.Spec.FusedSweep.Step`'s steps -- `step_frame` --
/// not yet exported; taken as a hypothesis here.)
let sweep_frame : prop =
  forall (g: heap) (fp: U64.t) (c: U64.t) (budget: nat).
    SPI.sweep_inv_incremental g fp c ==>
    (let (g', _, st') = SL.sweep_slice g fp (SPI.state_at g c) budget in
     forall (a: hp_addr). U64.v a >= U64.v st'.GC.Spec.FusedSweep.cursor ==> read_word g' a == read_word g a)

#push-options "--ifuel 1 --z3rlimit 40"
let slice_blocks_sweeping (r: real_state) (h: cycle_history) (budget: nat) (r': real_state) (c: U64.t)
  : Lemma (requires run_invariant r h /\ slice_step r budget r' /\ r.phase == Ph.Sweeping c /\ sweep_frame)
          (ensures slice_blocks_post r r' h)
  = let g = r.memory.major in
    let fp = r.free_list in
    GI.phase_shape_sweeping r.memory.nursery g fp c r.scan_pos;
    SL.sweep_slice_phase g fp c budget;
    let (g2, fp2, st2) = SL.sweep_slice g fp (SPI.state_at g c) budget in
    let c' = st2.GC.Spec.FusedSweep.cursor in
    assert (r'.memory.major == g2);
    SPI.sweep_inv_incremental_elim g2 fp2 c';
    assert (forall (a: hp_addr). U64.v a >= U64.v c' ==> read_word g2 a == read_word g a);
    assert (MPC.sweep_in_snapshot (kept h) g c /\
            (forall (x: obj_addr). kept h x /\ U64.v x > U64.v c ==> is_black x g));
    let alloc (x: obj_addr)
      : Lemma (requires is_allocated r'.memory (Major x))
              (ensures is_allocated r.memory (Major x) /\ SPI.same_block g g2 (hd_address x))
      = if SPI.pending_free c' g2 x then begin
          assert (SPI.pending_free c g x);
          hd_address_spec x;
          W.bnext_facts g (hd_address x)
        end else
          assert (in_use (SPI.free_incremental c') g2 x)
    in
    let keep (x: obj_addr)
      : Lemma (requires kept h x /\ is_allocated r.memory (Major x))
              (ensures is_allocated r'.memory (Major x))
      = is_black_iff x g; is_white_iff x g;
        assert (~(SPI.pending_free c g x));
        assert (in_use (SPI.free_incremental c) g x);
        assert (in_use (SPI.free_incremental c') g2 x)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires alloc);
    FStar.Classical.forall_intro (FStar.Classical.move_requires keep)
#pop-options
