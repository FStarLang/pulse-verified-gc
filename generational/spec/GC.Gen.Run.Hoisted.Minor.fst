/// The graph half of `GC.Gen.Run.Hoisted.Steps.minor_promotes`: the nursery
/// objects a minor collection can reach -- through nursery objects, from the
/// roots it is handed (the program's pointer roots and the values of the
/// remembered slots, `collector_roots`) -- are exactly the blocks of the
/// objects `GC.Gen.Run.IdAccounting.promoted` names (`minor_graph`).
///
/// The real graph is read off the nursery (`GC.Gen.Reachability`); every
/// nursery block and every kept major block holds a faithful copy of its
/// object (`copies_faithful`), so a field (or a root, or a remembered slot)
/// is the translation of an ideal value: a word lies outside both heaps, a
/// pointer into the major heap is never young, and a pointer `Ptr {head; k}`
/// into the nursery resolves (through the infix header, whose size is `k`)
/// to `head`'s block.  The remembered slots are the accounting's (`rt_rep`).
module GC.Gen.Run.Hoisted.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents
open GC.Gen.Run.IdAccounting
open GC.Gen.Run.Hoisted.Base
open GC.Gen.Run.Hoisted.Frame

module U64 = FStar.UInt64
module I = GC.Model.Ideal
module GB = GC.Gen.Barrier
module GBase = GC.Gen.Base
module Promote = GC.Gen.Promote
module Reach = GC.Gen.Reachability
module RTg = GC.Gen.Run.RememberedTargets
module St = GC.Gen.Run.Hoisted.Start

/// ---------------------------------------------------------------------------
/// The facts read at a minor collection
/// ---------------------------------------------------------------------------

let mfacts (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
           (roots: seq U64.t) : prop =
  ids_injective_on_allocated r.memory ids /\ copies_faithful r.memory h im ids /\ I.wf_memory im /\ I.wf_objects im /\
  minor_wf r.memory.nursery /\ blocks_fit r.memory.major /\
  acc_inv r h ids a /\ a.mem == im /\ rt_ok a /\
  roots_represented ids (ptr_values im.I.roots) roots

/// ---------------------------------------------------------------------------
/// Words and the nursery
/// ---------------------------------------------------------------------------

let to_minor_offset_id (w: U64.t) : Lemma (GBase.to_minor_offset w == w) =
  GC.Gen.Run.MinorBase.minor_base_addr_zero ()

/// The infix header of a nursery closure gives the offset back to it.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0 --using_facts_from '* -FStar.UInt.to_vec -FStar.UInt.from_vec -FStar.BitVector'"
let nursery_infix (ms: minor_state) (o: U64.t) (k: pos) (wd: U64.t) (w: U64.t)
  : Lemma (requires U64.v o >= 8 /\ U64.v o % 8 == 0 /\ U64.v o + 8 * k < GBase.minor_heap_size /\
                    U64.v w == U64.v o + 8 * k /\
                    minor_read_field ms o (k - 1) == wd /\ getTag wd == infix_tag /\ U64.v (getWosize wd) == k)
          (ensures is_infix_in_minor ms w /\ infix_parent ms w == o)
  = getTag_spec wd;
    getWosize_spec wd;
    infix_tag_val ();
    FStar.Math.Lemmas.lemma_mod_plus (U64.v o) k 8;
    assert (U64.v w - 8 == U64.v o + (k - 1) * 8);
    assert (U64.uint_to_t (U64.v w - 8) == U64.uint_to_t (U64.v o + (k - 1) * 8));
    assert (minor_read_word ms.data (U64.uint_to_t (U64.v w - 8)) == wd);
    assert (minor_tag ms w == 249);
    assert (minor_wosize ms w == k)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let infix_branch (ms: minor_state) (ids: block_id_map) (o: U64.t) (ob: I.ideal_object) (k: nat) (w: U64.t)
  : Lemma (requires k > 0 /\ k < ob.I.size /\ U64.v o >= 8 /\ U64.v o % 8 == 0 /\
                    U64.v o + 8 * ob.I.size <= GBase.minor_heap_size /\ U64.v w == U64.v o + 8 * k /\
                    (forall (i: nat). i < ob.I.size ==> content_rep ids (I.field_at ob i) (minor_read_field ms o i)) /\
                    (match I.field_at ob (k - 1) with
                     | I.FValue (I.Word wd) -> getTag wd == infix_tag /\ U64.v (getWosize wd) == k
                     | _ -> False))
          (ensures resolve_minor ms w == o)
  = match I.field_at ob (k - 1) with
    | I.FValue (I.Word wd) ->
        assert (content_rep ids (I.field_at ob (k - 1)) (minor_read_field ms o (k - 1)));
        nursery_infix ms o k wd w
#pop-options

/// A nursery pointer resolves to the block it points into.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let nursery_resolve (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                    (o: U64.t) (hd: I.obj_id) (k: nat)
  : Lemma (requires ids_injective_on_allocated m ids /\ copies_faithful m h im ids /\ minor_wf m.nursery /\ I.wf_objects im /\
                    ids (Nursery o) == Some hd /\ I.valid_value im (I.Ptr { I.head = hd; I.infix_offset = k }))
          (ensures (let w = ptr_value (Nursery o) k in
                    resolve_minor m.nursery w == o /\ Seq.mem o (minor_objects m.nursery) /\
                    GB.is_young w))
  = let ms = m.nursery in
    rep_of m h im ids (Nursery o) hd;
    let ob = Seq.index im.I.objects hd in
    assert (k < ob.I.size);
    nursery_ptr_shape ms o k;
    let w = ptr_value (Nursery o) k in
    minor_objects_valid ms o;
    minor_objects_body_bound ms o;
    if k = 0 then begin
      assert (minor_tag ms o == U64.v ob.I.tag);
      infix_tag_val ();
      assert (w == o)
    end else begin
      assert (block_size m (Nursery o) == ob.I.size);
      infix_branch ms ids o ob k (ptr_value (Nursery o) k)
    end
#pop-options

/// A translated value that a minor collection would follow into a nursery
/// object is a pointer to that object's block.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let word_to_nursery (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
                    (v: I.value) (w: U64.t)
  : Lemma (requires ids_injective_on_allocated m ids /\ copies_faithful m h im ids /\ minor_wf m.nursery /\ blocks_fit m.major /\
                    I.wf_objects im /\ value_rep ids v w /\ I.valid_value im v /\
                    Seq.mem (resolve_minor m.nursery w) (minor_objects m.nursery))
          (ensures (match v with
                    | I.Ptr { I.head = hd } -> ids (Nursery (resolve_minor m.nursery w)) == Some hd
                    | I.Word _ -> False))
  = let ms = m.nursery in
    to_minor_offset_id w;
    let rw = resolve_minor ms w in
    minor_objects_valid ms rw;
    match v with
    | I.Word _ ->
        // a word is not young, so neither an infix address nor an object of the nursery
        assert (~(is_infix_in_minor ms w));
        assert (rw == w)
    | I.Ptr { I.head = hd; I.infix_offset = k } ->
        eliminate exists (b: block_addr). ids b == Some hd /\ w == ptr_value b k
        with (match b with
              | Nursery o -> nursery_resolve m h im ids o hd k
              | Major x ->
                  header_of m h im ids b hd;
                  major_ptr_shape m.major x k;
                  GBase.zero_addr_above_minor ();
                  assert (~(is_infix_in_minor ms w));
                  assert (rw == w))
#pop-options

/// ---------------------------------------------------------------------------
/// Roots
/// ---------------------------------------------------------------------------

/// Every pointer among the values is in `ptr_values`.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec ptr_values_complete (vs: seq I.value) (j: nat)
  : Lemma (requires j < Seq.length vs /\ I.Ptr? (Seq.index vs j))
          (ensures exists (i: nat). i < Seq.length (ptr_values vs) /\ Seq.index (ptr_values vs) i == Seq.index vs j)
          (decreases Seq.length vs)
  = let rest = ptr_values (Seq.tail vs) in
    if j = 0 then assert (Seq.index (ptr_values vs) 0 == Seq.head vs)
    else begin
      ptr_values_complete (Seq.tail vs) (j - 1);
      assert (Seq.index (Seq.tail vs) (j - 1) == Seq.index vs j);
      eliminate exists (i: nat). i < Seq.length rest /\ Seq.index rest i == Seq.index (Seq.tail vs) (j - 1)
      with (if I.Ptr? (Seq.head vs) then assert (Seq.index (ptr_values vs) (i + 1) == Seq.index rest i)
            else ())
    end
#pop-options

/// The block of a value in the remembered slot `(x, j)` of a kept block.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 1"
let slot_value (m: real_memory) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
               (x: obj_addr) (xid: I.obj_id) (j: nat)
  : Lemma (requires ids_injective_on_allocated m ids /\ copies_faithful m h im ids /\ blocks_fit m.major /\ I.wf_memory im /\
                    ids (Major x) == Some xid /\ kept h x /\ Some? (field_value im xid j))
          (ensures (let Some v = field_value im xid j in
                    let s = major_slot x j in
                    U64.v s == U64.v x + 8 * j /\ U64.v s < heap_size /\ U64.v s % 8 == 0 /\
                    value_rep ids v (read_word m.major (s <: hp_addr)) /\ I.valid_value im v))
  = rep_of m h im ids (Major x) xid;
    let o = Seq.index im.I.objects xid in
    let I.Scannable vs = o.I.fields in
    assert (j < Seq.length vs);
    assert (I.field_at o j == I.FValue (Seq.index vs j));
    assert (content_rep ids (I.field_at o j) (block_field m (Major x) j));
    St.field_in_heap m.major x j;
    FStar.Math.Lemmas.small_mod (U64.v x + 8 * j) (pow2 64);
    FStar.Math.Lemmas.lemma_mod_plus (U64.v x) j 8;
    let s = major_slot x j in
    assert (U64.uint_to_t (U64.v x + j * 8) == s);
    assert (block_field m (Major x) j == read_word m.major (s <: hp_addr));
    assert (I.valid_value im (Seq.index (I.field_values o) j))
#pop-options

/// ---------------------------------------------------------------------------
/// Reached ==> promoted
/// ---------------------------------------------------------------------------

let promoted_block (ids: block_id_map) (a: acc) (o: U64.t) : prop =
  exists (id: I.obj_id). ids (Nursery o) == Some id /\ promoted a id

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let root_promoted (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                  (roots: seq U64.t) (rr: U64.t)
  : Lemma (requires mfacts r h im ids a roots /\ Seq.mem rr (collector_roots r roots) /\
                    Seq.mem (resolve_minor r.memory.nursery rr) (minor_objects r.memory.nursery))
          (ensures promoted_block ids a (resolve_minor r.memory.nursery rr))
  = let m = r.memory in
    let ms = m.nursery in
    Seq.lemma_mem_append roots (GC.Gen.MinorCollectForwarding.Helpers.remembered_slot_targets m.major r.ref_table (Seq.length r.ref_table));
    if FStar.IndefiniteDescription.strong_excluded_middle (Seq.mem rr roots) then begin
      Seq.Properties.mem_index rr roots;
      eliminate exists (i: nat{i < Seq.length roots}). Seq.index roots i == rr
      with begin
        let v = Seq.index (ptr_values im.I.roots) i in
        St.ptr_values_index im.I.roots i;
        eliminate exists (jj: nat). jj < Seq.length im.I.roots /\ Seq.index im.I.roots jj == v
        with begin
          assert (I.valid_value im v);
          word_to_nursery m h im ids v rr;
          match v with
          | I.Ptr { I.head = hd } ->
              assert (a.nurs hd);
              assert (I.root_names a.mem hd);
              assert (promo_within a 0 hd)
        end
      end
    end else begin
      RTg.remembered_mem m.major r.ref_table (Seq.length r.ref_table) rr;
      eliminate exists (i: nat). RTg.slot_target m.major r.ref_table (Seq.length r.ref_table) i rr
      with begin
        eliminate exists (x: obj_addr) (j: nat) (xid: I.obj_id).
          ids (Major x) == Some xid /\ a.rt xid j /\ Seq.index r.ref_table i == major_slot x j
        with begin
          rt_block_kept h ids a m x xid;
          assert (Some? (field_value im xid j));
          slot_value m h im ids x xid j;
          let Some v = field_value im xid j in
          to_minor_offset_id (read_word m.major (Seq.index r.ref_table i <: hp_addr));
          word_to_nursery m h im ids v rr;
          match v with
          | I.Ptr { I.head = hd } ->
              assert (a.nurs hd);
              assert (promo_within a 0 hd)
        end
      end
    end
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 10"
let promo_step (a: acc) (n: nat) (src id: I.obj_id)
  : Lemma (requires promo_within a n src /\ I.points_to a.mem src id /\ a.nurs id)
          (ensures promo_within a (n + 1) id)
  = ()
#pop-options

let scannable_of_tag (im: I.ideal_memory) (id: I.obj_id)
  : Lemma (requires I.wf_objects im /\ I.valid_id im id /\ U64.v (Seq.index im.I.objects id).I.tag < 251)
          (ensures I.Scannable? (Seq.index im.I.objects id).I.fields)
  = no_scan_tag_val ()

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let succ_promoted (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                  (roots: seq U64.t) (x y: U64.t)
  : Lemma (requires mfacts r h im ids a roots /\ promoted_block ids a x /\
                    Seq.mem y (Reach.minor_successors r.memory.nursery x))
          (ensures promoted_block ids a y)
  = let m = r.memory in
    let ms = m.nursery in
    Reach.minor_successors_char ms x y;
    eliminate exists (i: nat). i < minor_scan_wosize ms x /\
        resolve_minor ms (GBase.to_minor_offset (minor_read_field ms x i)) == y /\
        GBase.is_minor_addr y /\ Seq.mem y (minor_objects ms)
    with eliminate exists (xid: I.obj_id). ids (Nursery x) == Some xid /\ promoted a xid
    with begin
      rep_of m h im ids (Nursery x) xid;
      let o = Seq.index im.I.objects xid in
      minor_scan_wosize_cases ms x;
      no_scan_tag_val ();
      assert (minor_tag ms x == U64.v o.I.tag);
      assert (minor_tag ms x < 251);
      scannable_of_tag im xid;
      assert (I.Scannable? o.I.fields);
      let I.Scannable vs = o.I.fields in
      let w = minor_read_field ms x i in
      assert (I.field_at o i == I.FValue (Seq.index vs i));
      assert (content_rep ids (I.field_at o i) (block_field m (Nursery x) i));
      assert (value_rep ids (Seq.index vs i) w);
      assert (I.field_values o == vs);
      assert (I.valid_value im (Seq.index (I.field_values o) i));
      to_minor_offset_id w;
      word_to_nursery m h im ids (Seq.index vs i) w;
      match Seq.index vs i with
      | I.Ptr { I.head = hd } ->
          assert (I.points_to im xid hd);
          assert (a.nurs hd);
          eliminate exists (n: nat). promo_within a n xid
          with promo_step a n xid hd
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Promoted ==> reached
/// ---------------------------------------------------------------------------

let reached_block (r: real_state) (roots: seq U64.t) (ids: block_id_map) (id: I.obj_id) : prop =
  exists (o: U64.t). ids (Nursery o) == Some id /\
    Seq.mem o (Reach.minor_reachable r.memory.nursery (collector_roots r roots))

/// A root of the collection that resolves to a nursery block reaches it.
let root_reaches (r: real_state) (roots: seq U64.t) (ids: block_id_map) (id: I.obj_id) (o: U64.t) (rr: U64.t)
  : Lemma (requires ids (Nursery o) == Some id /\ Seq.mem rr (collector_roots r roots) /\
                    resolve_minor r.memory.nursery rr == o /\ Seq.mem o (minor_objects r.memory.nursery))
          (ensures reached_block r roots ids id)
  = Reach.minor_reachable_roots r.memory.nursery (collector_roots r roots)

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let seed_reached (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                 (roots: seq U64.t) (id: I.obj_id)
  : Lemma (requires mfacts r h im ids a roots /\ promo_seed a id)
          (ensures reached_block r roots ids id)
  = let m = r.memory in
    let ms = m.nursery in
    let tgs = GC.Gen.MinorCollectForwarding.Helpers.remembered_slot_targets m.major r.ref_table (Seq.length r.ref_table) in
    eliminate exists (o0: U64.t). ids (Nursery o0) == Some id
    with begin
      if FStar.IndefiniteDescription.strong_excluded_middle (I.root_names im id) then begin
        eliminate exists (j: nat). j < Seq.length im.I.roots /\ I.target (Seq.index im.I.roots j) == Some id
        with begin
          ptr_values_complete im.I.roots j;
          eliminate exists (i: nat). i < Seq.length (ptr_values im.I.roots) /\
                                     Seq.index (ptr_values im.I.roots) i == Seq.index im.I.roots j
          with begin
            let rr = Seq.index roots i in
            let I.Ptr { I.infix_offset = k } = Seq.index im.I.roots j in
            assert (value_rep ids (Seq.index im.I.roots j) rr);
            assert (I.valid_value im (Seq.index im.I.roots j));
            eliminate exists (b: block_addr). ids b == Some id /\ rr == ptr_value b k
            with begin
              assert (b == Nursery o0);
              nursery_resolve m h im ids o0 id k;
              Seq.lemma_mem_append roots tgs;
              root_reaches r roots ids id o0 rr
            end
          end
        end
      end else begin
        eliminate exists (x: I.obj_id) (j: nat). a.rt x j /\
            (match field_value a.mem x j with Some v -> I.target v == Some id | None -> False)
        with begin
          eliminate exists (xb: obj_addr) (jj: nat). ids (Major xb) == Some x /\ jj < Seq.length r.ref_table /\
              Seq.index r.ref_table jj == major_slot xb j
          with begin
            rt_block_kept h ids a m xb x;
            slot_value m h im ids xb x j;
            let Some v = field_value im x j in
            let I.Ptr { I.infix_offset = k } = v in
            let s = major_slot xb j in
            let w = read_word m.major (s <: hp_addr) in
            eliminate exists (b: block_addr). ids b == Some id /\ w == ptr_value b k
            with begin
              assert (b == Nursery o0);
              nursery_resolve m h im ids o0 id k;
              to_minor_offset_id w;
              assert (RTg.slot_target m.major r.ref_table (Seq.length r.ref_table) jj w);
              RTg.remembered_mem m.major r.ref_table (Seq.length r.ref_table) w;
              Seq.lemma_mem_append roots tgs;
              root_reaches r roots ids id o0 w
            end
          end
        end
      end
    end
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let step_reached (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                 (roots: seq U64.t) (src id: I.obj_id)
  : Lemma (requires mfacts r h im ids a roots /\ reached_block r roots ids src /\
                    I.points_to a.mem src id /\ a.nurs id)
          (ensures reached_block r roots ids id)
  = let m = r.memory in
    let ms = m.nursery in
    let rts = collector_roots r roots in
    eliminate exists (os: U64.t). ids (Nursery os) == Some src /\ Seq.mem os (Reach.minor_reachable ms rts)
    with eliminate exists (o0: U64.t). ids (Nursery o0) == Some id
    with begin
      rep_of m h im ids (Nursery os) src;
      let o = Seq.index im.I.objects src in
      let vs = I.field_values o in
      eliminate exists (i: nat). i < Seq.length vs /\ I.target (Seq.index vs i) == Some id
      with begin
        assert (I.Scannable? o.I.fields);
        no_scan_tag_val ();
        minor_scan_wosize_cases ms os;
        assert (minor_tag ms os == U64.v o.I.tag);
        let w = minor_read_field ms os i in
        assert (I.field_at o i == I.FValue (Seq.index vs i));
        assert (content_rep ids (I.field_at o i) (block_field m (Nursery os) i));
        assert (I.valid_value im (Seq.index (I.field_values o) i));
        let I.Ptr { I.infix_offset = k } = Seq.index vs i in
        eliminate exists (b: block_addr). ids b == Some id /\ w == ptr_value b k
        with begin
          assert (b == Nursery o0);
          nursery_resolve m h im ids o0 id k;
          to_minor_offset_id w;
          minor_objects_valid ms o0;
          GBase.is_minor_addr_from_bounds o0;
          Reach.minor_successors_char ms os o0;
          Reach.minor_reachable_closed ms rts os o0
        end
      end
    end
#pop-options

[@@"opaque_to_smt"]
let mf (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
       (roots: seq U64.t) : prop = mfacts r h im ids a roots

let seed_reached' (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                  (roots: seq U64.t) (id: I.obj_id)
  : Lemma (requires mf r h im ids a roots /\ promo_seed a id) (ensures reached_block r roots ids id)
  = reveal_opaque (`%mf) mf; seed_reached r h im ids a roots id

let step_reached' (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                  (roots: seq U64.t) (src id: I.obj_id)
  : Lemma (requires mf r h im ids a roots /\ reached_block r roots ids src /\
                    I.points_to a.mem src id /\ a.nurs id)
          (ensures reached_block r roots ids id)
  = reveal_opaque (`%mf) mf; step_reached r h im ids a roots src id

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec promoted_reached (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                         (roots: seq U64.t) (n: nat) (id: I.obj_id)
  : Lemma (requires mf r h im ids a roots /\ promo_within a n id)
          (ensures reached_block r roots ids id)
          (decreases n)
  = if n = 0 then seed_reached' r h im ids a roots id
    else begin
      let n' : nat = n - 1 in
      if FStar.IndefiniteDescription.strong_excluded_middle (promo_within a n' id) then
        promoted_reached r h im ids a roots n' id
      else
        eliminate exists (src: I.obj_id). promo_within a n' src /\ I.points_to a.mem src id /\ a.nurs id
        with begin
          promoted_reached r h im ids a roots n' src;
          step_reached' r h im ids a roots src id
        end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The correspondence
/// ---------------------------------------------------------------------------

/// **A minor collection reaches exactly the blocks of the promoted objects.**
#push-options "--z3rlimit 40 --fuel 0 --ifuel 1"
let minor_graph (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map) (a: acc)
                (roots: seq U64.t)
  : Lemma (requires mfacts r h im ids a roots)
          (ensures forall (o: U64.t). Seq.mem o (minor_objects r.memory.nursery) ==>
                     (Seq.mem o (Reach.minor_reachable r.memory.nursery (collector_roots r roots)) <==>
                      promoted_block ids a o))
  = let ms = r.memory.nursery in
    let rts = collector_roots r roots in
    let fwd (o: U64.t) : Lemma (Seq.mem o (Reach.minor_reachable ms rts) ==> promoted_block ids a o) =
      if FStar.IndefiniteDescription.strong_excluded_middle (Seq.mem o (Reach.minor_reachable ms rts)) then begin
        FStar.Classical.forall_intro (FStar.Classical.move_requires (root_promoted r h im ids a roots));
        FStar.Classical.forall_intro_2 (fun x y -> FStar.Classical.move_requires (succ_promoted r h im ids a roots x) y);
        Reach.minor_reachable_ind ms rts (promoted_block ids a) o
      end in
    let bwd (o: U64.t) : Lemma (promoted_block ids a o ==> Seq.mem o (Reach.minor_reachable ms rts)) =
      if FStar.IndefiniteDescription.strong_excluded_middle (promoted_block ids a o) then
        eliminate exists (id: I.obj_id). ids (Nursery o) == Some id /\ promoted a id
        with eliminate exists (n: nat). promo_within a n id
        with begin
          reveal_opaque (`%mf) mf;
          promoted_reached r h im ids a roots n id;
          eliminate exists (o': U64.t). ids (Nursery o') == Some id /\ Seq.mem o' (Reach.minor_reachable ms rts)
          with assert (Nursery o' == Nursery o)
        end in
    FStar.Classical.forall_intro fwd;
    FStar.Classical.forall_intro bwd
#pop-options

/// What is promoted is in the nursery.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let rec promo_nurs (a: acc) (n: nat) (id: I.obj_id)
  : Lemma (requires promo_within a n id) (ensures a.nurs id) (decreases n)
  = if n = 0 then ()
    else if FStar.IndefiniteDescription.strong_excluded_middle (promo_within a (n - 1) id)
    then promo_nurs a (n - 1) id
    else ()
#pop-options
