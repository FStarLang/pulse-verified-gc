/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesLive - the minor collection's roots and liveness
/// ---------------------------------------------------------------------------
///
/// The roots the promotion forwards (`roots_of`): the young pointers the
/// model resolves, among the program's roots and in the remembered slots
/// of pointer fields.  The live objects (`live`): nursery objects whose
/// young block the minor collection traces (`Heap.minor_live`).  Both
/// meet what `PromoteRun` asks: every root is justified (`roots_just`), and
/// liveness is closed under the fields the scan reads (`live_closed`).
/// Nothing here depends on the allocator.

module GC.Spec.Top.PagesLive

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module Y = GC.Spec.Top.Young
module YI = GC.Spec.Top.YoungInfix
module Q = GC.Spec.Top.PagesQueue
module F = GC.Spec.Pages.Promote.Follow

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// Every word is its own nursery offset.
let tmo_id (v: U64.t) : Lemma (to_minor_offset v == v)
  = if U64.v v % 8 = 0 then begin
      if U64.v v < minor_heap_size then to_minor_offset_in_minor_range v
      else to_minor_offset_stable_above_minor v
    end

/// A young pointer the model resolves, as a word.
let yword (y: M.mheap) (v: M.value) : GTot (seq U64.t) =
  match v with
  | M.VPtr (M.Young a) ->
    if Some? (M.resolve y a) && 8 * a + 16 <= minor_heap_size
    then (Y.msz (); Seq.create 1 (U64.uint_to_t (8 * a + 8))) else Seq.empty
  | _ -> Seq.empty

let rec yroots (y: M.mheap) (rs: list M.value) : GTot (seq U64.t) (decreases rs) =
  match rs with [] -> Seq.empty | v :: tl -> Seq.append (yword y v) (yroots y tl)

let rec yrem (m y: M.mheap) (rem: list M.slot) : GTot (seq U64.t) (decreases rem) =
  match rem with
  | [] -> Seq.empty
  | (o, i) :: tl -> Seq.append (if M.ptr_field m o i then yword y (M.field m o i) else Seq.empty) (yrem m y tl)

/// **The roots the promotion forwards.**
let roots_of (w: M.world) : GTot (seq U64.t) = Seq.append (yroots w.M.yng w.M.roots) (yrem w.M.maj w.M.yng w.M.rem)

/// **The live nursery objects.**
let live (w: M.world) (ms: minor_state) (x: U64.t) : prop =
  Seq.mem x (minor_objects ms) /\ M.minor_live w (Q.yof x)

/// ---------------------------------------------------------------------------
/// The roots are live
/// ---------------------------------------------------------------------------

/// A root word: a young pointer the model resolves to a live block.
let root_ok (w: M.world) (r: U64.t) : prop =
  exists (a o: nat). 8 * a + 16 <= minor_heap_size /\ U64.v r == 8 * a + 8 /\
    M.resolve w.M.yng a == Some o /\ M.minor_live w o

let mem_empty (u: U64.t) : Lemma (~(Seq.mem u (Seq.empty #U64.t)))
  = assert_norm (Seq.count u (Seq.empty #U64.t) == 0)

let mem_one (u x: U64.t) : Lemma (Seq.mem u (Seq.create 1 x) <==> u == x)
  = assert (Seq.equal (Seq.create 1 x) (Seq.cons x Seq.empty));
    FStar.Seq.Properties.mem_cons x (Seq.empty #U64.t);
    mem_empty u

let yword_ok (w: M.world) (v: M.value) (u: U64.t)
  : Lemma (requires Seq.mem u (yword w.M.yng v) /\
                    (forall (a o: nat). v == M.VPtr (M.Young a) /\ M.resolve w.M.yng a == Some o ==> M.minor_live w o))
          (ensures root_ok w u)
  = mem_empty u;
    match v with
    | M.VPtr (M.Young a) ->
      Y.msz ();
      mem_one u (U64.uint_to_t (8 * a + 8));
      let Some o = M.resolve w.M.yng a in
      assert (M.minor_live w o)
    | _ -> ()

#push-options "--fuel 1"
let rec yroots_ok (w: M.world) (rs: list M.value) (u: U64.t)
  : Lemma (requires Seq.mem u (yroots w.M.yng rs) /\ (forall (v: M.value). L.memP v rs ==> L.memP v w.M.roots))
          (ensures root_ok w u) (decreases rs)
  = match rs with
    | [] -> mem_empty u
    | v :: tl ->
      FStar.Seq.Properties.lemma_mem_append (yword w.M.yng v) (yroots w.M.yng tl);
      if Seq.mem u (yword w.M.yng v) then begin
        let lv (a o: nat) : Lemma (v == M.VPtr (M.Young a) /\ M.resolve w.M.yng a == Some o ==> M.minor_live w o)
          = if FStar.IndefiniteDescription.strong_excluded_middle (v == M.VPtr (M.Young a) /\ M.resolve w.M.yng a == Some o)
            then begin
              let l : M.mlive w o = M.LRoot o a () in
              assert (M.minor_live w o)
            end in
        FStar.Classical.forall_intro_2 lv;
        yword_ok w v u
      end
      else yroots_ok w tl u

let rec yrem_ok (w: M.world) (rem: list M.slot) (u: U64.t)
  : Lemma (requires Seq.mem u (yrem w.M.maj w.M.yng rem) /\ (forall (s: M.slot). L.memP s rem ==> L.memP s w.M.rem))
          (ensures root_ok w u) (decreases rem)
  = match rem with
    | [] -> mem_empty u
    | (o, i) :: tl ->
      let hd = if M.ptr_field w.M.maj o i then yword w.M.yng (M.field w.M.maj o i) else Seq.empty in
      FStar.Seq.Properties.lemma_mem_append hd (yrem w.M.maj w.M.yng tl);
      if Seq.mem u hd then begin
        mem_empty u;
        let v = M.field w.M.maj o i in
        let lv (a y': nat) : Lemma (v == M.VPtr (M.Young a) /\ M.resolve w.M.yng a == Some y' ==> M.minor_live w y')
          = if FStar.IndefiniteDescription.strong_excluded_middle (v == M.VPtr (M.Young a) /\ M.resolve w.M.yng a == Some y')
            then begin
              let l : M.mlive w y' = M.LRem y' o i a () in
              assert (M.minor_live w y')
            end in
        FStar.Classical.forall_intro_2 lv;
        yword_ok w v u
      end
      else yrem_ok w tl u
#pop-options

/// **Every root word is a young pointer to a live block.**
let roots_ok (w: M.world) (u: U64.t)
  : Lemma (requires Seq.mem u (roots_of w)) (ensures root_ok w u)
  = FStar.Seq.Properties.lemma_mem_append (yroots w.M.yng w.M.roots) (yrem w.M.maj w.M.yng w.M.rem);
    if Seq.mem u (yroots w.M.yng w.M.roots) then yroots_ok w w.M.roots u
    else yrem_ok w w.M.rem u

/// ---------------------------------------------------------------------------
/// What `PromoteRun` asks
/// ---------------------------------------------------------------------------

let a1_lt (a: nat) : Lemma (requires 8 * a + 16 <= minor_heap_size) (ensures a + 1 < ywords)
  = FStar.Math.Lemmas.lemma_div_le (8 * (a + 1) + 8) minor_heap_size 8;
    FStar.Math.Lemmas.cancel_mul_div (a + 2) 8

let yof_v (o: nat) : Lemma (requires 8 * o + 8 < pow2 64) (ensures Q.yof (PC.yobj o) == o) = ()

/// One root is justified.
#push-options "--z3rlimit 40"
let root_just (w: M.world) (ms: minor_state) (u: U64.t)
  : Lemma (requires Y.yrepr w.M.yng ms /\ M.young_ok w.M.yng /\ root_ok w u)
          (ensures PR.justified ms (live w ms) u)
  = let a = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun a -> exists (o: nat). 8 * a + 16 <= minor_heap_size /\ U64.v u == 8 * a + 8 /\
                                    M.resolve w.M.yng a == Some o /\ M.minor_live w o) in
    let o = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun o -> 8 * a + 16 <= minor_heap_size /\ U64.v u == 8 * a + 8 /\
                        M.resolve w.M.yng a == Some o /\ M.minor_live w o) in
    a1_lt a;
    Y.msz ();
    U64.v_inj u (U64.uint_to_t (8 * a + 8));
    Y.young_resolve w.M.yng ms a o;
    GC.Spec.Top.ToyMark.resolve_resolves w.M.yng a o;
    PC.young_obj w.M.yng ms o;
    yof_v o
#pop-options

/// **The roots are justified.**
let roots_just (w: M.world) (ms: minor_state)
  : Lemma (requires Y.yrepr w.M.yng ms /\ M.young_ok w.M.yng)
          (ensures forall (i: nat). i < Seq.length (roots_of w) ==> PR.justified ms (live w ms) (Seq.index (roots_of w) i))
  = let one (i: nat) : Lemma (i < Seq.length (roots_of w) ==> PR.justified ms (live w ms) (Seq.index (roots_of w) i))
      = if i < Seq.length (roots_of w) then begin
          GC.Spec.Top.ByteMark.mem_of_index (roots_of w) i;
          roots_ok w (Seq.index (roots_of w) i);
          root_just w ms (Seq.index (roots_of w) i)
        end in
    FStar.Classical.forall_intro one

/// A young block's object leaves room for a field.
let block_room (y: M.mheap) (o: nat)
  : Lemma (requires M.young_ok y /\ M.is_block y o /\ y.M.size == ywords) (ensures 8 * o + 16 <= minor_heap_size)
  = assert_norm (minor_heap_size % 8 == 0)

/// The word of a young pointer.
let young_word (a: nat)
  : Lemma (requires 8 * a + 16 <= minor_heap_size)
          (ensures (Y.msz (); absv (U64.uint_to_t (8 * a + 8)) == M.VPtr (M.Young a)))
  = Y.msz ();
    GC.Gen.Base.zero_addr_above_minor ();
    base_facts ()

let plain_obj (y: M.mheap) (ms: minor_state) (f: U64.t)
  : Lemma (requires Y.yrepr y ms /\ M.young_ok y /\ Seq.mem f (minor_objects ms))
          (ensures (let a = (U64.v f - 8) / 8 in
                    U64.v f >= 8 /\ U64.v f == 8 * a + 8 /\ 8 * a + 16 <= minor_heap_size /\
                    f == U64.uint_to_t (8 * a + 8)))
  = Q.obj_young y ms f;
    let o = Q.yof f in
    PC.yobj_v o 0;
    assert (U64.v f == 8 * o + 8);
    FStar.Math.Lemmas.cancel_mul_div o 8;
    assert ((U64.v f - 8) / 8 == o);
    Y.yrepr_elim y ms;
    block_room y o

/// A field word whose resolution is an object is a young pointer.
let field_young (y: M.mheap) (ms: minor_state) (f: U64.t)
  : Lemma (requires Y.yrepr y ms /\ M.young_ok y /\ Seq.mem (resolve_minor ms f) (minor_objects ms))
          (ensures (let a = (U64.v f - 8) / 8 in
                    U64.v f >= 8 /\ U64.v f == 8 * a + 8 /\ 8 * a + 16 <= minor_heap_size /\
                    f == U64.uint_to_t (8 * a + 8) /\ absv f == M.VPtr (M.Young a)))
  = if is_infix_in_minor ms f then begin
      YI.addr_facts ms f;
      young_word ((U64.v f - 8) / 8)
    end
    else begin
      resolve_minor_non_infix ms f;
      plain_obj y ms f;
      young_word ((U64.v f - 8) / 8)
    end

/// One field of a live object is justified.
#push-options "--z3rlimit 40"
let field_just (w: M.world) (ms: minor_state) (x: U64.t) (i: nat)
  : Lemma (requires Y.yrepr w.M.yng ms /\ M.young_ok w.M.yng /\ T.young_follow_ok w.M.yng /\
                    live w ms x /\ i < minor_scan_wosize ms x)
          (ensures PR.justified ms (live w ms) (to_minor_offset (minor_read_field ms x i)))
  = let y = w.M.yng in
    Q.obj_young y ms x;
    let o = Q.yof x in
    PC.young_obj y ms o;
    minor_scan_wosize_cases ms x;
    let f = minor_read_field ms x i in
    tmo_id f;
    PC.young_field y ms o i;
    let r = resolve_minor ms f in
    if Seq.mem r (minor_objects ms) && minor_wosize ms r > 0 then begin
      field_young y ms f;
      let a = (U64.v f - 8) / 8 in
      assert (M.ptr_field y o i);
      assert (M.field y o i == M.VPtr (M.Young a));
      YI.young_resolve_back y ms a;
      assert (M.young_edge y o (Q.yof r));
      let l : M.mlive w o = FStar.IndefiniteDescription.indefinite_description_ghost (M.mlive w o) (fun _ -> True) in
      let l' : M.mlive w (Q.yof r) = M.LStep o (Q.yof r) l () in
      assert (M.minor_live w (Q.yof r))
    end
#pop-options

/// **Liveness is closed under the fields the scan reads.**
let live_closed (w: M.world) (ms: minor_state)
  : Lemma (requires Y.yrepr w.M.yng ms /\ M.young_ok w.M.yng /\ T.young_follow_ok w.M.yng)
          (ensures PR.live_ok ms (live w ms))
  = let one (x: U64.t) (i: nat)
      : Lemma (live w ms x /\ Seq.mem x (minor_objects ms) /\ i < minor_scan_wosize ms x ==>
               PR.justified ms (live w ms) (to_minor_offset (minor_read_field ms x i)))
      = if FStar.IndefiniteDescription.strong_excluded_middle (live w ms x /\ i < minor_scan_wosize ms x)
        then field_just w ms x i in
    FStar.Classical.forall_intro_2 one

/// ---------------------------------------------------------------------------
/// What the promotion follows, it follows safely (design doc §12)
/// ---------------------------------------------------------------------------

/// One field of a nursery object.
#push-options "--z3rlimit 40"
let field_follow (y: M.mheap) (ms: minor_state) (x: U64.t) (i: nat)
  : Lemma (requires Y.yrepr y ms /\ M.young_ok y /\ T.young_follow_ok y /\
                    Seq.mem x (minor_objects ms) /\ i < minor_scan_wosize ms x)
          (ensures F.follow_ok ms (to_minor_offset (minor_read_field ms x i)))
  = Q.obj_young y ms x;
    let o = Q.yof x in
    PC.young_obj y ms o;
    minor_scan_wosize_cases ms x;
    let f = minor_read_field ms x i in
    tmo_id f;
    PC.young_field y ms o i;
    if is_infix_in_minor ms f then begin
      YI.addr_facts ms f;
      let a = (U64.v f - 8) / 8 in
      young_word a;
      assert (M.ptr_field y o i);
      assert (M.field y o i == M.VPtr (M.Young a));
      YI.follow_one y ms f
    end
#pop-options

/// **The nursery's fields are followed safely.**
let fields_follow_of (y: M.mheap) (ms: minor_state)
  : Lemma (requires Y.yrepr y ms /\ M.young_ok y /\ T.young_follow_ok y) (ensures F.fields_follow ms)
  = F.fields_follow_intro ms (fun x i -> field_follow y ms x i)

let div_back (a: nat) (r: nat) : Lemma (requires r == 8 * a + 8) (ensures (r - 8) / 8 == a)
  = FStar.Math.Lemmas.cancel_mul_div a 8

/// A root word: the model resolves it.
let root_follow (w: M.world) (ms: minor_state) (r: U64.t)
  : Lemma (requires Y.yrepr w.M.yng ms /\ M.young_ok w.M.yng /\ root_ok w r) (ensures F.follow_ok ms r)
  = eliminate exists (a o: nat). 8 * a + 16 <= minor_heap_size /\ U64.v r == 8 * a + 8 /\
                                M.resolve w.M.yng a == Some o /\ M.minor_live w o
    with begin
      div_back a (U64.v r);
      YI.follow_one w.M.yng ms r
    end

/// **The roots are followed safely.**
let roots_follow_of (w: M.world) (ms: minor_state)
  : Lemma (requires Y.yrepr w.M.yng ms /\ M.young_ok w.M.yng) (ensures F.roots_follow ms (roots_of w))
  = let one (i: nat) : Lemma (i < Seq.length (roots_of w) ==> F.follow_ok ms (Seq.index (roots_of w) i))
      = if i < Seq.length (roots_of w) then begin
          GC.Spec.Top.ByteMark.mem_of_index (roots_of w) i;
          roots_ok w (Seq.index (roots_of w) i);
          root_follow w ms (Seq.index (roots_of w) i)
        end in
    FStar.Classical.forall_intro one
