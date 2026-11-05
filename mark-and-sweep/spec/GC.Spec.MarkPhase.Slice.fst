module GC.Spec.MarkPhase.Slice

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module HG = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module MP = GC.Spec.MarkPhase
module MM = GC.Spec.MarkPhase.Mutator
module SweepInv = GC.Spec.SweepInv
module HM = GC.Spec.HeapModel

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

/// ---------------------------------------------------------------------------
/// Sequences of moves
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let moves_nil (g: heap) : Lemma (moves g [] g) = ()

let moves_cons (g h g': heap) (t: list heap)
  : Lemma (moves g (h :: t) g' <==> mark_move g h /\ moves h t g') = ()

let rec moves_append (g1 g2 g3: heap) (l1 l2: list heap)
  : Lemma (requires moves g1 l1 g2 /\ moves g2 l2 g3)
          (ensures moves g1 (FStar.List.Tot.append l1 l2) g3)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | h :: t -> moves_append h g2 g3 t l2

let rec moves_ind (p: heap -> prop)
  (step: (g: heap) -> (g': heap) -> Lemma (requires p g /\ mark_move g g') (ensures p g'))
  (g: heap) (l: list heap) (g': heap)
  : Lemma (requires p g /\ moves g l g') (ensures p g') (decreases l)
  = match l with
    | [] -> ()
    | h :: t -> step g h; moves_ind p step h t g'
#pop-options

let mark_steps_refl g = moves_nil g; assert (moves g [] g)

let mark_steps_trans g1 g2 g3 =
  eliminate exists (l1: list heap). moves g1 l1 g2
  with begin
    eliminate exists (l2: list heap). moves g2 l2 g3
    with moves_append g1 g2 g3 l1 l2
  end

let mark_steps_move g g' =
  moves_nil g'; moves_cons g g' g' [];
  assert (moves g [g'] g')

let mark_steps_snoc g1 g2 g3 =
  mark_steps_move g2 g3; mark_steps_trans g1 g2 g3

let mark_steps_ind p step g g' =
  eliminate exists (l: list heap). moves g l g'
  with moves_ind p step g l g'

/// ---------------------------------------------------------------------------
/// Colour changes
/// ---------------------------------------------------------------------------

/// A colour change of `o` keeps the colours of every other block.
let cc_colours (o y: obj_addr) (g: heap) (c: color)
  : Lemma (requires o <> y)
          (ensures (let g' = set_object_color o g c in
                    (is_black y g' <==> is_black y g) /\ (is_white y g' <==> is_white y g) /\
                    (is_gray y g' <==> is_gray y g) /\ (is_blue y g' <==> is_blue y g)))
  = let g' = set_object_color o g c in
    color_change_preserves_other_color o y g c;
    is_black_iff y g; is_black_iff y g';
    is_white_iff y g; is_white_iff y g';
    is_gray_iff y g; is_gray_iff y g';
    is_blue_iff y g; is_blue_iff y g'

/// The colours of a greyed block and of a blackened one.
let gray_colours (t: obj_addr) (g: heap)
  : Lemma (is_gray t (makeGray t g) /\ ~(is_white t (makeGray t g)) /\
           ~(is_black t (makeGray t g)) /\ ~(is_blue t (makeGray t g)))
  = makeGray_is_gray t g; colors_exhaustive_and_exclusive t (makeGray t g)

let black_colours (t: obj_addr) (g: heap)
  : Lemma (is_black t (makeBlack t g) /\ ~(is_white t (makeBlack t g)) /\
           ~(is_gray t (makeBlack t g)) /\ ~(is_blue t (makeBlack t g)))
  = makeBlack_is_black t g; colors_exhaustive_and_exclusive t (makeBlack t g)

/// ---------------------------------------------------------------------------
/// Scanning a field
/// ---------------------------------------------------------------------------

/// A pointer field of a block on the walk points at its value.
let field_points_to (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\
                    U64.v k <= U64.v (wosize_of_object x g) /\ is_pointer (HG.get_field g x k))
          (ensures points_to g x (HG.get_field g x k))
  = let wz = wosize_of_object x g in
    wosize_of_object_bound x g;
    hd_address_spec x;
    FStar.Math.Lemmas.pow2_lt_compat 61 54;
    wf_object_size_bound g x;
    HG.get_field_addr_eq g x k;
    field_read_implies_exists_pointing g x wz (U64.sub k 1UL) (HG.get_field g x k)

/// The target of a pointer field of a scan target is on the walk.
let field_target_mem (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    ~(is_no_scan x g) /\
                    U64.v k <= U64.v (wosize_of_object x g) /\ is_pointer (HG.get_field g x k))
          (ensures Seq.mem (resolve_object (HG.get_field g x k) g) (objects zero_addr g))
  = field_points_to g x k;
    points_to_target_not_blue g x (HG.get_field g x k)

let scan_target_not_blue (g: heap) (x: obj_addr)
  : Lemma (requires is_gray x g) (ensures ~(is_blue x g))
  = colors_exhaustive_and_exclusive x g

let scan_field_is_grey g x k =
  let v = HG.get_field g x k in
  scan_target_not_blue g x;
  if is_pointer v then field_target_mem g x k

let scan_field_dark g x k =
  let v = HG.get_field g x k in
  scan_target_not_blue g x;
  if is_pointer v && is_white (resolve_object v g) g then begin
    field_target_mem g x k;
    let t = resolve_object v g in
    makeGray_eq t g;
    Mark.color_preserves_get_field t x g Header.Gray k;
    color_change_preserves_resolve t v g Header.Gray;
    gray_colours t g
  end

/// ---------------------------------------------------------------------------
/// Blackening
/// ---------------------------------------------------------------------------

/// `push_children` changes nothing when every field it looks at is dark.
#push-options "--fuel 1"
let rec push_children_dark (g: heap) (st: seq obj_addr) (obj: obj_addr)
    (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires fields_dark g obj (U64.v i) (U64.v ws))
          (ensures fst (Mark.push_children g st obj i ws) == g)
          (decreases (U64.v ws - U64.v i))
  = if U64.v i > U64.v ws then ()
    else begin
      assert (field_dark g obj i);
      if U64.v i < U64.v ws then
        push_children_dark g st obj (U64.add i 1UL) ws
    end
#pop-options

/// Blackening `x` keeps the fields of `x` dark.
let black_fields_dark (g: heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires well_formed_heap g /\ Seq.mem x (objects zero_addr g) /\
                    U64.v k <= U64.v (wosize_of_object x g) /\ field_dark g x k)
          (ensures field_dark (makeBlack x g) x k)
  = let v = HG.get_field g x k in
    makeBlack_eq x g;
    Mark.color_preserves_get_field x x g Header.Black k;
    if is_pointer v then begin
      color_change_preserves_resolve x v g Header.Black;
      let t = resolve_object v g in
      if t = x then black_colours x g
      else cc_colours x t g Header.Black
    end

let black_move_is_step g x =
  if is_no_scan x g then ()
  else begin
    let ws = wosize_of_object x g in
    let g1 = makeBlack x g in
    introduce forall (k: U64.t{U64.v k >= 1}). 1 <= U64.v k /\ U64.v k <= U64.v ws ==> field_dark g1 x k
    with introduce _ ==> _ with black_fields_dark g x k;
    push_children_dark g1 Seq.empty x 1UL ws
  end

/// ---------------------------------------------------------------------------
/// The marking invariant
/// ---------------------------------------------------------------------------

let grey_move_inv (g g': heap) (held: obj_addr -> prop)
  : Lemma (requires MP.marking_inv g held /\ grey_move g g') (ensures MP.marking_inv g' held)
  = eliminate exists (x: obj_addr) (k: U64.t{U64.v k >= 1}).
      scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g) /\ g' == scan_field g x k
    with MM.darken_inv g held (HG.get_field g x k)

let black_move_inv (g g': heap) (held: obj_addr -> prop)
  : Lemma (requires MP.marking_inv g held /\ black_move g g') (ensures MP.marking_inv g' held)
  = eliminate exists (x: obj_addr).
      Seq.mem x (objects zero_addr g) /\ is_gray x g /\
      (is_no_scan x g \/ fields_dark g x 1 (U64.v (wosize_of_object x g))) /\
      g' == makeBlack x g
    with begin
      black_move_is_step g x;
      MP.marking_inv_step g held x
    end

let mark_move_inv g g' held =
  FStar.Classical.move_requires (grey_move_inv g g') held;
  FStar.Classical.move_requires (black_move_inv g g') held

let mark_steps_inv g g' held =
  let p (h: heap) : prop = MP.marking_inv h held in
  let step (h h': heap) : Lemma (requires p h /\ mark_move h h') (ensures p h') =
    mark_move_inv h h' held
  in
  mark_steps_ind p step g g'

/// ---------------------------------------------------------------------------
/// Darker
/// ---------------------------------------------------------------------------

let darker_refl g = ()

let darker_trans g1 g2 g3 = ()

/// The colour change of a move: a white block greyed or a grey one blackened.
let cc_move (g: heap) (t: obj_addr) (c: color) : prop =
  well_formed_heap g /\ Seq.mem t (objects zero_addr g) /\
  ((c == Header.Gray /\ is_white t g) \/ (c == Header.Black /\ is_gray t g))

let cc_move_set (g: heap) (t: obj_addr) (c: color)
  : Lemma (requires cc_move g t c)
          (ensures (let g' = set_object_color t g c in
                    (c == Header.Gray ==> g' == makeGray t g) /\
                    (c == Header.Black ==> g' == makeBlack t g) /\
                    ~(is_blue t g)))
  = makeGray_eq t g; makeBlack_eq t g; colors_exhaustive_and_exclusive t g

let cc_move_header (g: heap) (t: obj_addr) (c: color) (y: obj_addr)
  : Lemma (requires cc_move g t c /\ Seq.mem y (objects zero_addr g))
          (ensures (let g' = set_object_color t g c in
                    wosize_of_object y g' == wosize_of_object y g /\
                    is_no_scan y g' == is_no_scan y g /\
                    (is_blue y g' <==> is_blue y g) /\
                    (is_white y g' ==> is_white y g) /\
                    (is_gray y g ==> is_gray y g' \/ is_black y g') /\
                    (is_black y g ==> is_black y g')))
  = cc_move_set g t c;
    color_change_preserves_wosize_any t y g c;
    colors_exhaustive_and_exclusive y g;
    if y = t then begin
      color_preserves_is_no_scan t g c;
      gray_colours t g; black_colours t g
    end else begin
      color_change_preserves_other_is_no_scan t y g c;
      cc_colours t y g c
    end

let cc_move_field (g: heap) (t: obj_addr) (c: color) (y: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires cc_move g t c /\ Seq.mem y (objects zero_addr g) /\
                    U64.v k <= U64.v (wosize_of_object y g))
          (ensures HG.get_field (set_object_color t g c) y k == HG.get_field g y k)
  = Mark.color_preserves_get_field t y g c k

let cc_move_darker (g: heap) (t: obj_addr) (c: color)
  : Lemma (requires cc_move g t c) (ensures darker g (set_object_color t g c))
  = let g' = set_object_color t g c in
    cc_move_set g t c;
    Mark.color_change_preserves_wf g t c;
    color_change_preserves_objects g t c;
    FStar.Classical.move_requires (SweepInv.color_change_preserves_density t g) c;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (cc_move_header g t c));
    introduce forall (y: obj_addr) (k: U64.t{U64.v k >= 1}).
      Seq.mem y (objects zero_addr g) /\ U64.v k <= U64.v (wosize_of_object y g) ==>
      HG.get_field g' y k == HG.get_field g y k
    with introduce _ ==> _ with cc_move_field g t c y k;
    introduce forall (v: obj_addr). resolve_object v g' == resolve_object v g
    with color_change_preserves_resolve t v g c

let grey_move_darker (g g': heap)
  : Lemma (requires well_formed_heap g /\ grey_move g g') (ensures darker g g')
  = eliminate exists (x: obj_addr) (k: U64.t{U64.v k >= 1}).
      scan_target g x /\ U64.v k <= U64.v (wosize_of_object x g) /\ g' == scan_field g x k
    with begin
      scan_field_is_grey g x k;
      let v = HG.get_field g x k in
      if is_pointer v && is_white (resolve_object v g) g then begin
        makeGray_eq (resolve_object v g) g;
        cc_move_darker g (resolve_object v g) Header.Gray
      end else darker_refl g
    end

let black_move_darker (g g': heap)
  : Lemma (requires well_formed_heap g /\ black_move g g') (ensures darker g g')
  = eliminate exists (x: obj_addr).
      Seq.mem x (objects zero_addr g) /\ is_gray x g /\
      (is_no_scan x g \/ fields_dark g x 1 (U64.v (wosize_of_object x g))) /\
      g' == makeBlack x g
    with begin
      makeBlack_eq x g;
      cc_move_darker g x Header.Black
    end

let mark_move_darker g g' =
  FStar.Classical.move_requires (grey_move_darker g) g';
  FStar.Classical.move_requires (black_move_darker g) g'

let mark_steps_darker g g' =
  let p (h: heap) : prop = darker g h in
  let step (h h': heap) : Lemma (requires p h /\ mark_move h h') (ensures p h') =
    mark_move_darker h h';
    darker_trans g h h'
  in
  darker_refl g;
  mark_steps_ind p step g g'

/// Dark fields stay dark: the fields and their resolutions are kept, and the
/// target of a pointer field of a non-free scannable block is on the walk,
/// where nothing becomes white.
let darker_field_dark (g g': heap) (x: obj_addr) (k: U64.t{U64.v k >= 1})
  : Lemma (requires darker g g' /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\
                    ~(is_no_scan x g) /\
                    U64.v k <= U64.v (wosize_of_object x g) /\ field_dark g x k)
          (ensures field_dark g' x k)
  = let v = HG.get_field g' x k in
    assert (v == HG.get_field g x k);
    if is_pointer v then begin
      field_target_mem g' x k;
      assert (resolve_object v g' == resolve_object v g)
    end

let darker_fields_dark g g' x lo hi =
  introduce forall (k: U64.t{U64.v k >= 1}). lo <= U64.v k /\ U64.v k <= hi ==> field_dark g' x k
  with introduce _ ==> _ with darker_field_dark g g' x k

/// ---------------------------------------------------------------------------
/// The measure
/// ---------------------------------------------------------------------------

let w1 (g: heap) (y: obj_addr) : GTot nat =
  if is_white y g then 2 else if is_gray y g then 1 else 0

let rec weight_in (g: heap) (s: seq obj_addr) : GTot nat (decreases Seq.length s) =
  if Seq.length s = 0 then 0 else w1 g (Seq.head s) + weight_in g (Seq.tail s)

let mark_weight g = weight_in g (objects zero_addr g)

/// No duplicates.
let nodup (s: seq obj_addr) : prop = GC.Spec.Graph.is_vertex_set (HG.coerce_to_vertex_list s)

#push-options "--fuel 1"
let nodup_tail (s: seq obj_addr)
  : Lemma (requires nodup s /\ Seq.length s > 0)
          (ensures nodup (Seq.tail s) /\ ~(Seq.mem (Seq.head s) (Seq.tail s)))
  = let c = HG.coerce_to_vertex_list (Seq.tail s) in
    HG.coerce_mem_lemma (Seq.tail s) (Seq.head s);
    assert (HG.coerce_to_vertex_list s == Seq.cons (Seq.head s) c);
    Seq.lemma_eq_elim (Seq.tail (Seq.cons (Seq.head s) c)) c;
    assert (Seq.head (Seq.cons (Seq.head s) c) == Seq.head s)

/// Changing the term of one element `t` of a sequence without duplicates.
let rec weight_in_change (g g': heap) (s: seq obj_addr) (t: obj_addr)
  : Lemma (requires nodup s /\ Seq.mem t s /\
                    (forall (y: obj_addr). Seq.mem y s /\ y <> t ==> w1 g' y == w1 g y))
          (ensures weight_in g' s + w1 g t == weight_in g s + w1 g' t)
          (decreases Seq.length s)
  = nodup_tail s;
    Seq.mem_cons (Seq.head s) (Seq.tail s);
    assert (Seq.equal s (Seq.cons (Seq.head s) (Seq.tail s)));
    if Seq.head s = t then weight_in_same g g' (Seq.tail s) t
    else weight_in_change g g' (Seq.tail s) t

and weight_in_same (g g': heap) (s: seq obj_addr) (t: obj_addr)
  : Lemma (requires ~(Seq.mem t s) /\
                    (forall (y: obj_addr). Seq.mem y s /\ y <> t ==> w1 g' y == w1 g y))
          (ensures weight_in g' s == weight_in g s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      Seq.mem_cons (Seq.head s) (Seq.tail s);
      assert (Seq.equal s (Seq.cons (Seq.head s) (Seq.tail s)));
      weight_in_same g g' (Seq.tail s) t
    end
#pop-options

/// A colour change of `t` changes the weight by the change of its term.
let weight_cc (g: heap) (t: obj_addr) (c: color)
  : Lemma (requires Seq.mem t (objects zero_addr g))
          (ensures mark_weight (set_object_color t g c) + w1 g t ==
                   mark_weight g + w1 (set_object_color t g c) t)
  = let g' = set_object_color t g c in
    color_change_preserves_objects g t c;
    HM.objects_is_vertex_set g;
    let aux (y: obj_addr) : Lemma (requires y <> t) (ensures w1 g' y == w1 g y) =
      cc_colours t y g c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    weight_in_change g g' (objects zero_addr g) t

let weight_grey g t =
  makeGray_eq t g;
  weight_cc g t Header.Gray;
  gray_colours t g

let weight_black g x =
  makeBlack_eq x g;
  weight_cc g x Header.Black;
  black_colours x g;
  colors_exhaustive_and_exclusive x g

let scan_field_weight g x k =
  scan_field_is_grey g x k;
  let v = HG.get_field g x k in
  if is_pointer v && is_white (resolve_object v g) g then weight_grey g (resolve_object v g)
