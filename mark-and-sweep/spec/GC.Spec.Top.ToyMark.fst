/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ToyMark - a toy mark and write barrier meeting the contracts
/// ---------------------------------------------------------------------------
///
/// Satisfiability of `mark_ok` and `barrier_ok` (GC.Spec.Top.Iface).
///
/// The mark's state is the scan, and a move is the model's move
/// (`tmmove`); `tmstart` greys every white object in outside_refs.
/// `tmslice` (the lowest grey block's children greyed, the block
/// blackened, as a whole) is kept with its model proofs: the byte mark's
/// account of akhil's whole-object slice uses it.  The barrier greys the overwritten
/// target while marking, then stores, and remembers every field of a
/// scannable block that receives a young pointer.
///
/// Proved: `toy_mark_ok` (the start establishes the snapshot invariant; a
/// move is the model's), `tmslice_m` (the whole-object slice keeps the
/// invariant and decreases the measure),
/// `toy_barrier_ok`.

module GC.Spec.Top.ToyMark

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.IdRep
open GC.Spec.Top.ToyRep
module L = FStar.List.Tot
module Seq = FStar.Seq

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Bounded searches
/// ---------------------------------------------------------------------------

let rec exists_below (n: nat) (f: nat -> bool) : bool =
  if n = 0 then false else f (n - 1) || exists_below (n - 1) f

let rec exists_below_iff (n: nat) (f: nat -> bool)
  : Lemma (exists_below n f == true <==> (exists (i: nat). i < n /\ f i == true))
  = if n = 0 then () else exists_below_iff (n - 1) f

let points_major (h: mheap) (v: value) (x: nat) : bool =
  match v with
  | VPtr (Major a) -> resolve h a = Some x
  | _ -> false

let points_major_iff (h: mheap) (v: value) (x: nat)
  : Lemma (points_major h v x == true <==> (exists (a: nat). v == VPtr (Major a) /\ resolve h a == Some x))
  = match v with
    | VPtr (Major a) -> ()
    | _ -> ()

let rec root_b (h: mheap) (rs: list value) (x: nat) : bool =
  match rs with
  | [] -> false
  | v :: tl -> points_major h v x || root_b h tl x

let rec root_b_iff (h: mheap) (rs: list value) (x: nat)
  : Lemma (root_b h rs x == true <==> (exists (a: nat). L.memP (VPtr (Major a)) rs /\ resolve h a == Some x))
  = match rs with
    | [] -> ()
    | v :: tl ->
      root_b_iff h tl x;
      match v with
      | VPtr (Major a) -> if resolve h a = Some x then assert (L.memP (VPtr (Major a)) rs)
      | _ -> ()

let young_field_b (w: world) (x: nat) (y: nat) : bool =
  exists_below (wz_of w.yng y) (fun i -> ptr_field w.yng y i && points_major w.maj (field w.yng y i) x)

let young_b (w: world) (x: nat) : bool =
  exists_below w.yng.size (young_field_b w x)

let young_b_iff (w: world) (x: nat)
  : Lemma (young_b w x == true <==> young_ref w x)
  = exists_below_iff w.yng.size (young_field_b w x);
    let aux (y: nat) : Lemma (young_field_b w x y == true <==>
                              (exists (i a: nat). ptr_field w.yng y i /\ field w.yng y i == VPtr (Major a) /\
                                                  resolve w.maj a == Some x))
      = exists_below_iff (wz_of w.yng y)
          (fun i -> ptr_field w.yng y i && points_major w.maj (field w.yng y i) x);
        let pm (i: nat) : Lemma (points_major w.maj (field w.yng y i) x == true <==>
                                 (exists (a: nat). field w.yng y i == VPtr (Major a) /\ resolve w.maj a == Some x))
          = points_major_iff w.maj (field w.yng y i) x in
        FStar.Classical.forall_intro pm in
    FStar.Classical.forall_intro aux

let outside_b (w: world) (x: nat) : bool = root_b w.maj w.roots x || young_b w x

let outside_b_iff (w: world) (x: nat) : Lemma (outside_b w x == true <==> outside_ref w x)
  = root_b_iff w.maj w.roots x; young_b_iff w x

let edge_b (h: mheap) (g x: nat) : bool =
  exists_below (wz_of h g) (fun i -> ptr_field h g i && points_major h (field h g i) x)

let edge_b_iff (h: mheap) (g x: nat) : Lemma (edge_b h g x == true <==> major_edge h g x)
  = exists_below_iff (wz_of h g) (fun i -> ptr_field h g i && points_major h (field h g i) x);
    let pm (i: nat) : Lemma (points_major h (field h g i) x == true <==>
                             (exists (a: nat). field h g i == VPtr (Major a) /\ resolve h a == Some x))
      = points_major_iff h (field h g i) x in
    FStar.Classical.forall_intro pm

let rec find_grey (h: mheap) (n: nat) : option nat =
  if n = 0 then None
  else match find_grey h (n - 1) with
    | Some g -> Some g
    | None -> if is_block h (n - 1) && col_of h (n - 1) = Grey then Some (n - 1) else None

let rec find_grey_spec (h: mheap) (n: nat)
  : Lemma (match find_grey h n with
           | Some g -> is_block h g /\ col_of h g == Grey
           | None -> (forall (o: nat). o < n /\ is_block h o ==> col_of h o <> Grey))
  = if n = 0 then () else find_grey_spec h (n - 1)

/// ---------------------------------------------------------------------------
/// The mark
/// ---------------------------------------------------------------------------

let resolve_resolves (h: mheap) (a o: nat) : Lemma (resolve h a == Some o ==> is_block h o) = ()

let tmstart (w: world) : GTot mheap =
  { w.maj with hd = (fun (x: nat) ->
      match w.maj.hd x with
      | Some hx -> if outside_b w x && hx.col = White then Some ({ hx with col = Grey }) else Some hx
      | None -> None) }

let tmslice_with (h: mheap) (g: nat) : mheap =
  { h with hd = (fun (x: nat) ->
      match h.hd x with
      | Some hx ->
        if x = g then Some ({ hx with col = Black })
        else if hx.col = White && edge_b h g x then Some ({ hx with col = Grey })
        else Some hx
      | None -> None) }

let tmslice (h: mheap) : GTot mheap =
  match find_grey h h.size with
  | None -> h
  | Some g -> tmslice_with h g

let tmstart_c (cw: cworld mheap mheap) : GTot mheap = tmstart (tview cw)

/// A move: the model's move itself; the state is the scan.
let tmmove (h: mheap) (sc: scan) (mv: move) : mheap & scan = (move_heap h sc mv, move_scan sc mv)

let tmark : mark mheap mheap = {
  mstate = scan; mscan = (fun sc -> sc); mnone = None; mstart = tmstart_c; mmove = tmmove }

/// Recolouring keeps resolve, pointer fields and edges.
let colours_only_edges (h h': mheap)
  : Lemma (requires colours_only h h')
          (ensures (forall (a: nat). resolve h' a == resolve h a) /\
                   (forall (o i: nat). ptr_field h' o i == ptr_field h o i /\ field h' o i == field h o i) /\
                   (forall (o o': nat). major_edge h' o o' <==> major_edge h o o'))
  = ()

let start_colour (w: world) (x: nat)
  : Lemma (col_of (tmstart w) x ==
           (if Some? (w.maj.hd x) && outside_b w x && col_of w.maj x = White then Grey else col_of w.maj x))
  = ()

/// Only blocks change colour, and they darken (G50, G52).
let start_darken1 (w: world) (x: nat)
  : Lemma (col_of (tmstart w) x =!= col_of w.maj x ==> is_block w.maj x /\ dark (col_of (tmstart w) x))
  = start_colour w x;
    if outside_b w x then begin
      outside_b_iff w x;
      FStar.Classical.forall_intro (resolve_resolves w.maj x)
    end

let start_darken (w: world) : Lemma (darken_only w.maj (tmstart w))
  = FStar.Classical.forall_intro (start_darken1 w)

let tmstart_colours_only (w: world) : Lemma (colours_only w.maj (tmstart w))
  = let h' = tmstart w in
    let a (o: nat) : Lemma (is_block h' o == is_block w.maj o /\ wz_of h' o == wz_of w.maj o /\
                            tag_of h' o == tag_of w.maj o) = () in
    FStar.Classical.forall_intro a

/// Every reachable object is grey, or reached from a grey one through white
/// ones, right after the start.
let rec start_path (w: world) (o: nat) (r: reach w o)
  : Ghost (wpath (tmstart w) o)
          (requires well_formed w.maj /\ no_dark w.maj /\ (forall (x: nat). reachable w x ==> is_block w.maj x /\ col_of w.maj x == White))
          (ensures fun _ -> True)
          (decreases r)
  = let h' = tmstart w in
    assert (reachable w o);
    start_colour w o;
    match r with
    | RBase _ _ ->
      outside_b_iff w o;
      WGrey o ()
    | RStep p _ r' _ ->
      if col_of h' o = Grey then WGrey o ()
      else begin
        let pp = start_path w p r' in
        tmstart_colours_only w;
        colours_only_edges w.maj h';
        WStep p o pp ()
      end

let tmstart_m (w: world) : Lemma (mark_start_pre w ==> mark_start_post w (tmstart w))
  = let pre () : Lemma (requires well_formed w.maj /\ no_dark w.maj /\
                                 (forall (o: nat). reachable w o ==> is_block w.maj o /\ col_of w.maj o == White))
                       (ensures (let h' = tmstart w in
                                 colours_only w.maj h' /\ darken_only w.maj h' /\
                                 (forall (o: nat). outside_ref w o ==> dark (col_of h' o)) /\
                                 tricolour h' (reachable w) (fun _ -> False)))
      = let h' = tmstart w in
        tmstart_colours_only w;
        FStar.Classical.forall_intro (start_colour w);
        let c (x: nat) : Lemma ((outside_ref w x ==> dark (col_of h' x)) /\
                                (is_block h' x /\ dark (col_of h' x) ==> reachable w x))
          = start_colour w x; outside_b_iff w x;
            if outside_b w x then begin
              assert (outside_ref w x);
              let rb : reach w x = RBase x () in
              assert (reachable w x)
            end
        in
        FStar.Classical.forall_intro c;
        let t3 (o: nat) : Lemma (reachable w o /\ col_of h' o == White ==> grey_reached h' o)
          = if FStar.IndefiniteDescription.strong_excluded_middle (reachable w o) then begin
              let r = FStar.IndefiniteDescription.indefinite_description_ghost (reach w o) (fun _ -> True) in
              let p = start_path w o r in
              assert (grey_reached h' o)
            end
        in
        FStar.Classical.forall_intro t3;
        assert (forall (o: nat). reachable w o ==> is_block h' o);
        assert (forall (o: nat). is_block h' o /\ dark (col_of h' o) ==> reachable w o \/ False);
        assert (forall (o: nat). reachable w o /\ col_of h' o == White ==> grey_reached h' o);
        assert (tricolour h' (reachable w) (fun _ -> False));
        start_darken w;
        assert (darken_only w.maj h')
    in
    FStar.Classical.move_requires pre ()

let tmstart_ok (cw: cworld mheap mheap) : Lemma (mark_start_at toy_rep tmark cw)
  = toy_rep_id ();
    let w = tview cw in
    tmstart_m w;
    id_repr toy_rep (tmstart w) (tmstart w);
    assert (mark_start_m toy_rep tmark cw w);
    forall_views_id toy_rep cw (mark_start_m toy_rep tmark cw)

let tmslice_colours_only (h: mheap) (g: nat) : Lemma (colours_only h (tmslice_with h g))
  = let h' = tmslice_with h g in
    let a (o: nat) : Lemma (is_block h' o == is_block h o /\ wz_of h' o == wz_of h o /\
                            tag_of h' o == tag_of h o) = () in
    FStar.Classical.forall_intro a

/// The colours after a slice at grey `g`.
let slice_colour (h: mheap) (g x: nat)
  : Lemma (col_of (tmslice_with h g) x ==
           (if Some? (h.hd x) && x = g then Black
            else if Some? (h.hd x) && col_of h x = White && edge_b h g x then Grey
            else col_of h x))
  = ()

let slice_darken1 (h: mheap) (g x: nat)
  : Lemma (requires is_block h g)
          (ensures col_of (tmslice_with h g) x =!= col_of h x ==> is_block h x /\ dark (col_of (tmslice_with h g) x))
  = slice_colour h g x;
    if edge_b h g x then begin
      edge_b_iff h g x;
      FStar.Classical.forall_intro (resolve_resolves h x)
    end

let slice_darken (h: mheap) (g: nat) : Lemma (requires is_block h g) (ensures darken_only h (tmslice_with h g))
  = FStar.Classical.forall_intro (slice_darken1 h g)

let wpath_not_black (#h: mheap) (#x: nat) (p: wpath h x)
  : Lemma (is_block h x /\ col_of h x <> Black)
  = match p with
    | WGrey _ _ -> ()
    | WStep _ _ _ _ -> ()

let rec slice_path (h: mheap) (g: nat) (x: nat) (p: wpath h x)
  : Ghost (wpath (tmslice_with h g) x)
          (requires is_block h g /\ col_of h g == Grey /\ col_of (tmslice_with h g) x <> Black)
          (ensures fun _ -> True)
          (decreases p)
  = let h' = tmslice_with h g in
    slice_colour h g x;
    match p with
    | WGrey _ _ -> WGrey x ()
    | WStep o _ p' _ ->
      if col_of h' x = Grey then WGrey x ()
      else begin
        slice_colour h g o;
        wpath_not_black p';
        if o = g then begin
          edge_b_iff h g x;
          assert False
        end;
        let q = slice_path h g o p' in
        tmslice_colours_only h g;
        colours_only_edges h h';
        WStep o x q ()
      end

let slice_measure (h: mheap) (g: nat) (live: nat -> prop)
  : Lemma (requires is_block h g /\ col_of h g == Grey /\ live g)
          (ensures mark_decreases h (tmslice_with h g) live)
  = let h' = tmslice_with h g in
    let wsub (x: nat) : Lemma (white_live h' live x ==> white_live h live x) = slice_colour h g x in
    FStar.Classical.forall_intro wsub;
    let some_greyed : prop = exists (x: nat). white_live h live x /\ col_of h' x == Grey in
    if FStar.IndefiniteDescription.strong_excluded_middle some_greyed then begin
      let x = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun x -> white_live h live x /\ col_of h' x == Grey) in
      assert (white_live h live x /\ ~(white_live h' live x))
    end
    else begin
      let w (x: nat) : Lemma (requires ~some_greyed)
                             (ensures (white_live h' live x <==> white_live h live x) /\
                                      (grey_live h' live x ==> grey_live h live x))
        = slice_colour h g x;
          assert (~(white_live h live x /\ col_of h' x == Grey)) in
      FStar.Classical.forall_intro (FStar.Classical.move_requires w);
      slice_colour h g g;
      assert (grey_live h live g /\ ~(grey_live h' live g))
    end

/// A slice at any grey block keeps the invariant and decreases the measure.
#push-options "--z3rlimit 40"
let tmslice_with_m (h: mheap) (snap allocd: nat -> prop) (g: nat)
  : Lemma (requires mark_slice_pre snap allocd h /\ is_block h g /\ col_of h g == Grey)
          (ensures mark_slice_post snap allocd h (tmslice_with h g))
  = let live = union snap allocd in
    let h' = tmslice_with h g in
    tmslice_colours_only h g;
    slice_darken h g;
    FStar.Classical.forall_intro (slice_colour h g);
    assert (darken_only h h');
    assert (live g);
    let c (x: nat) : Lemma ((is_block h' x /\ dark (col_of h' x) ==> snap x \/ allocd x) /\
                            (allocd x ==> col_of h' x == Black) /\
                            (col_of h' x == White ==> col_of h x == White))
      = slice_colour h g x;
        if Some? (h.hd x) && x <> g && col_of h x = White && edge_b h g x then begin
          edge_b_iff h g x;
          assert (exists (o' a: nat). resolve h a == Some o' /\ live o' /\ resolve h a == Some x)
        end
    in
    FStar.Classical.forall_intro c;
    let t3 (o: nat) : Lemma (snap o /\ col_of h' o == White ==> grey_reached h' o)
      = if FStar.IndefiniteDescription.strong_excluded_middle (snap o /\ col_of h' o == White) then begin
          let p = FStar.IndefiniteDescription.indefinite_description_ghost (wpath h o) (fun _ -> True) in
          let q = slice_path h g o p in
          assert (grey_reached h' o)
        end
    in
    FStar.Classical.forall_intro t3;
    assert (tricolour h' snap allocd);
    slice_measure h g live
#pop-options

let tmslice_m (h: mheap) (snap allocd: nat -> prop)
  : Lemma (mark_slice_pre snap allocd h ==> mark_slice_post snap allocd h (tmslice h))
  = let pre () : Lemma (requires mark_slice_pre snap allocd h)
                       (ensures mark_slice_post snap allocd h (tmslice h))
      = find_grey_spec h h.size;
        let Some g = find_grey h h.size in
        assert (tmslice h == tmslice_with h g);
        tmslice_with_m h snap allocd g
    in
    FStar.Classical.move_requires pre ()

/// A move meets the contract: it is the model's move.
let tmove_ok (h: mheap) (ms: tmark.mstate) (mv: move) : Lemma (mark_move_at toy_rep tmark h ms mv)
  = toy_rep_id ();
    id_repr toy_rep (move_heap h ms mv) (move_heap h ms mv);
    forall_repr_id toy_rep h (mark_move_m toy_rep tmark h ms mv)

let toy_mark_ok () : Lemma (mark_ok toy_rep tmark)
  = FStar.Classical.forall_intro tmstart_ok;
    FStar.Classical.forall_intro_3 tmove_ok

/// ---------------------------------------------------------------------------
/// The barrier
/// ---------------------------------------------------------------------------

let rec slots (o: nat) (n: nat) : list slot =
  if n = 0 then [] else (o, n - 1) :: slots o (n - 1)

let rec slots_mem (o n i: nat) : Lemma (i < n ==> L.memP (o, i) (slots o n))
  = if n = 0 then () else slots_mem o (n - 1) i

let tbwrite (marking: bool) (h: mheap) (rem: list slot) (o i: nat) (v: value) : GTot (mheap & list slot) =
  let h1 =
    if marking then
      (match old_target h o i with
       | Some t -> if col_of h t = White then set_col h t Grey else h
       | None -> h)
    else h in
  let rem' = if young_slot h o i v then (o, i) :: rem else rem in
  (set_field h1 o i v, rem')

let tbinit (h: mheap) (rem: list slot) (o: nat) (vs: list value) : GTot (mheap & list slot) =
  (fill h o vs, L.append (slots o (L.length vs)) rem)

let tbarrier : barrier mheap = { bwrite = tbwrite; binit = tbinit }

let tbwrite_m (marking: bool) (h: mheap) (rem: list slot) (o i: nat) (v: value)
  : Lemma (let (h', rem') = tbwrite marking h rem o i v in
           write_pre o i v (toy_rep.storable v) h ==> write_post marking rem rem' o i v h h')
  = ()

let tbwrite_ok (marking: bool) (h: mheap) (rem: list slot) (o i: nat) (v: value)
  : Lemma (barrier_write_at toy_rep tbarrier marking h rem o i v)
  = tbwrite_m marking h rem o i v;
    toy_rep_id ();
    let (h', rem') = tbwrite marking h rem o i v in
    lifted_id toy_rep (write_pre o i v (toy_rep.storable v)) h h' (write_post marking rem rem' o i v)

let tbinit_ok (h: mheap) (rem: list slot) (o: nat) (vs: list value)
  : Lemma (barrier_init_at toy_rep tbarrier h rem o vs)
  = toy_rep_id ();
    id_repr toy_rep (fill h o vs) (fill h o vs);
    forall_repr_id toy_rep h (binit_m toy_rep tbarrier h rem o vs);
    let m (sl: slot) : Lemma (L.memP sl rem ==> L.memP sl (L.append (slots o (L.length vs)) rem))
      = L.append_memP (slots o (L.length vs)) rem sl in
    FStar.Classical.forall_intro m;
    let n (i: nat) : Lemma (i < L.length vs ==> L.memP (o, i) (L.append (slots o (L.length vs)) rem))
      = slots_mem o (L.length vs) i;
        L.append_memP (slots o (L.length vs)) rem (o, i) in
    FStar.Classical.forall_intro n

let toy_barrier_ok () : Lemma (barrier_ok toy_rep tbarrier)
  = let w (marking: bool) (h: mheap) (rem: list slot)
      : Lemma (forall o i v. barrier_write_at toy_rep tbarrier marking h rem o i v)
      = let w1 (o: nat) : Lemma (forall i v. barrier_write_at toy_rep tbarrier marking h rem o i v)
          = FStar.Classical.forall_intro_2 (tbwrite_ok marking h rem o) in
        FStar.Classical.forall_intro w1 in
    FStar.Classical.forall_intro_3 w;
    let i (h: mheap) (rem: list slot) : Lemma (forall o vs. barrier_init_at toy_rep tbarrier h rem o vs)
      = FStar.Classical.forall_intro_2 (tbinit_ok h rem) in
    FStar.Classical.forall_intro_2 i
