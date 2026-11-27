/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StepWrite - the program's store into a major block
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 8): `EWrite (Major o) i v`.  The barrier stores
/// `v` into field `i` of `o` and changes no other word (G49); while marking
/// it greys the overwritten field's target if it was white; it remembers a
/// young pointer it stores.  The allocator's invariant moves through
/// `inv_frame` (the stored value's target is kept, the greyed block is in
/// use), and nothing is freed.  Then:
///   - resolution is unchanged (`w_resolve`: the stored word is a field of a
///     block that is not a closure, so not an infix header), and nothing
///     new is reachable (`v` is a value the program may hold);
///   - snapshot-at-the-beginning (`w_lpath`): along a path from a live grey
///     block through white ones, each block is greyed by the barrier or
///     still reached by such a path, because the only edge the store cuts
///     leads to the block the barrier greys.

module GC.Spec.Top.StepWrite

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.StepFacts
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The barrier's guarantee, sealed
/// ---------------------------------------------------------------------------

let tgt (#c: comps) (x: config c) (o i: nat) : GTot (option nat) =
  if is_marking x.ph then old_target (mj x) o i else None

[@@"opaque_to_smt"]
let wpost (#c: comps) (x: config c) (o i: nat) (v: value) (rem': list slot) (m': mheap) : prop =
  write_post (is_marking x.ph) (vw x).rem rem' o i v (mj x) m'

let wp_hd (#c: comps) (x: config c) (o i: nat) (v: value) (rem': list slot) (m': mheap) (y: nat)
  : Lemma (requires wpost x o i v rem' m')
          (ensures m'.size == (mj x).size /\ is_block m' y == is_block (mj x) y /\
                   wz_of m' y == wz_of (mj x) y /\ tag_of m' y == tag_of (mj x) y)
  = reveal_opaque (`%wpost) (wpost #c)

let wp_body (#c: comps) (x: config c) (o i: nat) (v: value) (rem': list slot) (m': mheap) (n: nat)
  : Lemma (requires wpost x o i v rem' m') (ensures m'.body n == (if n = o + 1 + i then v else (mj x).body n))
  = reveal_opaque (`%wpost) (wpost #c)

let wp_col (#c: comps) (x: config c) (o i: nat) (v: value) (rem': list slot) (m': mheap) (y: nat)
  : Lemma (requires wpost x o i v rem' m')
          (ensures col_of m' y == (if Some y = tgt x o i && col_of (mj x) y = White then Grey else col_of (mj x) y))
  = reveal_opaque (`%wpost) (wpost #c)

let wp_rem (#c: comps) (x: config c) (o i: nat) (v: value) (rem': list slot) (m': mheap)
  : Lemma (requires wpost x o i v rem' m')
          (ensures (forall (sl: slot). L.memP sl (vw x).rem ==> L.memP sl rem') /\
                   (young_slot (mj x) o i v ==> L.memP (o, i) rem'))
  = reveal_opaque (`%wpost) (wpost #c)

/// ---------------------------------------------------------------------------
/// The step's context
/// ---------------------------------------------------------------------------

let wok (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) : prop =
  rinv x /\ mutator_ok x (EWrite (Major o) i v) /\ wpost x o i v rem' m' /\
  x'.ph == x.ph /\ x'.ast == x.ast /\ x'.w.cmaj == h' /\ x'.w.crem == rem' /\ x'.w.cyng == x.w.cyng /\
  x'.w.croots == x.w.croots /\ x'.snap == x.snap /\ x'.allocd == x.allocd /\ x'.ms == x.ms /\
  c.a.inv x.ph h' x.ast /\ (forall (y: nat). c.a.free x.ast h' y == c.a.free x.ast x.w.cmaj y)

let wnext (#c: comps) (x: config c) (rem': list slot) (m': mheap) : GTot world =
  { vw x with maj = m'; rem = rem' }

let w_basic (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m')
          (ensures well_formed (mj x) /\ well_formed m' /\ unique_cover m' /\ unique_cover (mj x) /\
                   is_block (mj x) o /\ reachable (vw x) o /\ i < wz_of (mj x) o /\
                   tag_of (mj x) o <> closure_tag /\
                   (scannable (tag_of (mj x) o) ==> value_ok (vw x) v) /\
                   (forall (y: nat). iu x' m' y == in_use_c x y))
  = reveal_opaque (`%r_heap) (r_heap #c);
    C.forall_intro (wp_hd x o i v rem' m');
    assert (forall (y n: nat). covers m' y n == covers (mj x) y n)

/// A store into field `i` of `o` leaves every other field (small context).
let field_store (m m': mheap) (o i y j: nat) (v: value)
  : Lemma (requires well_formed m /\ is_block m y /\ j < wz_of m y /\ is_block m o /\ i < wz_of m o /\
                    m'.body (y + 1 + j) == (if y + 1 + j = o + 1 + i then v else m.body (y + 1 + j)))
          (ensures m'.body (y + 1 + j) == (if y = o && j = i then v else m.body (y + 1 + j)))
  = let n = y + 1 + j in
    if n = o + 1 + i && not (y = o && j = i) then begin
      assert (covers m y n); assert (covers m o n);
      cover_unique m y o n
    end

/// Fields after the store.
let w_field (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (y j: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ is_block (mj x) y /\ j < wz_of (mj x) y)
          (ensures field m' y j == (if y = o && j = i then v else field (mj x) y j))
  = w_basic x x' o i v h' rem' m';
    let n = y + 1 + j in
    wp_body x o i v rem' m' n;
    field_store (mj x) m' o i y j v;
    assert (field m' y j == m'.body n /\ field (mj x) y j == (mj x).body n)

/// Resolution is unchanged.
let w_resolve (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (b: nat)
  : Lemma (requires wok x x' o i v h' rem' m') (ensures resolve m' b == resolve (mj x) b)
  = w_basic x x' o i v h' rem' m';
    C.forall_intro (wp_hd x o i v rem' m');
    C.forall_intro (wp_body x o i v rem' m');
    assert (covers (mj x) o (o + 1 + i));
    one_word_resolve (mj x) m' o (o + 1 + i) b

let old_target_facts (h: mheap) (o i t: nat)
  : Lemma (requires old_target h o i == Some t)
          (ensures ptr_field h o i /\ (exists (a: nat). field h o i == VPtr (Major a) /\ resolve h a == Some t))
  = match field h o i with
    | VPtr (Major a) -> assert (field h o i == VPtr (Major a) /\ resolve h a == Some t)
    | _ -> ()

/// The overwritten value's target, while marking, is reachable.
let w_tgt (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Some? (tgt x o i))
          (ensures Marking? x.ph /\ reachable (vw x) (Some?.v (tgt x o i)) /\ kept x (Some?.v (tgt x o i)))
  = let w = vw x in
    let t = Some?.v (tgt x o i) in
    w_basic x x' o i v h' rem' m';
    old_target_facts w.maj o i t;
    eliminate exists (a: nat). field w.maj o i == VPtr (Major a) /\ resolve w.maj a == Some t
    with begin reach_field w o i a t; reach_kept x w t end

/// ---------------------------------------------------------------------------
/// The allocator's invariant
/// ---------------------------------------------------------------------------

let w_rel (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires rinv x /\ mutator_ok x (EWrite (Major o) i v) /\ wpost x o i v rem' m')
          (ensures inv_frame_rel c.a x.ph x.ast x.w.cmaj (mj x) m')
  = let m = mj x in
    let w = vw x in
    reveal_opaque (`%r_heap) (r_heap #c);
    C.forall_intro (wp_hd x o i v rem' m');
    C.forall_intro (wp_body x o i v rem' m');
    let cl (y: nat) : Lemma (col_of m' y =!= col_of m y ==> in_use c.a x.ast x.w.cmaj m y /\ Marking? x.ph /\ dark (col_of m' y))
      = wp_col x o i v rem' m' y;
        if Some y = tgt x o i then begin
          old_target_facts w.maj o i y;
          eliminate exists (a: nat). field w.maj o i == VPtr (Major a) /\ resolve w.maj a == Some y
          with begin reach_field w o i a y; reach_kept x w y end
        end in
    C.forall_intro cl;
    reach_kept x w o;
    kept_live_target x w o;
    let sv () : Lemma (scannable (tag_of m o) ==> sound_value c.a x.ph x.ast x.w.cmaj m' v)
      = if scannable (tag_of m o) then
          match v with
          | VPtr (Major b) ->
            eliminate exists (t: nat). resolve m b == Some t /\ reachable w t
            with begin
              reach_kept x w t; kept_live_target x w t;
              wp_hd x o i v rem' m' t; wp_col x o i v rem' m' t;
              (* the frame's resolve: only word o+1+i changed, a field of a non-closure *)
              assert (resolve m b == Some t);
              assert (covers m o (o + 1 + i));
              one_word_resolve m m' o (o + 1 + i) b;
              assert (live_target c.a x.ph x.ast x.w.cmaj m' t)
            end
          | _ -> () in
    sv ()

/// ---------------------------------------------------------------------------
/// Reachability and the invariant's pointer parts
/// ---------------------------------------------------------------------------

let w_edge (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (y z: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ reachable (vw x) y /\ major_edge m' y z)
          (ensures reachable (vw x) z)
  = let w = vw x in
    eliminate exists (j a: nat). ptr_field m' y j /\ field m' y j == VPtr (Major a) /\ resolve m' a == Some z
    with begin
      w_basic x x' o i v h' rem' m';
      wp_hd x o i v rem' m' y;
      w_field x x' o i v h' rem' m' y j;
      w_resolve x x' o i v h' rem' m' a;
      if y = o && j = i then ()
      else reach_field w y j a z
    end

let w_outside (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ outside_ref (wnext x rem' m') z) (ensures reachable (vw x) z)
  = let w = vw x in
    C.forall_intro (w_resolve x x' o i v h' rem' m');
    assert (outside_ref w z);
    reach_outside w z

let w_reach (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ reachable (wnext x rem' m') z) (ensures reachable (vw x) z)
  = C.forall_intro (C.move_requires (w_outside x x' o i v h' rem' m'));
    C.forall_intro_2 (fun y z -> C.move_requires (w_edge x x' o i v h' rem' m' y) z);
    reachable_within (wnext x rem' m') (reachable (vw x)) z

let w_r_reach (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m')
          (ensures r_reach x' (wnext x rem' m') /\ rback_w x (wnext x rem' m'))
  = C.forall_intro (C.move_requires (w_reach x x' o i v h' rem' m'));
    C.forall_intro (C.move_requires (reach_kept x (vw x)));
    w_basic x x' o i v h' rem' m';
    reveal_opaque (`%r_reach) (r_reach #c);
    reveal_opaque (`%rback_w) (rback_w #c)

let w_resolves (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (u: value)
  : Lemma (requires wok x x' o i v h' rem' m' /\ resolves (vw x) u) (ensures resolves (wnext x rem' m') u)
  = match u with
    | VPtr (Major a) -> w_resolve x x' o i v h' rem' m' a
    | _ -> ()

let w_res_maj (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z j: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ reachable (wnext x rem' m') z /\ ptr_field m' z j)
          (ensures resolves (wnext x rem' m') (field m' z j))
  = let w = vw x in
    w_reach x x' o i v h' rem' m' z;
    w_basic x x' o i v h' rem' m';
    wp_hd x o i v rem' m' z;
    w_field x x' o i v h' rem' m' z j;
    if z = o && j = i then w_resolves x x' o i v h' rem' m' v
    else begin res_maj w z j; w_resolves x x' o i v h' rem' m' (field w.maj z j) end

let w_r_res (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m') (ensures r_res (wnext x rem' m'))
  = let w = vw x in
    let rt (u: value) : Lemma (requires L.memP u w.roots) (ensures resolves (wnext x rem' m') u)
      = res_root w u; w_resolves x x' o i v h' rem' m' u in
    C.forall_intro (C.move_requires rt);
    C.forall_intro_2 (fun z j -> C.move_requires (w_res_maj x x' o i v h' rem' m' z) j);
    let yf (y j: nat) : Lemma (requires ptr_field w.yng y j) (ensures resolves (wnext x rem' m') (field w.yng y j))
      = res_yng w y j; w_resolves x x' o i v h' rem' m' (field w.yng y j) in
    C.forall_intro_2 (fun y j -> C.move_requires (yf y) j);
    reveal_opaque (`%r_res) r_res

let w_lt (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ live_target c.a x'.ph x'.ast x'.w.cmaj m' z)
          (ensures live_target c.a x.ph x.ast x.w.cmaj (mj x) z)
  = w_basic x x' o i v h' rem' m';
    wp_col x o i v rem' m' z

let w_young1 (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z j b: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ live_target c.a x'.ph x'.ast x'.w.cmaj m' z /\
                    ptr_field m' z j /\ field m' z j == VPtr (Young b))
          (ensures Some? (resolve (vw x).yng b) /\ L.memP (z, j) rem')
  = let w = vw x in
    w_basic x x' o i v h' rem' m';
    wp_hd x o i v rem' m' z;
    w_field x x' o i v h' rem' m' z j;
    wp_rem x o i v rem' m';
    if z = o && j = i then assert (young_slot w.maj o i v)
    else begin
      w_lt x x' o i v h' rem' m' z;
      reveal_opaque (`%r_young) (r_young #c);
      assert (ptr_field w.maj z j /\ field w.maj z j == VPtr (Young b))
    end

let w_r_young (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m') (ensures r_young x' (wnext x rem' m'))
  = C.forall_intro_3 (fun z j b -> C.move_requires (w_young1 x x' o i v h' rem' m' z j) b);
    reveal_opaque (`%r_young) (r_young #c)

/// ---------------------------------------------------------------------------
/// Colours: snapshot-at-the-beginning
/// ---------------------------------------------------------------------------

/// A block on a path: greyed by the barrier, or reached after the store.
let greyed_or_reached (#c: comps) (x: config c) (m': mheap) (u: nat) : prop =
  col_of m' u == Grey \/ live_reached m' (scan_of x) (union x.snap x.allocd) u

let rec w_lpath_rec (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
    (u: nat) (p: lpath (mj x) (scan_of x) (union x.snap x.allocd) u)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph)
          (ensures union x.snap x.allocd u /\ greyed_or_reached x m' u) (decreases p)
  = let m = mj x in
    reveal_opaque (`%r_col) (r_col #c);
    w_basic x x' o i v h' rem' m';
    wp_hd x o i v rem' m' u;
    wp_col x o i v rem' m' u;
    match p with
    | PGrey _ _ -> let q : lpath m' (scan_of x) (union x.snap x.allocd) u = PGrey u () in ()
    | PStep y _ p0 _ ->
      w_lpath_rec x x' o i v h' rem' m' y p0;
      uedge_major m (scan_of x) y u;
      edge_closed m (union x.snap x.allocd) y u;
      if col_of m' u = Grey then ()
      else begin
        (* a path to y after the store *)
        wp_hd x o i v rem' m' y;
        wp_col x o i v rem' m' y;
        let py : squash (live_reached m' (scan_of x) (union x.snap x.allocd) y) =
          if col_of m' y = Grey then (let q : lpath m' (scan_of x) (union x.snap x.allocd) y = PGrey y () in ()) else () in
        (* the edge y -> u is not the overwritten one *)
        eliminate exists (j a: nat). ptr_field m y j /\ unscanned (scan_of x) y j /\ field m y j == VPtr (Major a) /\
                                     resolve m a == Some u
        with begin
          w_field x x' o i v h' rem' m' y j;
          w_resolve x x' o i v h' rem' m' a;
          if y = o && j = i then assert (tgt x o i == Some u)
          else begin
            assert (ptr_field m' y j /\ field m' y j == VPtr (Major a));
            assert (uedge m' (scan_of x) y u);
            let q0 = FStar.IndefiniteDescription.indefinite_description_ghost (lpath m' (scan_of x) (union x.snap x.allocd) y) (fun _ -> True) in
            let q : lpath m' (scan_of x) (union x.snap x.allocd) u = PStep y u q0 () in ()
          end
        end
      end

let w_lpath (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (u: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph /\ live_reached (mj x) (scan_of x) (union x.snap x.allocd) u)
          (ensures greyed_or_reached x m' u)
  = let f (p: lpath (mj x) (scan_of x) (union x.snap x.allocd) u) : Lemma (greyed_or_reached x m' u) = w_lpath_rec x x' o i v h' rem' m' u p in
    C.forall_intro f

let w_tri1 (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph)
          (ensures (live x' z ==> is_block m' z) /\
                   (iu x' m' z /\ dark (col_of m' z) ==> live x' z) /\
                   (x'.allocd z ==> col_of m' z == Black))
  = reveal_opaque (`%r_col) (r_col #c);
    w_basic x x' o i v h' rem' m';
    wp_hd x o i v rem' m' z;
    wp_col x o i v rem' m' z;
    if Some z = tgt x o i then w_tgt x x' o i v h' rem' m'

let w_tri4 (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph /\ x'.snap z /\ col_of m' z == White)
          (ensures live_reached m' (scan_of x') (union x'.snap x'.allocd) z)
  = reveal_opaque (`%r_col) (r_col #c);
    wp_col x o i v rem' m' z;
    assert (col_of (mj x) z == White);
    assert (live_reached (mj x) (scan_of x) (union x.snap x.allocd) z);
    w_lpath x x' o i v h' rem' m' z;
    assert (union x'.snap x'.allocd == union x.snap x.allocd)

/// The block being scanned stays a grey block: the barrier only greys.
let w_scan (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph)
          (ensures scan_ok x' m' /\ fleft m' (scan_of x') == fleft (mj x) (scan_of x))
  = reveal_opaque (`%r_col) (r_col #c);
    w_basic x x' o i v h' rem' m';
    assert (scan_of x' == scan_of x);
    (match scan_of x with
     | Some (s, _) -> wp_hd x o i v rem' m' s; wp_col x o i v rem' m' s
     | None -> wp_hd x o i v rem' m' 0);
    fleft_same (mj x) m' (scan_of x)

let w_tri (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph) (ensures tri_iu x' m' /\ scan_ok x' m')
  = w_scan x x' o i v h' rem' m';
    C.forall_intro (w_tri1 x x' o i v h' rem' m');
    C.forall_intro (C.move_requires (w_tri4 x x' o i v h' rem' m'))

let w_closed1 (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z j a: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph /\ union x.snap x.allocd z /\ ptr_field m' z j /\
                    field m' z j == VPtr (Major a))
          (ensures exists (t: nat). resolve m' a == Some t /\ union x.snap x.allocd t)
  = let w = vw x in
    reveal_opaque (`%r_col) (r_col #c);
    w_basic x x' o i v h' rem' m';
    wp_hd x o i v rem' m' z;
    w_field x x' o i v h' rem' m' z j;
    w_resolve x x' o i v h' rem' m' a;
    if z = o && j = i then begin
      eliminate exists (t: nat). resolve w.maj a == Some t /\ reachable w t
      with reach_kept x w t
    end else assert (ptr_field w.maj z j /\ field w.maj z j == VPtr (Major a))

let w_r_heap (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m') (ensures r_heap x' (wnext x rem' m'))
  = w_basic x x' o i v h' rem' m';
    reveal_opaque (`%r_heap) (r_heap #c)

let w_r_live (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m') (ensures r_live x' (wnext x rem' m'))
  = w_basic x x' o i v h' rem' m';
    r_live_iu x x' (vw x) (wnext x rem' m')

let w_col_same (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ ~(Marking? x.ph))
          (ensures col_of m' z == col_of (mj x) z)
  = wp_col x o i v rem' m' z

let w_r_col_other (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m' /\ ~(Marking? x.ph)) (ensures r_col x' (wnext x rem' m'))
  = w_basic x x' o i v h' rem' m';
    C.forall_intro (C.move_requires (w_col_same x x' o i v h' rem' m'));
    r_col_iu x x' (vw x) (wnext x rem' m')

let w_r_col_mark (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph) (ensures r_col x' (wnext x rem' m'))
  = w_tri x x' o i v h' rem' m';
    C.forall_intro_3 (fun z j a -> C.move_requires (w_closed1 x x' o i v h' rem' m' z j) a);
    assert (closed m' (union x.snap x.allocd));
    assert (union x'.snap x'.allocd == union x.snap x.allocd);
    reveal_opaque (`%r_col) (r_col #c)

let w_r_col (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m')
          (ensures r_col x' (wnext x rem' m') /\ r_live x' (wnext x rem' m') /\ r_heap x' (wnext x rem' m'))
  = w_r_heap x x' o i v h' rem' m';
    w_r_live x x' o i v h' rem' m';
    if Marking? x.ph then w_r_col_mark x x' o i v h' rem' m'
    else w_r_col_other x x' o i v h' rem' m'

/// ---------------------------------------------------------------------------
/// The conclusions
/// ---------------------------------------------------------------------------

let w_kept (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ kept x z)
          (ensures iu x' m' z == true /\ contents_w x (EWrite (Major o) i v) (wnext x rem' m') z)
  = w_basic x x' o i v h' rem' m';
    wp_hd x o i v rem' m' z;
    assert (is_block (mj x) z);
    let f (j: nat) : Lemma (j < wz_of (mj x) z ==> field m' z j == (if z = o && j = i then v else field (mj x) z j))
      = if j < wz_of (mj x) z then w_field x x' o i v h' rem' m' z j in
    C.forall_intro f;
    let w' = wnext x rem' m' in
    assert (w'.maj == m');
    assert (wz_of w'.maj z == wz_of (mj x) z /\ tag_of w'.maj z == tag_of (mj x) z);
    assert (forall (j: nat). j < wz_of (mj x) z ==> field w'.maj z j == (if z = o && j = i then v else field (mj x) z j));
    assert (contents_w x (EWrite (Major o) i v) w' z)

let w_word (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (n: nat)
  : Lemma (requires wok x x' o i v h' rem' m' /\ n < (mj x).size)
          (ensures (in_use_word_c x n /\ free_w x' (wnext x rem' m') n ==> False) /\
                   (free_word_c x n /\ used_w x' (wnext x rem' m') n ==> False))
  = w_basic x x' o i v h' rem' m';
    C.forall_intro (wp_hd x o i v rem' m');
    assert (forall (y: nat). covers m' y n == covers (mj x) y n);
    word_xor c.a x.ast x.w.cmaj (mj x) n

let w_meas1 (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap) (z: nat)
  : Lemma (requires wok x x' o i v h' rem' m')
          (ensures (white_live m' (live x') z ==> white_live (mj x) (live x') z) /\
                   (grey_live m' (live x') z ==> grey_live (mj x) (live x') z \/
                      (tgt x o i == Some z /\ col_of (mj x) z == White)))
  = wp_hd x o i v rem' m' z;
    wp_col x o i v rem' m' z

let w_measure (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m' /\ Marking? x.ph)
          (ensures mark_noinc (mj x) (scan_of x) m' (scan_of x') (live x'))
  = let m = mj x in
    w_scan x x' o i v h' rem' m';
    C.forall_intro (w_meas1 x x' o i v h' rem' m');
    match tgt x o i with
    | Some t ->
      if col_of m t = White then begin
        w_tgt x x' o i v h' rem' m';
        reveal_opaque (`%r_heap) (r_heap #c);
        wp_hd x o i v rem' m' t;
        wp_col x o i v rem' m' t;
        assert (white_live m (live x') t /\ ~(white_live m' (live x') t))
      end
    | None -> ()

let w_cs (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires wok x x' o i v h' rem' m')
          (ensures (let e = EWrite (Major o) i v in let w' = wnext x rem' m' in
                    cs_keep x e x' w' /\ cs_alloc x e x' w' /\ cs_words x e x' w' /\ cs_mark x e x' w' /\
                    cs_old x e x'))
  = let e = EWrite (Major o) i v in
    C.forall_intro (C.move_requires (w_kept x x' o i v h' rem' m'));
    reveal_opaque (`%cs_keep) (cs_keep #c);
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    C.forall_intro (C.move_requires (w_word x x' o i v h' rem' m'));
    reveal_opaque (`%cs_words) (cs_words #c);
    (if Marking? x.ph then w_measure x x' o i v h' rem' m');
    reveal_opaque (`%cs_mark) (cs_mark #c)

/// ---------------------------------------------------------------------------
/// EWrite (Major _)
/// ---------------------------------------------------------------------------

let w_finish (#c: comps) (x x': config c) (o i: nat) (v: value) (h': c.t) (rem': list slot) (m': mheap)
  : Lemma (requires faithful c.r /\ wok x x' o i v h' rem' m' /\ views x' (wnext x rem' m'))
          (ensures rinv x' /\ concl_step x (EWrite (Major o) i v) x' /\ rback x x' /\ cyc x x')
  = w_r_reach x x' o i v h' rem' m';
    w_r_res x x' o i v h' rem' m';
    w_r_young x x' o i v h' rem' m';
    w_r_col x x' o i v h' rem' m';
    w_cs x x' o i v h' rem' m';
    w_basic x x' o i v h' rem' m';
    C.forall_intro (wp_hd x o i v rem' m');
    wp_hd x o i v rem' m' 0;
    cyc_same x x' (wnext x rem' m');
    step_out_intro x (EWrite (Major o) i v) x' (wnext x rem' m')

#push-options "--z3rlimit 40"
let write_step (#c: comps) (x: config c) (o i: nat) (v: value)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x (EWrite (Major o) i v) /\
                    mutator_ok x (EWrite (Major o) i v))
          (ensures (let e = EWrite (Major o) i v in let x' = step c x e in
                    rinv x' /\ concl_step x e x' /\ rback x x' /\ cyc x x'))
  = let e = EWrite (Major o) i v in
    let x' = step c x e in
    let w = vw x in
    let m = w.maj in
    vw_views x;
    let (h', rem') = c.b.bwrite (is_marking x.ph) x.w.cmaj x.w.crem o i v in
    assert (write_pre o i v (c.r.storable v) m);
    let m' = FStar.IndefiniteDescription.indefinite_description_ghost mheap
               (fun m' -> c.r.repr m' h' /\ write_post (is_marking x.ph) x.w.crem rem' o i v m m') in
    reveal_opaque (`%wpost) (wpost #c);
    assert (wpost x o i v rem' m');
    w_rel x x' o i v h' rem' m';
    reveal_opaque (`%r_heap) (r_heap #c);
    assert (inv_frame_m c.a x.ph x.w.cmaj x.ast h' m m');
    assert (c.a.inv x.ph h' x.ast /\ (forall (y: nat). c.a.free x.ast h' y == c.a.free x.ast x.w.cmaj y));
    assert (wok x x' o i v h' rem' m');
    assert (views x' (wnext x rem' m'));
    w_finish x x' o i v h' rem' m'
#pop-options
