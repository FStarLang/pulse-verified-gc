/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.MidSweepStep - sweeping further pages keeps the mid-sweep invariant
/// ---------------------------------------------------------------------------
///
/// Plan §20.4.  One step of the sweep (`SweepAll.step`, a pool page or a
/// run) keeps `MidSweep.pages_ok_sw`, whatever allocations came before it:
///
///   - the page invariant without L10 and the lists: the step lemmas of the
///     whole sweep (`SweepStep.pool_step`, `run_step`) are local, and need
///     only the unit as the mark left it;
///   - no grey block in an unswept page: the other pages are kept;
///   - well formed mid-sweep: the blocks in use are the same before and
///     after (the unit's survivors were black and in use, and are white in a
///     swept page, still in use; the rest of the unit was free mid-sweep and
///     is free), block for block (`SweepUnits.unit_ok`), so main's
///     `wf_transport` carries the pointer clauses over.
///
/// **`step_sw`**: one step keeps the invariant and sweeps its unit.
/// **`sweep_rest`**: from any mid-sweep state, sweeping the rest
/// (`SweepAll.sweep_all`, whose steps skip swept units) ends in the `Idle`
/// invariant.  **`sw_start`**: the sweep's start (`StartSweep.start_ready`
/// with the mark's guarantees) is a mid-sweep state.

module GC.Spec.Pages.MidSweepStep

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
open GC.Spec.Pages.Frame
open GC.Spec.Pages.MidSweep

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module G = GC.Spec.Pages.Graft
module Sc = GC.Spec.Pages.Scrub
module Th = GC.Spec.Pages.Theorems
module R = GC.Spec.Pages.Replace
module SU = GC.Spec.Pages.SweepUnits
module SS = GC.Spec.Pages.SweepStep
module SA = GC.Spec.Pages.SweepAll
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module ST = GC.Spec.Pages.SweepTags
module SW = GC.Spec.Pages.SweepWf
module Cells = GC.Spec.Pages.Cells
module SPI = GC.Spec.SweepPhase.Intrinsic
module RC = GC.Spec.Pages.Recolour

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// A unit rewritten in place
/// ---------------------------------------------------------------------------

/// `g'` is `g` with the stretch `[s, e)` rewritten; both walks step from
/// `s` to `e`.
let unit_step (g g': heap) (s e: nat) : prop =
  s < e /\ e <= heap_size /\ steps_to g R.z s /\ steps_to g s e /\ steps_to g' s e /\
  (forall (x: hp_addr). U64.v x < s \/ U64.v x >= e ==> read_word g' x == read_word g x)

/// Outside the stretch, both walks reach the same positions (as
/// `Replace.replace_walk`).
let unit_walk (g g': heap) (s e: nat) (b: nat)
  : Lemma (requires unit_step g g' s e /\ (b <= s \/ b >= e))
          (ensures steps_to g R.z b <==> steps_to g' R.z b)
  = steps_to_frame g g' R.z s;
    if b <= s then steps_to_frame g g' R.z b
    else begin
      steps_to_frame g g' e b;
      if steps_to g R.z b then begin
        steps_to_trans g R.z s e;
        R.steps_to_det g R.z e b;
        steps_to_trans g' s e b;
        steps_to_trans g' R.z s b
      end;
      if steps_to g' R.z b then begin
        steps_to_trans g' R.z s e;
        R.steps_to_det g' R.z e b;
        steps_to_trans g s e b;
        steps_to_trans g R.z s b
      end
    end

/// An object outside the stretch is an object of both heaps or of neither,
/// with the same block.
let unit_obj_out (g g': heap) (s e: nat) (x: obj_addr)
  : Lemma (requires unit_step g g' s e /\ (U64.v x - 8 < s \/ U64.v x - 8 >= e))
          (ensures (Seq.mem x (objects zero_addr g) <==> Seq.mem x (objects zero_addr g')) /\
                   (Seq.mem x (objects zero_addr g) ==>
                      (forall (y: hp_addr). U64.v x - 8 <= U64.v y /\
                         U64.v y < U64.v x - 8 + words_at g (U64.v x - 8) * 8 ==>
                         read_word g' y == read_word g y)))
  = let h = U64.v x - 8 in
    hd_address_spec x;
    steps_to_frame g g' R.z s;
    unit_walk g g' s e h;
    R.obj_iff g x;
    R.obj_iff g' x;
    if h < s && steps_to g R.z h then R.block_before g R.z h s;
    if h < heap_size then assert (hdr g' h == hdr g h)

/// An object inside the stretch is a block the walk from `s` reaches.
let unit_obj_in (g g': heap) (s e: nat) (x: obj_addr)
  : Lemma (requires unit_step g g' s e /\ s <= U64.v x - 8 /\ U64.v x - 8 < e)
          (ensures (Seq.mem x (objects zero_addr g) <==> steps_to g s (U64.v x - 8) /\ U64.v x < heap_size) /\
                   (Seq.mem x (objects zero_addr g') <==> steps_to g' s (U64.v x - 8) /\ U64.v x < heap_size))
  = steps_to_frame g g' R.z s;
    R.replace_obj_in g s e x;
    R.replace_obj_in g' s e x

/// ---------------------------------------------------------------------------
/// The blocks in use are kept
/// ---------------------------------------------------------------------------

/// The sweep of the unit at `[s, e)`: its survivors, made white, and free
/// blocks (`unit_ok`); no grey block in it before; the unit unswept before
/// and swept after, the swept bits of the rest kept.
let swept_unit (g g': heap) (pm pm': page_map) (p k: nat) : prop =
  p + k <= n_pages /\ k >= 1 /\
  unit_step g g' (page_base p) (page_base (p + k)) /\
  SU.unit_ok g g' p k /\ ST.blue_ok g g' p k /\
  (forall (b: nat). steps_to g (page_base p) b /\ b < page_base (p + k) ==> color_at g b =!= Gray) /\
  (forall (a: nat). page_base p <= a /\ a < page_base (p + k) ==> G.uw pm a /\ not (G.uw pm' a)) /\
  (forall (a: nat). a < page_base p \/ a >= page_base (p + k) ==> G.uw pm' a == G.uw pm a)

let colours (g: heap) (x: obj_addr)
  : Lemma (color_at g (U64.v x - 8) == color_of_object x g /\
           (is_blue x g <==> color_of_object x g == Blue) /\
           (is_white x g <==> color_of_object x g == White) /\
           (is_black x g <==> color_of_object x g == Black) /\
           (is_gray x g <==> color_of_object x g == Gray))
  = R.hdr_obj g x;
    is_blue_iff x g;
    is_white_iff x g;
    is_black_iff x g;
    is_gray_iff x g

let whitened_colour (g g': heap) (b: nat)
  : Lemma (requires Th.whitened_at g g' b) (ensures color_at g' b == White /\ words_at g' b == words_at g b)
  = colorHeader_getColor (hdr g b) White;
    colorHeader_preserves_wosize (hdr g b) White

#push-options "--z3rlimit 40"
let step_use (g g': heap) (pm pm': page_map) (p k: nat) (y: obj_addr)
  : Lemma (requires swept_unit g g' pm pm' p k)
          (ensures in_use (free_sw pm') g' y == in_use (free_sw pm) g y)
  = let s = page_base p in
    let e = page_base (p + k) in
    let h = U64.v y - 8 in
    colours g y;
    colours g' y;
    if h < s || h >= e then begin
      unit_obj_out g g' s e y;
      if Seq.mem y (objects zero_addr g) then begin
        hd_address_spec y;
        R.hdr_obj g y;
        color_of_header_eq y g g'
      end
    end
    else begin
      unit_obj_in g g' s e y;
      if Seq.mem y (objects zero_addr g') && color_at g' h <> Blue then whitened_colour g g' h;
      if Seq.mem y (objects zero_addr g) && color_at g h = Black then whitened_colour g g' h
    end
#pop-options

/// A block in use keeps its block.
#push-options "--z3rlimit 40"
let step_block (g g': heap) (pm pm': page_map) (p k: nat) (y: obj_addr)
  : Lemma (requires swept_unit g g' pm pm' p k /\ in_use (free_sw pm) g y)
          (ensures SPI.same_block g g' (hd_address y))
  = let s = page_base p in
    let e = page_base (p + k) in
    let h = U64.v y - 8 in
    colours g y;
    hd_address_spec y;
    R.hdr_obj g y;
    if h < s || h >= e then unit_obj_out g g' s e y
    else begin
      unit_obj_in g g' s e y;
      assert (color_at g h == Black);
      whitened_colour g g' h;
      SA.whiten_tag y g
    end
#pop-options

/// No block of the swept heap is infix.
#push-options "--z3rlimit 40"
let step_infix (g g': heap) (pm pm': page_map) (p k: nat) (y: obj_addr)
  : Lemma (requires swept_unit g g' pm pm' p k /\ no_infix_block g /\ Seq.mem y (objects zero_addr g'))
          (ensures ~(is_infix y g'))
  = let s = page_base p in
    let e = page_base (p + k) in
    let h = U64.v y - 8 in
    colours g' y;
    hd_address_spec y;
    R.hdr_obj g' y;
    if h < s || h >= e then begin
      unit_obj_out g g' s e y;
      R.hdr_obj g y;
      resolve_object_locality y g g'
    end
    else begin
      unit_obj_in g g' s e y;
      if color_at g' h = Blue then begin
        if getTag (hdr g' h) = 0UL then SW.tag0_not_infix g' y
        else begin
          assert (steps_to g s h /\ hdr g' h == hdr g h);
          R.hdr_obj g y;
          resolve_object_locality y g g'
        end
      end
      else begin
        assert (Th.whitened_at g g' h);
        R.hdr_obj g y;
        SA.whiten_tag y g;
        is_infix_spec y g;
        is_infix_spec y g';
        tag_of_object_spec y g;
        tag_of_object_spec y g'
      end
    end
#pop-options

/// **Well formed mid-sweep, after sweeping a unit.**
let step_wf (g g': heap) (pm pm': page_map) (p k: nat)
  : Lemma (requires swept_unit g g' pm pm' p k /\ well_formed_heap_with (free_sw pm) g)
          (ensures well_formed_heap_with (free_sw pm') g')
  = wf_with_parts ();
    free_sw_ok pm;
    free_sw_ok pm';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (step_infix g g' pm pm' p k));
    FStar.Classical.forall_intro (step_use g g' pm pm' p k);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (step_block g g' pm pm' p k));
    SPI.wf_transport g g' (free_sw pm) (free_sw pm')

/// The blocks in use mid-sweep are the same before and after, and each keeps
/// its block (size, tag, fields).
let use_kept (g g': heap) (pm pm': page_map) : prop =
  (forall (y: obj_addr). in_use (free_sw pm') g' y == in_use (free_sw pm) g y) /\
  (forall (y: obj_addr). in_use (free_sw pm) g y ==> SPI.same_block g g' (hd_address y))

let unit_use_kept (g g': heap) (pm pm': page_map) (p k: nat)
  : Lemma (requires swept_unit g g' pm pm' p k) (ensures use_kept g g' pm pm')
  = FStar.Classical.forall_intro (step_use g g' pm pm' p k);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (step_block g g' pm pm' p k))

/// ---------------------------------------------------------------------------
/// Swept bits
/// ---------------------------------------------------------------------------

/// Every page swept in `pm` is swept in `pm'`.
let swept_mono (pm pm': page_map) : prop =
  forall (j: nat{j < n_pages}). (entry pm j).swept ==> (entry pm' j).swept

/// A page swept in `pm'` holds no word unswept there; a page whose swept
/// bit is kept, the same words.
let uw_page (pm pm': page_map) (a: nat)
  : Lemma (requires U64.v zero_addr <= a /\ a < pages_end /\
                    (entry pm' (page_of a)).swept == (entry pm (page_of a)).swept)
          (ensures G.uw pm' a == G.uw pm a)
  = reveal_opaque (`%G.uw) G.uw

let uw_swept (pm: page_map) (a: nat)
  : Lemma (requires U64.v zero_addr <= a /\ a < pages_end /\ (entry pm (page_of a)).swept)
          (ensures not (G.uw pm a))
  = reveal_opaque (`%G.uw) G.uw

let uw_out (pm: page_map) (a: nat)
  : Lemma (requires ~(U64.v zero_addr <= a /\ a < pages_end)) (ensures not (G.uw pm a))
  = reveal_opaque (`%G.uw) G.uw

/// The swept bits of the unit `[p, p + k)`, unswept before and swept
/// after, the others kept: the unswept words move as `swept_unit` says.
let unit_uw (pm pm': page_map) (p k: nat)
  : Lemma (requires p + k <= n_pages /\
                    (forall (j: nat{j < n_pages}). p <= j /\ j < p + k ==>
                       not (entry pm j).swept /\ (entry pm' j).swept) /\
                    (forall (j: nat{j < n_pages}). j < p \/ j >= p + k ==> (entry pm' j).swept == (entry pm j).swept))
          (ensures (forall (a: nat). page_base p <= a /\ a < page_base (p + k) ==> G.uw pm a /\ not (G.uw pm' a)) /\
                   (forall (a: nat). a < page_base p \/ a >= page_base (p + k) ==> G.uw pm' a == G.uw pm a))
  = let inside (a: nat) : Lemma (page_base p <= a /\ a < page_base (p + k) ==> G.uw pm a /\ not (G.uw pm' a))
      = if page_base p <= a && a < page_base (p + k) then begin
          in_pages_uw pm p k a;
          page_of_pos a p k;
          uw_swept pm' a
        end
    in
    FStar.Classical.forall_intro inside;
    let outside (a: nat) : Lemma (a < page_base p \/ a >= page_base (p + k) ==> G.uw pm' a == G.uw pm a)
      = if a < page_base p || a >= page_base (p + k) then begin
          if U64.v zero_addr <= a && a < pages_end then begin
            page_of_spec a;
            let j = page_of a in
            if p <= j && j < p + k then begin
              page_base_mono p j;
              page_base_mono (j + 1) (p + k)
            end;
            uw_page pm pm' a
          end
          else begin uw_out pm a; uw_out pm' a end
        end
    in
    FStar.Classical.forall_intro outside

/// The unit of one page.
let unit_one (pm pm': page_map) (p: nat{p < n_pages})
  : Lemma (requires not (entry pm p).swept /\ (entry pm' p).swept /\
                    (forall (j: nat{j < n_pages}). j <> p ==> SS.same_but_next (entry pm j) (entry pm' j)))
          (ensures (forall (j: nat{j < n_pages}). p <= j /\ j < p + 1 ==>
                      not (entry pm j).swept /\ (entry pm' j).swept) /\
                   (forall (j: nat{j < n_pages}). j < p \/ j >= p + 1 ==> (entry pm' j).swept == (entry pm j).swept))
  = ()

/// The kinds and swept bits of the pages outside the unit `[p, p + k)` are
/// kept.
let kinds_kept (pm pm': page_map) (p k: nat) : prop =
  forall (j: nat{j < n_pages}). j < p \/ j >= p + k ==>
    (entry pm' j).kind == (entry pm j).kind /\ (entry pm' j).swept == (entry pm j).swept

/// ---------------------------------------------------------------------------
/// A pool page
/// ---------------------------------------------------------------------------

/// No position of a marked pool page is grey.
let pool_no_grey (g: heap) (pm: page_map) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (b: nat)
  : Lemma (requires Th.marked_pool_page g pm p c /\ steps_to g (page_base p) b /\ b < page_base (p + 1))
          (ensures color_at g b =!= Gray)
  = ST.slot0 p c;
    ST.pool_pos3 g p c 0 b

#push-options "--z3rlimit 40"
let pool_step_sw (g: heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pages_ok_sw g st /\ (entry st.pm p).kind == Pool c /\ not (entry st.pm p).swept)
          (ensures (let (g', st') = SA.step g st p in
                    pages_ok_sw g' st' /\ (entry st'.pm p).swept == true /\ swept_mono st.pm st'.pm /\
                    kinds_kept st.pm st'.pm p 1 /\ use_kept g g' st.pm st'.pm))
  = let pm = st.pm in
    pages_ok_sw_elim g st;
    assert (page_local g pm p);
    assert (Th.marked_pool_page g pm p c);
    let cs = Cells.walk g (Cells.large_head st) heap_words in
    Cells.large_ok_lview g st;
    SS.pool_step g st p c cs;
    let (g', e) = SP.sweep_page g pm p in
    let st' = SS.push_avail st p e in
    let pm' = st'.pm in
    assert (SA.step g st p == (g', st'));
    Cells.lview_large_ok g' st' cs;
    (* the unit *)
    walk_pages_reached g pm p;
    page_steps g pm p;
    page_base_mono p (p + 1);
    page_base_mono (p + 1) n_pages;
    ST.pool_blue_ok g pm p c;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (pool_no_grey g pm p c));
    unit_one pm pm' p;
    unit_uw pm pm' p 1;
    assert (swept_unit g g' pm pm' p 1);
    unit_use_kept g g' pm pm' p 1;
    step_wf g g' pm pm' p 1;
    (* no grey block in the pages left unswept *)
    let kept_entry (i: nat{i < n_pages})
      : Lemma (not (entry pm' i).swept ==> entry pm' i == entry pm i)
      = if not (entry pm' i).swept && i <> p then
          if FStar.IndefiniteDescription.strong_excluded_middle (entry pm' i == entry pm i) then ()
          else assert (exists (d: nat{d < n_cls}). has_free_slot pm d i)
    in
    FStar.Classical.forall_intro kept_entry;
    no_grey_frame g g' pm pm';
    pages_ok_sw_intro g' st'
#pop-options

/// ---------------------------------------------------------------------------
/// A run
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let run_step_sw (g: heap) (st: pstate) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires pages_ok_sw g st /\ (entry st.pm p).kind == LargeHead n /\ not (entry st.pm p).swept)
          (ensures (let (g', st') = SA.step g st p in
                    pages_ok_sw g' st' /\ p + n <= n_pages /\
                    (forall (j: nat{j < n_pages}). p <= j /\ j < p + n ==> (entry st'.pm j).swept) /\
                    swept_mono st.pm st'.pm /\ kinds_kept st.pm st'.pm p n /\ use_kept g g' st.pm st'.pm))
  = let pm = st.pm in
    pages_ok_sw_elim g st;
    assert (page_local g pm p);
    assert (run_ok pm p);
    assert (Th.marked_run g pm p);
    let cs = Cells.walk g (Cells.large_head st) heap_words in
    Cells.large_ok_lview g st;
    SS.run_step g st p n cs;
    let (g', pm', fp') = SR.sweep_run g pm p (Cells.large_head st) in
    let st' = SS.run_state st pm' fp' in
    assert (SA.step g st p == (g', st'));
    eliminate exists (cs': list obj_addr). Cells.lview g' st' cs'
    with Cells.lview_large_ok g' st' cs';
    (* the unit *)
    walk_pages_reached g pm p;
    page_base_mono p (p + n);
    page_base_mono (p + n) n_pages;
    ST.run_blue_ok g pm p (Cells.large_head st);
    let in_unit (j: nat{j < n_pages})
      : Lemma (p <= j /\ j < p + n ==> not (entry pm j).swept /\ (entry pm' j).swept)
      = if p < j && j < p + n then assert ((entry pm j).swept == (entry pm p).swept)
    in
    FStar.Classical.forall_intro in_unit;
    let off_unit (j: nat{j < n_pages})
      : Lemma (j < p \/ j >= p + n ==> (entry pm' j).swept == (entry pm j).swept) = ()
    in
    FStar.Classical.forall_intro off_unit;
    unit_uw pm pm' p n;
    assert (swept_unit g g' pm pm' p n);
    unit_use_kept g g' pm pm' p n;
    step_wf g g' pm pm' p n;
    no_grey_frame g g' pm pm';
    pages_ok_sw_intro g' st'
#pop-options

/// ---------------------------------------------------------------------------
/// Any step
/// ---------------------------------------------------------------------------

/// The pages of the unit at a walk page `p`, after its step, are swept.
let unit_swept (st': pstate) (pm: page_map) (p: nat{p < n_pages}) : prop =
  p + span pm p <= n_pages /\
  (forall (j: nat{j < n_pages}). p <= j /\ j < p + span pm p ==> (entry st'.pm j).swept)

let unit_swept_one (st': pstate) (pm: page_map) (p: nat{p < n_pages})
  : Lemma (requires (entry st'.pm p).swept /\ span pm p == 1) (ensures unit_swept st' pm p)
  = ()

let unit_swept_run (st': pstate) (pm: page_map) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires span pm p == n /\ p + n <= n_pages /\
                    (forall (j: nat{j < n_pages}). p <= j /\ j < p + n ==> (entry st'.pm j).swept))
          (ensures unit_swept st' pm p)
  = ()

/// **One sweep step keeps the mid-sweep invariant**, sweeps its unit, and
/// unsweeps nothing.
let step_sw (g: heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires pages_ok_sw g st)
          (ensures (let (g', st') = SA.step g st p in
                    pages_ok_sw g' st' /\ swept_mono st.pm st'.pm /\ use_kept g g' st.pm st'.pm /\
                    (walk_page st.pm p ==> unit_swept st' st.pm p /\ kinds_kept st.pm st'.pm p (span st.pm p))))
  = pages_ok_sw_elim g st;
    let pm = st.pm in
    assert (run_ok pm p /\ free_ok pm p);
    if walk_page pm p then next_walk_page pm p p;
    if (entry pm p).swept then begin
      if walk_page pm p then begin
        let one (j: nat{j < n_pages}) : Lemma (p <= j /\ j < p + span pm p ==> (entry pm j).swept)
          = if p < j && j < p + span pm p then assert ((entry pm j).swept == (entry pm p).swept)
        in
        FStar.Classical.forall_intro one
      end
    end
    else match (entry pm p).kind with
      | Pool c ->
        pool_step_sw g st p c;
        let (g', st') = SA.step g st p in
        unit_swept_one st' pm p
      | LargeHead n ->
        run_step_sw g st p n;
        let (g', st') = SA.step g st p in
        unit_swept_run st' pm p n
      | _ -> ()

/// ---------------------------------------------------------------------------
/// The end of the sweep
/// ---------------------------------------------------------------------------

/// **Every page swept: the `Idle` invariant.**  Mid-sweep, free then means
/// blue.
let sw_end (g: heap) (st: pstate)
  : Lemma (requires pages_ok_sw g st /\ GC.Spec.Pages.MarkPhase.all_swept st)
          (ensures GC.Spec.Pages.Allocator.inv GC.Spec.AllocIface.Idle g st)
  = pages_ok_sw_elim g st;
    let pm = st.pm in
    free_sw_ok pm;
    GC.Spec.Fields.free_stw_ok ();
    wf_with_parts ();
    let none (a: nat) : Lemma (not (G.uw pm a))
      = if U64.v zero_addr <= a && a < pages_end then begin page_of_spec a; uw_swept pm a end
        else uw_out pm a
    in
    FStar.Classical.forall_intro none;
    let same (y: obj_addr) : Lemma (in_use free_stw g y == in_use (free_sw pm) g y) = () in
    FStar.Classical.forall_intro same;
    let blk (y: obj_addr) : Lemma (SPI.same_block g g (hd_address y)) = () in
    FStar.Classical.forall_intro blk;
    SPI.wf_transport g g (free_sw pm) free_stw;
    GC.Spec.Pages.Wf.wfh_old_parts ();
    Sc.ok_of_core g st

/// The rest of the sweep, from page `p` on: the pages before `p` are swept.
#push-options "--fuel 1"
let rec sweep_from_sw (g: heap) (st: pstate) (p: nat)
  : Lemma (requires pages_ok_sw g st /\ p <= n_pages /\ walk_page st.pm p /\
                    (forall (j: nat{j < n_pages}). j < p ==> (entry st.pm j).swept))
          (ensures (let (g', st') = SA.sweep_from g st p in
                    pages_ok_sw g' st' /\ GC.Spec.Pages.MarkPhase.all_swept st'))
          (decreases (if p < n_pages then n_pages - p else 0))
  = if p >= n_pages then ()
    else begin
      pages_ok_sw_elim g st;
      let k = span st.pm p in
      step_sw g st p;
      let (g', st') = SA.step g st p in
      next_walk_page st.pm p p;
      pages_ok_sw_elim g' st';
      sweep_from_sw g' st' (p + k)
    end
#pop-options

/// **The sweep still ends in the `Idle` invariant**: from any mid-sweep
/// state, whatever allocations and steps came before, sweeping the rest
/// (each step skips the units already swept) gives it.
let sweep_rest (g: heap) (st: pstate)
  : Lemma (requires pages_ok_sw g st)
          (ensures (let (g', st') = SA.sweep_all g st in
                    GC.Spec.Pages.Allocator.inv GC.Spec.AllocIface.Idle g' st'))
  = pages_ok_sw_elim g st;
    if n_pages > 0 then assert (cont_ok st.pm 0);
    sweep_from_sw g st 0;
    let (g', st') = SA.sweep_all g st in
    sw_end g' st'

/// ---------------------------------------------------------------------------
/// The start of the sweep
/// ---------------------------------------------------------------------------

/// Where the sweep starts, every page that is not free is unswept, so a
/// block that is not free lies in an unswept page.
let start_unswept (g: heap) (st: pstate) (y: obj_addr)
  : Lemma (requires SA.sweep_ready g st /\ Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
          (ensures unswept_at st.pm y)
  = let pm = st.pm in
    let h = U64.v y - 8 in
    colours g y;
    R.obj_iff g y;
    pages_end_bound ();
    if h < pages_end then begin
      unit_of g pm h;
      eliminate exists (i: nat{i < n_pages}).
        walk_page pm i /\ page_base i <= h /\ h < page_base (i + span pm i) /\
        steps_to g (page_base i) h /\ steps_to g (page_base i) (page_base (i + span pm i)) /\
        i + span pm i <= n_pages /\
        (forall (j: nat{j < n_pages}). i <= j /\ j < i + span pm i ==> (entry pm j).swept == (entry pm i).swept)
      with begin
        page_of_pos h i (span pm i);
        if (entry pm i).kind = Free then begin
          assert (page_shape g pm i);
          GC.Spec.Pages.MarkPhase.free_page_only g i h
        end
        else begin
          reveal_opaque (`%G.uw) G.uw;
          assert (not (entry pm (page_of h)).swept)
        end
      end
    end
    else begin
      (* the tail is one free block *)
      walk_pages_reached g pm n_pages;
      assert (tail_shape g);
      R.steps_to_det g R.z pages_end h;
      if h > pages_end then begin
        steps_to_refl g pages_end;
        R.block_before g pages_end pages_end h
      end
    end

/// **The sweep's start is a mid-sweep state**: the state the mark leaves,
/// lists cleared and every page that is not free unswept (`sweep_ready`),
/// with what the mark guarantees (`mark_done`).
#push-options "--z3rlimit 40"
let sw_start (g: heap) (st: pstate)
  : Lemma (requires SA.sweep_ready g st /\ SA.mark_done g)
          (ensures pages_ok_sw g st)
  = let pm = st.pm in
    SA.inv_init g st;
    SA.inv_elim g st g st 0;
    eliminate exists (cs: list obj_addr). Cells.lview g st cs
    with Cells.lview_large_ok g st cs;
    assert (Sc.core g st);
    free_sw_ok pm;
    wf_parts ();
    wf_with_parts ();
    (* a block in use is black: not grey after the mark, not free *)
    let black (src: obj_addr)
      : Lemma (requires in_use (free_sw pm) g src) (ensures is_black src g /\ in_use free_stw g src)
      = in_use_not_blue (free_sw pm) g src;
        start_unswept g st src;
        colours g src
    in
    let p2 (src dst: obj_addr)
      : Lemma (requires in_use (free_sw pm) g src /\ scannable g src /\ points_to g src dst)
              (ensures in_use (free_sw pm) g (resolve_object dst g))
      = black src;
        points_to_target_not_free free_stw g src dst
    in
    pointers_lead_to_non_free_intro (free_sw pm) g p2;
    let p3 (src dst: obj_addr)
      : Lemma (requires in_use (free_sw pm) g src /\ scannable g src /\ points_to g src dst)
              (ensures infix_addr_wf g (objects zero_addr g) dst)
      = black src;
        points_to_target_not_free free_stw g src dst
    in
    interior_pointers_valid_intro (free_sw pm) g p3;
    pages_ok_sw_intro g st
#pop-options
