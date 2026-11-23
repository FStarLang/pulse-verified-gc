/// ---------------------------------------------------------------------------
/// GC.Spec.Top.RInv - the run invariant
/// ---------------------------------------------------------------------------
///
/// Design doc §16.3, §16.6 (module 2).  `rinv x` is carried along a run by
/// one step lemma per event (GC.Spec.Top.Step*); `concl_point` (clauses (1b)
/// and (5)) is read off it (`point_of_rinv`).  Its parts, each sealed and
/// stated on a world `w` that views `x` (any such world: `rinv_w_agree`):
///   - R1 `r_heap`: the heaps well formed, the allocator's invariant;
///   - R3 `r_reach`, `r_res`: reachable objects are kept; every pointer in a
///     root, in a pointer field of a reachable block or of any young block
///     resolves;
///   - R4 `r_young`: every young pointer in a pointer field of a block the
///     program may use (`live_target`) resolves and its slot is remembered;
///   - R5 `r_col`: colours.  Idle: nothing in use is dark.  Marking: the
///     tricolour invariant of `snap` and `allocd`, which are closed.
///     Sweeping: nothing in use is grey, a black block in use is live, and a
///     live block not yet swept is black;
///   - R2/R6 `r_live`: while marking or sweeping every live block is in use;
///     while sweeping every swept block in use is live.
/// (R2's "kept => live_target" follows from R5 and R6: `kept_live_target`.)

module GC.Spec.Top.RInv

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// In use in a model heap `m` of the configuration's major heap.
let iu (#c: comps) (x: config c) (m: mheap) (o: nat) : GTot bool = in_use c.a x.ast x.w.cmaj m o

/// A value resolves: a major pointer in the major heap, a young one in the
/// nursery.
let resolves (w: world) (v: value) : prop =
  match v with
  | VPtr (Major a) -> Some? (resolve w.maj a)
  | VPtr (Young a) -> Some? (resolve w.yng a)
  | VInt _ -> True

/// ---------------------------------------------------------------------------
/// The parts
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let r_heap (#c: comps) (x: config c) (w: world) : prop =
  well_formed w.maj /\ young_ok w.yng /\ c.a.inv x.ph x.w.cmaj x.ast

[@@"opaque_to_smt"]
let r_reach (#c: comps) (x: config c) (w: world) : prop =
  forall (o: nat). reachable w o ==> iu x w.maj o == true /\ (Idle? x.ph \/ live x o)

[@@"opaque_to_smt"]
let r_res (w: world) : prop =
  (forall (v: value). L.memP v w.roots ==> resolves w v) /\
  (forall (o i: nat). reachable w o /\ ptr_field w.maj o i ==> resolves w (field w.maj o i)) /\
  (forall (o i: nat). ptr_field w.yng o i ==> resolves w (field w.yng o i))

[@@"opaque_to_smt"]
let r_young (#c: comps) (x: config c) (w: world) : prop =
  forall (o i b: nat). live_target c.a x.ph x.ast x.w.cmaj w.maj o /\ ptr_field w.maj o i /\
    field w.maj o i == VPtr (Young b) ==> Some? (resolve w.yng b) /\ L.memP (o, i) w.rem

let col_sweep (#c: comps) (x: config c) (p: c.k.progress) (m: mheap) (o: nat) : prop =
  col_of m o <> Grey /\ (col_of m o == Black ==> live x o) /\
  (live x o /\ c.k.unswept p o == true ==> col_of m o == Black)

[@@"opaque_to_smt"]
let r_col (#c: comps) (x: config c) (w: world) : prop =
  match x.ph with
  | Idle -> forall (o: nat). iu x w.maj o ==> not (dark (col_of w.maj o))
  | Marking -> tricolour w.maj x.snap x.allocd /\ closed w.maj (union x.snap x.allocd)
  | Sweeping p -> forall (o: nat). iu x w.maj o ==> col_sweep x p w.maj o

[@@"opaque_to_smt"]
let r_live (#c: comps) (x: config c) (w: world) : prop =
  match x.ph with
  | Idle -> True
  | Marking -> forall (o: nat). live x o ==> iu x w.maj o
  | Sweeping p -> forall (o: nat). (live x o ==> iu x w.maj o) /\ (iu x w.maj o /\ c.k.unswept p o == false ==> live x o)

let rinv_w (#c: comps) (x: config c) (w: world) : prop =
  r_heap x w /\ r_reach x w /\ r_res w /\ r_young x w /\ r_col x w /\ r_live x w

let rinv (#c: comps) (x: config c) : prop = has_view x /\ rinv_w x (vw x)

/// ---------------------------------------------------------------------------
/// Any world that views the configuration
/// ---------------------------------------------------------------------------

let ag_iu (#c: comps) (x: config c) (m m': mheap) (o: nat)
  : Lemma (requires agree m m') (ensures iu x m o == iu x m' o /\ (iu x m o ==> col_of m o == col_of m' o))
  = ag_hd m m' o

let ag_r_heap (#c: comps) (x: config c) (w w': world)
  : Lemma (requires wagree w w' /\ r_heap x w) (ensures r_heap x w')
  = reveal_opaque (`%r_heap) (r_heap #c);
    ag_well_formed w.maj w'.maj; ag_young_ok w.yng w'.yng

let ag_r_reach (#c: comps) (x: config c) (w w': world)
  : Lemma (requires wagree w w' /\ r_reach x w) (ensures r_reach x w')
  = reveal_opaque (`%r_reach) (r_reach #c);
    C.forall_intro (C.move_requires (ag_reachable w w'));
    C.forall_intro (C.move_requires (ag_iu x w.maj w'.maj))

let ag_resolves (w w': world) (v: value)
  : Lemma (requires wagree w w') (ensures resolves w v <==> resolves w' v)
  = match v with
    | VPtr (Major a) -> ag_resolve w.maj w'.maj a
    | VPtr (Young a) -> ag_resolve w.yng w'.yng a
    | _ -> ()

let ag_res_maj (w w': world) (o i: nat)
  : Lemma (requires wagree w w' /\ r_res w /\ reachable w' o /\ ptr_field w'.maj o i)
          (ensures resolves w' (field w'.maj o i))
  = reveal_opaque (`%r_res) r_res;
    wagree_sym w w';
    ag_reachable w w' o; ag_ptr_field w.maj w'.maj o i; ag_field w.maj w'.maj o i;
    ag_resolves w w' (field w.maj o i)

let ag_res_yng (w w': world) (o i: nat)
  : Lemma (requires wagree w w' /\ r_res w /\ ptr_field w'.yng o i)
          (ensures resolves w' (field w'.yng o i))
  = reveal_opaque (`%r_res) r_res;
    ag_ptr_field w.yng w'.yng o i; ag_field w.yng w'.yng o i;
    ag_resolves w w' (field w.yng o i)

let ag_r_res (w w': world)
  : Lemma (requires wagree w w' /\ r_res w) (ensures r_res w')
  = C.forall_intro (fun (v: value) -> ag_resolves w w' v);
    C.forall_intro_2 (fun (o i: nat) -> C.move_requires (ag_res_maj w w' o) i);
    C.forall_intro_2 (fun (o i: nat) -> C.move_requires (ag_res_yng w w' o) i);
    reveal_opaque (`%r_res) r_res

let ag_young1 (#c: comps) (x: config c) (w w': world) (o i b: nat)
  : Lemma (requires wagree w w' /\ r_young x w /\ live_target c.a x.ph x.ast x.w.cmaj w'.maj o /\
                    ptr_field w'.maj o i /\ field w'.maj o i == VPtr (Young b))
          (ensures Some? (resolve w'.yng b) /\ L.memP (o, i) w'.rem)
  = reveal_opaque (`%r_young) (r_young #c);
    wagree_sym w w';
    ag_live_target c.a x.ph x.ast x.w.cmaj w.maj w'.maj o;
    ag_ptr_field w.maj w'.maj o i; ag_field w.maj w'.maj o i;
    ag_resolve w.yng w'.yng b

let ag_r_young (#c: comps) (x: config c) (w w': world)
  : Lemma (requires wagree w w' /\ r_young x w) (ensures r_young x w')
  = C.forall_intro_3 (fun o i b -> C.move_requires (ag_young1 x w w' o i) b);
    reveal_opaque (`%r_young) (r_young #c)

let ag_r_col (#c: comps) (x: config c) (w w': world)
  : Lemma (requires wagree w w' /\ r_col x w) (ensures r_col x w')
  = reveal_opaque (`%r_col) (r_col #c);
    match x.ph with
    | Marking -> ag_tricolour w.maj w'.maj x.snap x.allocd; ag_closed w.maj w'.maj (union x.snap x.allocd)
    | _ -> C.forall_intro (C.move_requires (ag_iu x w.maj w'.maj))

let ag_r_live (#c: comps) (x: config c) (w w': world)
  : Lemma (requires wagree w w' /\ r_live x w) (ensures r_live x w')
  = reveal_opaque (`%r_live) (r_live #c);
    C.forall_intro (C.move_requires (ag_iu x w.maj w'.maj))

let rinv_w_agree (#c: comps) (x: config c) (w w': world)
  : Lemma (requires wagree w w' /\ rinv_w x w) (ensures rinv_w x w')
  = ag_r_heap x w w'; ag_r_reach x w w'; ag_r_res w w'; ag_r_young x w w'; ag_r_col x w w'; ag_r_live x w w'

/// **The invariant of a configuration, from any world that views it.**
let rinv_intro (#c: comps) (x: config c) (w: world)
  : Lemma (requires faithful c.r /\ views x w /\ rinv_w x w) (ensures rinv x)
  = vw_agree x w;
    rinv_w_agree x w (vw x)

/// ---------------------------------------------------------------------------
/// Consequences
/// ---------------------------------------------------------------------------

/// Kept, in a world.
let kept_w (#c: comps) (x: config c) (w: world) (o: nat) : prop =
  iu x w.maj o == true /\ (Idle? x.ph \/ live x o)

/// **A kept block is one the program may use.**
let kept_live_target (#c: comps) (x: config c) (w: world) (o: nat)
  : Lemma (requires r_col x w /\ r_live x w /\ kept_w x w o)
          (ensures live_target c.a x.ph x.ast x.w.cmaj w.maj o)
  = reveal_opaque (`%r_col) (r_col #c);
    match x.ph with
    | Sweeping p -> assert (col_sweep x p w.maj o)
    | _ -> ()

let reach_kept (#c: comps) (x: config c) (w: world) (o: nat)
  : Lemma (requires r_reach x w /\ reachable w o) (ensures kept_w x w o)
  = reveal_opaque (`%r_reach) (r_reach #c)

/// The pointers of a reachable block resolve.
let res_maj (w: world) (o i: nat)
  : Lemma (requires r_res w /\ reachable w o /\ ptr_field w.maj o i) (ensures resolves w (field w.maj o i))
  = reveal_opaque (`%r_res) r_res

let res_yng (w: world) (o i: nat)
  : Lemma (requires r_res w /\ ptr_field w.yng o i) (ensures resolves w (field w.yng o i))
  = reveal_opaque (`%r_res) r_res

let res_root (w: world) (v: value)
  : Lemma (requires r_res w /\ L.memP v w.roots) (ensures resolves w v)
  = reveal_opaque (`%r_res) r_res

/// ---------------------------------------------------------------------------
/// (0): the initial configuration
/// ---------------------------------------------------------------------------

let no_reach_init (w: world) (o: nat)
  : Lemma (requires w.roots == [] /\ (forall (y: nat). ~(is_block w.yng y))) (ensures ~(reachable w o))
  = let s (_: nat) : prop = False in
    let aux (r: reach w o) : Lemma False = reach_within w s o r in
    C.forall_intro aux

#push-options "--z3rlimit 40"
let rinv_w_init (c: comps) (n ny: nat) (m: mheap)
  : Lemma (requires (let x = init_config c n ny in
                     init_post c.a n x.w.cmaj x.ast m))
          (ensures (let x = init_config c n ny in
                    rinv_w x ({ maj = m; yng = empty_heap ny; roots = []; rem = [] })))
  = let x = init_config c n ny in
    let w : world = { maj = m; yng = empty_heap ny; roots = []; rem = [] } in
    C.forall_intro (no_reach_init w);
    reveal_opaque (`%r_heap) (r_heap #c);
    reveal_opaque (`%r_reach) (r_reach #c);
    reveal_opaque (`%r_res) r_res;
    reveal_opaque (`%r_young) (r_young #c);
    reveal_opaque (`%r_col) (r_col #c);
    reveal_opaque (`%r_live) (r_live #c)
#pop-options

/// **(0), and the invariant at the start of every run.**
let rinv_init (c: comps) (n ny: nat)
  : Lemma (requires faithful c.r /\ c.r.size_ok n /\ c.r.ysize_ok ny /\ init_at c.r c.a n /\ yinit_ok c.r ny)
          (ensures rinv (init_config c n ny) /\ (forall (o: nat). in_use_c (init_config c n ny) o == false))
  = let x = init_config c n ny in
    let m = FStar.IndefiniteDescription.indefinite_description_ghost mheap
              (fun m -> c.r.repr m x.w.cmaj /\ init_post c.a n x.w.cmaj x.ast m) in
    let w : world = { maj = m; yng = empty_heap ny; roots = []; rem = [] } in
    rinv_w_init c n ny m;
    assert (views x w);
    rinv_intro x w;
    vw_agree x w;
    C.forall_intro (ag_in_use c.a x.ast x.w.cmaj m (mj x))

/// ---------------------------------------------------------------------------
/// (1b) and (5): every point
/// ---------------------------------------------------------------------------

let held_root (#c: comps) (x: config c) (v: value)
  : Lemma (requires rinv x /\ L.memP v (vw x).roots /\ VPtr? v) (ensures resolves_ok x v)
  = let w = vw x in
    res_root w v;
    match v with
    | VPtr (Major a) -> let o = Some?.v (resolve w.maj a) in reach_root w a o; reach_kept x w o
    | _ -> ()

let held_field (#c: comps) (x: config c) (v: value) (o i: nat)
  : Lemma (requires rinv x /\ reachable (vw x) o /\ ptr_field (vw x).maj o i /\ field (vw x).maj o i == v /\
                    VPtr? v)
          (ensures resolves_ok x v)
  = let w = vw x in
    res_maj w o i;
    match v with
    | VPtr (Major a) -> let o' = Some?.v (resolve w.maj a) in reach_field w o i a o'; reach_kept x w o'
    | _ -> ()

let held_yfield (#c: comps) (x: config c) (v: value) (y i: nat)
  : Lemma (requires rinv x /\ ptr_field (vw x).yng y i /\ field (vw x).yng y i == v /\ VPtr? v)
          (ensures resolves_ok x v)
  = let w = vw x in
    res_yng w y i;
    match v with
    | VPtr (Major a) -> let o' = Some?.v (resolve w.maj a) in reach_young w y i a o'; reach_kept x w o'
    | _ -> ()

let held_ok (#c: comps) (x: config c) (v: value)
  : Lemma (requires rinv x) (ensures held x v /\ VPtr? v ==> resolves_ok x v)
  = if VPtr? v then begin
      C.move_requires (held_root x) v;
      C.forall_intro_2 (fun o i -> C.move_requires (held_field x v o) i);
      C.forall_intro_2 (fun y i -> C.move_requires (held_yfield x v y) i)
    end

/// In use and not kept is pending.
let not_kept_pending (#c: comps) (x: config c) (o: nat)
  : Lemma (requires r_live x (vw x) /\ in_use_c x o == true /\ ~(kept x o)) (ensures pending x o)
  = reveal_opaque (`%r_live) (r_live #c)

let partition_word (#c: comps) (x: config c) (w: nat)
  : Lemma (requires r_heap x (vw x) /\ r_live x (vw x) /\ w < (mj x).size)
          (ensures exactly_one (exists (o: nat). covers (mj x) o w /\ kept x o)
                               (exists (o: nat). covers (mj x) o w /\ pending x o)
                               (free_word_c x w))
  = reveal_opaque (`%r_heap) (r_heap #c);
    let m = mj x in
    cover_exists m w;
    let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> covers m o w) in
    C.forall_intro (C.move_requires (cover_unique m o w));
    if in_use_c x o then begin
      if FStar.IndefiniteDescription.strong_excluded_middle (kept x o) then ()
      else not_kept_pending x o
    end

let partition_of (#c: comps) (x: config c)
  : Lemma (requires r_heap x (vw x) /\ r_live x (vw x)) (ensures partition x)
  = C.forall_intro (C.move_requires (partition_word x))

/// **`concl_point` from the invariant.**
let point_of_rinv (#c: comps) (x: config c)
  : Lemma (requires rinv x) (ensures concl_point x)
  = let w = vw x in
    C.forall_intro (C.move_requires (reach_kept x w));
    C.forall_intro (held_ok x);
    partition_of x;
    reveal_opaque (`%r_heap) (r_heap #c)
