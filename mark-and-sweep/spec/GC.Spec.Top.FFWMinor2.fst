/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWMinor2 - a minor collection of two young blocks, computed
/// ---------------------------------------------------------------------------
///
/// Design doc §15.  The incremental witness run collects the nursery while
/// marking and while sweeping when it holds two live one-field blocks: Y1 at
/// young address 0 and Y2 at 2 (GC.Spec.Top.FFWYoung), both roots, with the
/// roots `Y2 :: Y1 :: majors`.  The first-fit minor collection
/// (`FFMinor.pcollect`) is computed exactly:
///   - akhil's promotion forwards the young roots in order: Y2, then Y1, each
///     promoted once through first-fit from the bottom free block
///     (`FFWAlloc.ffalloc_head`), its field copied (`PromoteCopy.copy_cabs`);
///   - the scan finds no young pointer in the copies' fields (Y1's is a major
///     pointer, Y2's an integer);
///   - no promotion fails, so the result is `Done`;
///   - akhil's pointer update over the major heap writes nothing: no field of
///     the heap holds a nursery address;
///   - the forwarding is Y1 to the second copy, Y2 to the first; the roots are
///     rewritten through it.

module GC.Spec.Top.FFWMinor2

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFReplay
open GC.Spec.Top.FFMinor
open GC.Spec.Top.FFWState
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module Q = GC.Spec.Top.PagesQueue
module Q0 = GC.Spec.Top.PagesQueue
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module F = GC.Spec.Top.PagesFwd
module Y = GC.Spec.Top.Young
module YW = GC.Spec.Top.FFWYoung
module FWW = GC.Spec.Top.FFWWords

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Words that are no nursery address
/// ---------------------------------------------------------------------------

/// A value whose word is no nursery address: a major pointer, 0, or odd.
let hv (v: M.value) : bool =
  match v with
  | M.VInt n -> n = 0 || n % 2 = 1
  | M.VPtr (M.Major _) -> true
  | _ -> false

/// A word outside the nursery's object addresses.
let out (u: U64.t) : prop = U64.v u < 8 \/ U64.v u >= minor_heap_size \/ U64.v u % 8 <> 0

let hv_out (v: M.value)
  : Lemma (requires hv v) (ensures out (concv v))
  = base_facts ();
    match v with
    | M.VInt n -> if 0 <= n && n < pow2 64 then assert (U64.v (concv v) == n)
    | M.VPtr (M.Major a) -> if base + 8 * a + 8 < pow2 64 then assert (U64.v (concv v) == base + 8 * a + 8)

let out_none (ms: minor_state) (u: U64.t)
  : Lemma (requires out u)
          (ensures ~(Seq.mem u (minor_objects ms)) /\ ~(is_infix_in_minor ms u) /\ not (is_minor_pointer u))
  = FStar.Classical.move_requires (minor_objects_valid ms) u

/// ---------------------------------------------------------------------------
/// The nursery
/// ---------------------------------------------------------------------------

let yo1 : U64.t = 8UL      (* Y1, the block at 0 *)
let yo2 : U64.t = 24UL     (* Y2, the block at 2 *)

let yo_v (_: unit) : Lemma (8 * 0 + 8 < pow2 64 /\ 8 * 2 + 8 < pow2 64 /\ yo1 == PC.yobj 0 /\ yo2 == PC.yobj 2)
  = assert_norm (8 * 2 + 8 < pow2 64 /\ yo1 == PC.yobj 0 /\ yo2 == PC.yobj 2)

#push-options "--fuel 2"
let ym2_facts (v w: M.value)
  : Lemma (requires ff_room)
          (ensures (let y = YW.ym2 v w in
                    M.is_block y 0 /\ M.is_block y 2 /\ M.wz_of y 0 == 1 /\ M.wz_of y 2 == 1 /\
                    M.tag_of y 0 == 0 /\ M.tag_of y 2 == 0 /\
                    M.field y 0 0 == v /\ M.field y 2 0 == w /\
                    (forall (o: nat). M.is_block y o ==> o == 0 \/ o == 2)))
  = base_facts ()
#pop-options

let one_block (ms: minor_state) (v w: M.value) (o: nat)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ (o == 0 \/ o == 2))
          (ensures (let x = PC.yobj o in
                    Seq.mem x (minor_objects ms) /\ minor_wosize ms x == 1 /\ minor_tag ms x == 0 /\
                    minor_scan_wosize ms x == 1 /\ ~(is_infix_in_minor ms x) /\
                    absv (minor_read_field ms x 0) == M.field (YW.ym2 v w) o 0))
  = ym2_facts v w;
    PC.young_obj (YW.ym2 v w) ms o;
    PC.young_field (YW.ym2 v w) ms o 0;
    minor_scan_wosize_cases ms (PC.yobj o)

/// The nursery's objects are Y1 and Y2.
let only_two (ms: minor_state) (v w: M.value) (x: U64.t)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ Seq.mem x (minor_objects ms))
          (ensures x == yo1 \/ x == yo2)
  = ym2_facts v w;
    Q.obj_young (YW.ym2 v w) ms x;
    yo_v ()

/// A copied field is no nursery address.
let field_out (ms: minor_state) (v w: M.value) (o: nat)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ (o == 0 \/ o == 2) /\
                    hv (M.field (YW.ym2 v w) o 0))
          (ensures out (minor_read_field ms (PC.yobj o) 0))
  = one_block ms v w o;
    PC.young_field (YW.ym2 v w) ms o 0;
    let u = minor_read_field ms (PC.yobj o) 0 in
    FWW.concv_absv u;
    hv_out (absv u)

/// ---------------------------------------------------------------------------
/// One promotion, through first-fit from the bottom block
/// ---------------------------------------------------------------------------

module FWA = GC.Spec.Top.FFWAlloc
module FPr = GC.Spec.Top.FFPromote
module FS1 = GC.Spec.Top.FFWStep

/// The model after promoting the young block `o` (one field `v`) into the
/// bottom block of `m`, of `f` fields.
let promoted (m: M.mheap) (f: nat{3 <= f}) (col: M.colour) (v: M.value) : M.mheap =
  M.fill (FWA.split m f 1 0 col) (f - 1) [v]

let ptag (ms: minor_state) (x: U64.t)
  : Lemma (requires minor_tag ms x == 0) (ensures promoted_tag ms x == tg 0)
  = tg_v 0;
    U64.v_inj (promoted_tag ms x) (tg 0)

#push-options "--fuel 2"
let fields1 (y: M.mheap) (o: nat) : Lemma (requires M.wz_of y o == 1) (ensures M.fields_of y o == [M.field y o 0]) = ()
#pop-options

let obj_eq (r: U64.t) (k: nat)
  : Lemma (requires pos k + 8 < heap_size /\ U64.v r == base + 8 + 8 * k) (ensures r == obj_of k)
  = obj_of_v k; U64.v_inj r (obj_of k)

let below_top (m: M.mheap) (f: nat)
  : Lemma (requires FWA.head_ok m f /\ 1 <= f)
          (ensures pos (f - 1) + 8 < heap_size /\ f < msize /\ (3 <= f ==> pos (f - 3) + 8 < heap_size))
  = brep_size m; brep_block m 0; msize_pos f; base_facts ()

/// akhil's allocation of one field from the bottom block.
#push-options "--z3rlimit 40"
let alloc1 (ph: T.phase U64.t) (g: heap) (s: U64.t) (m: M.mheap) (f: nat)
  : Lemma (requires brepr m g /\ FWA.head_ok m f /\ 3 <= f /\ U64.v s == base + 8)
          (ensures (let r = GC.Spec.Allocator.Phase.alloc_at (gph ph) g s 1 (tg 0) in
                    pos (f - 1) + 8 < heap_size /\
                    r.GC.Spec.Allocator.fp_out == s /\ r.GC.Spec.Allocator.obj_out == obj_of (f - 1) /\
                    brepr (FWA.split m f 1 0 (T.colour_at ffk ph (f - 1))) r.GC.Spec.Allocator.heap_out))
  = FWA.head_word g m f;
    FWA.fp_obj s;
    let obj : obj_addr = s in
    let col = GC.Spec.Allocator.alloc_color (gph ph) g obj 1 in
    FWA.search_head ph g s m f 1 0;
    FWA.block_split g s m f 1 col 0 (GC.Spec.Allocator.spec_next_fp g obj);
    FWA.alloc_col ph g s m f 1;
    FWA.colour_rule ph (f - 1);
    FWA.alloc_repr g m f 1 col 0;
    below_top m f;
    let r = GC.Spec.Allocator.Phase.alloc_at (gph ph) g s 1 (tg 0) in
    obj_eq r.GC.Spec.Allocator.obj_out (f - 1)
#pop-options

/// **One promotion**: the copy at `f - 1`, in the colour rule's colour, its
/// field the young block's.
#push-options "--z3rlimit 40"
let promo1 (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (y: M.mheap) (o: nat)
           (g: heap) (s: U64.t) (m: M.mheap) (f: nat)
  : Lemma (requires 8 * o + 8 < pow2 64 /\ 3 <= f /\ pos (f - 1) + 8 < heap_size /\
                    brepr m g /\ FWA.head_ok m f /\ U64.v s == base + 8 /\
                    Y.yrepr y ms /\ M.is_block y o /\ M.wz_of y o == 1 /\ M.tag_of y o == 0 /\
                    minor_tag ms (PC.yobj o) == 0)
          (ensures (let (g2, s2, o2) = P.promote_object (ptal ph st0) ms g (PC.yobj o) s 1 in
                    o2 == obj_of (f - 1) /\ s2 == s /\
                    brepr (promoted m f (T.colour_at ffk ph (f - 1)) (M.field y o 0)) g2))
  = alloc1 ph g s m f;
    ptag ms (PC.yobj o);
    ptal_alloc ph st0 g s 1 (tg 0);
    let col = T.colour_at ffk ph (f - 1) in
    let r = GC.Spec.Allocator.Phase.alloc_at (gph ph) g s 1 (tg 0) in
    let g1 = r.GC.Spec.Allocator.heap_out in
    let m1 = FWA.split m f 1 0 col in
    FWA.split_def m f 1 0 col;
    brep_size m; brep_block m 0;
    assert (M.is_block m1 (f - 1) /\ M.wz_of m1 (f - 1) == 1);
    assert (M.is_block (cabs g1) (f - 1) /\ M.wz_of (cabs g1) (f - 1) == 1);
    PC.copy_cabs y ms o g1 (f - 1);
    fields1 y o;
    FS1.fill_heq m1 (cabs g1) (f - 1) [M.field y o 0]
#pop-options

/// ---------------------------------------------------------------------------
/// akhil's promotion, traced
/// ---------------------------------------------------------------------------

/// A new nursery object is promoted and queued.
let fwd_new (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (x: U64.t)
  : Lemma (requires Seq.mem x (minor_objects ms) /\ ~(is_infix_in_minor ms x) /\ cs.P.fwd x == 0UL /\
                    minor_wosize ms x == 1 /\
                    (let (_, _, o) = P.promote_object a ms cs.P.major x cs.P.st 1 in o <> 0UL))
          (ensures (let (g', s', o) = P.promote_object a ms cs.P.major x cs.P.st 1 in
                    P.forward_one a ms cs x ==
                    { P.major = g'; P.st = s'; P.fwd = extend_forwarding cs.P.fwd x o;
                      P.queue = Seq.append cs.P.queue (Seq.create 1 x) }))
  = ()

/// A word that is no nursery address is left alone.
let fwd_out (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (u: U64.t)
  : Lemma (requires out u) (ensures P.forward_one a ms cs u == cs)
  = out_none ms u

/// Scanning a one-field object whose field is no nursery address.
#push-options "--fuel 2"
let ff_one (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (x: U64.t)
  : Lemma (requires minor_scan_wosize ms x == 1 /\ out (to_minor_offset (minor_read_field ms x 0)))
          (ensures P.forward_fields a ms cs x 0 (minor_scan_wosize ms x) == cs)
  = fwd_out a ms cs (to_minor_offset (minor_read_field ms x 0))
#pop-options

/// Scanning any queued object leaves the state alone.
[@@"opaque_to_smt"]
let scan_noop (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) : prop =
  forall (j: nat). j < Seq.length cs.P.queue ==>
    P.forward_fields a ms cs (Seq.index cs.P.queue j) 0 (minor_scan_wosize ms (Seq.index cs.P.queue j)) == cs

let scan_noop_at (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (j: nat)
  : Lemma (requires scan_noop a ms cs /\ j < Seq.length cs.P.queue)
          (ensures P.forward_fields a ms cs (Seq.index cs.P.queue j) 0 (minor_scan_wosize ms (Seq.index cs.P.queue j)) == cs)
  = reveal_opaque (`%scan_noop) (scan_noop a ms cs)

#push-options "--fuel 1"
let scan_step (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (sc: nat) (n: Prims.pos)
  : Lemma (requires sc < Seq.length cs.P.queue)
          (ensures P.scan a ms cs sc n ==
                   P.scan a ms (P.forward_fields a ms cs (Seq.index cs.P.queue sc) 0
                                  (minor_scan_wosize ms (Seq.index cs.P.queue sc))) (sc + 1) (n - 1))
  = ()

let scan_stop (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (sc n: nat)
  : Lemma (requires n = 0 \/ sc >= Seq.length cs.P.queue) (ensures P.scan a ms cs sc n == cs)
  = ()
#pop-options

let rec scan_id (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (sc n: nat)
  : Lemma (requires scan_noop a ms cs) (ensures P.scan a ms cs sc n == cs) (decreases n)
  = if n = 0 || sc >= Seq.length cs.P.queue then scan_stop a ms cs sc n
    else begin
      let n' : nat = n - 1 in
      scan_step a ms cs sc n;
      scan_noop_at a ms cs sc;
      scan_id a ms cs (sc + 1) n'
    end

/// The roots, as the promotion reads them: Y2, then Y1.
let roots2 (r: seq U64.t) : prop = Seq.length r == 2 /\ Seq.index r 0 == yo2 /\ Seq.index r 1 == yo1

#push-options "--fuel 3"
let froots (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (r: seq U64.t)
  : Lemma (requires roots2 r)
          (ensures P.forward_roots a ms cs r 0 == P.forward_one a ms (P.forward_one a ms cs yo2) yo1)
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// The whole promotion
/// ---------------------------------------------------------------------------

/// The nursery, and the major heap's bottom block, the promotion starts from.
[@@"opaque_to_smt"]
let pre2 (ms: minor_state) (v w: M.value) (g: heap) (s: U64.t) (m: M.mheap) (f: nat) : prop =
  ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ hv v /\ hv w /\ storable_w v /\ storable_w w /\
  brepr m g /\ FWA.head_ok m f /\ 7 <= f /\ U64.v s == base + 8

let pre2_def (ms: minor_state) (v w: M.value) (g: heap) (s: U64.t) (m: M.mheap) (f: nat)
  : Lemma (pre2 ms v w g s m f <==>
           (ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ hv v /\ hv w /\ storable_w v /\ storable_w w /\
            brepr m g /\ FWA.head_ok m f /\ 7 <= f /\ U64.v s == base + 8))
  = reveal_opaque (`%pre2) (pre2 ms v w g s m f)

/// The colours of the two copies.
let c1 (ph: T.phase U64.t) (f: nat) : M.colour = T.colour_at ffk ph (sub f 1)
let c2 (ph: T.phase U64.t) (f: nat) : M.colour = T.colour_at ffk ph (sub f 3)

/// The model after both promotions: Y2's copy at `f - 1`, Y1's at `f - 3`.
let m2 (ph: T.phase U64.t) (v w: M.value) (m: M.mheap) (f: nat{7 <= f}) : M.mheap =
  promoted (promoted m f (c1 ph f) w) (f - 2) (c2 ph f) v

#push-options "--fuel 2"
let stor1 (v: M.value)
  : Lemma (requires storable_w v) (ensures L.length [v] == 1 /\ R.storable_all byte_rep [v])
  = ()
#pop-options

/// The model after the first promotion is again a bottom block of `f - 2`.
#push-options "--z3rlimit 40"
let head_after (m: M.mheap) (f: nat) (col: M.colour) (v: M.value)
  : Lemma (requires FWA.head_ok m f /\ 5 <= f /\ storable_w v)
          (ensures FWA.head_ok (promoted m f col v) (f - 2))
  = FWA.split_ok m f 1 0 col;
    FWA.split_def m f 1 0 col;
    brep_size m; brep_block m 0;
    let m1 = FWA.split m f 1 0 col in
    assert (M.is_block m1 (f - 1) /\ M.wz_of m1 (f - 1) == 1);
    stor1 v;
    FS1.fill_same_shape m1 (f - 1) [v]
#pop-options

let nursery (ms: minor_state) (v w: M.value)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ hv v /\ hv w)
          (ensures Seq.mem yo1 (minor_objects ms) /\ Seq.mem yo2 (minor_objects ms) /\
                   minor_wosize ms yo1 == 1 /\ minor_wosize ms yo2 == 1 /\
                   minor_tag ms yo1 == 0 /\ minor_tag ms yo2 == 0 /\
                   minor_scan_wosize ms yo1 == 1 /\ minor_scan_wosize ms yo2 == 1 /\
                   ~(is_infix_in_minor ms yo1) /\ ~(is_infix_in_minor ms yo2) /\
                   out (to_minor_offset (minor_read_field ms yo1 0)) /\
                   out (to_minor_offset (minor_read_field ms yo2 0)) /\
                   M.is_block (YW.ym2 v w) 0 /\ M.is_block (YW.ym2 v w) 2 /\
                   M.wz_of (YW.ym2 v w) 0 == 1 /\ M.wz_of (YW.ym2 v w) 2 == 1 /\
                   M.tag_of (YW.ym2 v w) 0 == 0 /\ M.tag_of (YW.ym2 v w) 2 == 0 /\
                   M.field (YW.ym2 v w) 0 0 == v /\ M.field (YW.ym2 v w) 2 0 == w)
  = yo_v ();
    ym2_facts v w;
    one_block ms v w 0;
    one_block ms v w 2;
    field_out ms v w 0;
    field_out ms v w 2;
    LV.tmo_id (minor_read_field ms yo1 0);
    LV.tmo_id (minor_read_field ms yo2 0)

let obj_ne (a b: nat) : Lemma (requires a <> b /\ pos a + 8 < heap_size /\ pos b + 8 < heap_size)
                              (ensures obj_of a <> obj_of b /\ obj_of a <> 0UL)
  = obj_of_v a; obj_of_v b

/// The object address of model block `k`, guarded.
let objp (k: nat) : U64.t = if pos k + 8 < heap_size then obj_of k else 0UL

let objp_facts (k j: nat)
  : Lemma (requires pos k + 8 < heap_size /\ pos j + 8 < heap_size /\ k <> j)
          (ensures objp k == obj_of k /\ maddr (objp k) == k /\ objp k <> 0UL /\ objp k <> objp j)
  = obj_ne k j; maddr_obj k;
    assert (objp k == obj_of k);
    assert (objp j == obj_of j)

let cs_init (#s: Type0) (g: heap) (st: s) : P.gstate s =
  { P.major = g; P.st = st; P.fwd = empty_forwarding; P.queue = Seq.empty }

/// The first promotion: Y2, to `f - 1`.
#push-options "--z3rlimit 40"
let prom_first (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (v w: M.value)
               (g: heap) (s: U64.t) (m: M.mheap) (f: nat)
  : Lemma (requires 7 <= f /\ pre2 ms v w g s m f)
          (ensures (let cs1 = P.forward_one (ptal ph st0) ms (cs_init g s) yo2 in
                    cs1.P.st == s /\ cs1.P.fwd == extend_forwarding empty_forwarding yo2 (objp (f - 1)) /\
                    cs1.P.queue == Seq.append Seq.empty (Seq.create 1 yo2) /\
                    brepr (promoted m f (c1 ph f) w) cs1.P.major))
  = pre2_def ms v w g s m f;
    let y = YW.ym2 v w in
    nursery ms v w;
    yo_v ();
    below_top m f;
    objp_facts (f - 1) (f - 3);
    promo1 ph st0 ms y 2 g s m f;
    fwd_new (ptal ph st0) ms (cs_init g s) yo2
#pop-options

/// The second promotion: Y1, to `f - 3`.
let prom_second (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (v w: M.value)
                 (s: U64.t) (m: M.mheap) (f: nat) (cs1: P.gstate U64.t)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ hv v /\ hv w /\ storable_w v /\ storable_w w /\
                    FWA.head_ok m f /\ 7 <= f /\ U64.v s == base + 8 /\
                    cs1.P.st == s /\ cs1.P.fwd == extend_forwarding empty_forwarding yo2 (objp (f - 1)) /\
                    cs1.P.queue == Seq.append Seq.empty (Seq.create 1 yo2) /\
                    brepr (promoted m f (c1 ph f) w) cs1.P.major)
          (ensures (let cs2 = P.forward_one (ptal ph st0) ms cs1 yo1 in
                    cs2.P.st == s /\
                    cs2.P.fwd == extend_forwarding (extend_forwarding empty_forwarding yo2 (objp (f - 1))) yo1 (objp (f - 3)) /\
                    cs2.P.queue == Seq.append (Seq.append Seq.empty (Seq.create 1 yo2)) (Seq.create 1 yo1) /\
                    brepr (m2 ph v w m f) cs2.P.major))
  = let y = YW.ym2 v w in
    nursery ms v w;
    yo_v ();
    below_top m f;
    objp_facts (f - 3) (f - 1);
    head_after m f (c1 ph f) w;
    below_top (promoted m f (c1 ph f) w) (f - 2);
    promo1 ph st0 ms y 0 cs1.P.major s (promoted m f (c1 ph f) w) (f - 2);
    fwd_new (ptal ph st0) ms cs1 yo1

/// The scan finds nothing to forward.
let scan_noop_intro (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s)
  : Lemma (requires forall (j: nat). j < Seq.length cs.P.queue ==>
             P.forward_fields a ms cs (Seq.index cs.P.queue j) 0 (minor_scan_wosize ms (Seq.index cs.P.queue j)) == cs)
          (ensures scan_noop a ms cs)
  = reveal_opaque (`%scan_noop) (scan_noop a ms cs)

/// A queued object the scan leaves alone: one field, not a young pointer
/// (sealed: the byte reads behind it slow every query that sees them).
[@@"opaque_to_smt"]
let quiet (ms: minor_state) (x: U64.t) : prop =
  minor_scan_wosize ms x == 1 /\ out (to_minor_offset (minor_read_field ms x 0))

let quiet_intro (ms: minor_state) (x: U64.t)
  : Lemma (requires minor_scan_wosize ms x == 1 /\ out (to_minor_offset (minor_read_field ms x 0)))
          (ensures quiet ms x)
  = reveal_opaque (`%quiet) (quiet ms x)

/// One queued object, scanned.
let at_q (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s) (j: nat)
  : Lemma (requires j < Seq.length cs.P.queue /\ quiet ms (Seq.index cs.P.queue j))
          (ensures P.forward_fields a ms cs (Seq.index cs.P.queue j) 0 (minor_scan_wosize ms (Seq.index cs.P.queue j)) == cs)
  = reveal_opaque (`%quiet) (quiet ms (Seq.index cs.P.queue j));
    ff_one a ms cs (Seq.index cs.P.queue j)

let scan2_core (#s: Type0) (a: P.tal s) (ms: minor_state) (cs: P.gstate s)
  : Lemma (requires Seq.length cs.P.queue == 2 /\ Seq.index cs.P.queue 0 == yo2 /\ Seq.index cs.P.queue 1 == yo1 /\
                    quiet ms yo1 /\ quiet ms yo2)
          (ensures scan_noop a ms cs)
  = let one (j: nat)
      : Lemma (j < Seq.length cs.P.queue ==>
               P.forward_fields a ms cs (Seq.index cs.P.queue j) 0 (minor_scan_wosize ms (Seq.index cs.P.queue j)) == cs)
      = if j = 0 then at_q a ms cs 0
        else if j = 1 then at_q a ms cs 1
        else () in
    FStar.Classical.forall_intro one;
    scan_noop_intro a ms cs

let scan2 (#s: Type0) (a: P.tal s) (ms: minor_state) (v w: M.value) (cs: P.gstate s)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ hv v /\ hv w /\
                    Seq.length cs.P.queue == 2 /\ Seq.index cs.P.queue 0 == yo2 /\ Seq.index cs.P.queue 1 == yo1)
          (ensures scan_noop a ms cs)
  = nursery ms v w;
    quiet_intro ms yo1;
    quiet_intro ms yo2;
    scan2_core a ms cs

/// **akhil's promotion of Y2 then Y1.**
#push-options "--z3rlimit 40"
let promote2 (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (v w: M.value)
             (g: heap) (s: U64.t) (m: M.mheap) (f: nat) (r: seq U64.t)
  : Lemma (requires 7 <= f /\ pre2 ms v w g s m f /\ roots2 r)
          (ensures (let cs = P.promote (ptal ph st0) ms g s r in
                    Seq.length cs.P.queue == 2 /\ Seq.index cs.P.queue 0 == yo2 /\ Seq.index cs.P.queue 1 == yo1 /\
                    cs.P.fwd yo2 == objp (f - 1) /\ cs.P.fwd yo1 == objp (f - 3) /\
                    cs.P.st == s /\ brepr (m2 ph v w m f) cs.P.major))
  = pre2_def ms v w g s m f;
    let a = ptal ph st0 in
    nursery ms v w;
    prom_first ph st0 ms v w g s m f;
    let cs1 = P.forward_one a ms (cs_init g s) yo2 in
    prom_second ph st0 ms v w s m f cs1;
    let cs2 = P.forward_one a ms cs1 yo1 in
    froots a ms (cs_init g s) r;
    assert (Seq.index cs2.P.queue 0 == yo2 /\ Seq.index cs2.P.queue 1 == yo1 /\ Seq.length cs2.P.queue == 2);
    scan2 a ms v w cs2;
    scan_id a ms cs2 0 (Seq.length (minor_objects ms))
#pop-options

/// ---------------------------------------------------------------------------
/// No promotion fails
/// ---------------------------------------------------------------------------

#push-options "--fuel 2"
let replay01 (#s: Type0) (a: P.tal s) (ms: minor_state) (g0: heap) (st0: s) (q: seq U64.t)
  : Lemma (requires Seq.length q == 2)
          (ensures PR.replay a ms g0 st0 q 0 == (g0, st0) /\
                   PR.replay a ms g0 st0 q 1 ==
                     (let (g2, s2, _) = PR.promote_at a ms g0 st0 (Seq.index q 0) in (g2, s2)))
  = ()
#pop-options

let po (#s: Type0) (a: P.tal s) (ms: minor_state) (g: heap) (x: U64.t) (st: s) : GTot (heap & s & U64.t) =
  P.promote_object a ms g x st 1
let po_h (#s: Type0) (r: heap & s & U64.t) : heap = Mktuple3?._1 r
let po_s (#s: Type0) (r: heap & s & U64.t) : s = Mktuple3?._2 r
let po_o (#s: Type0) (r: heap & s & U64.t) : U64.t = Mktuple3?._3 r

#push-options "--fuel 2"
let fails01 (#s: Type0) (a: P.tal s) (ms: minor_state) (g0: heap) (st0: s) (q: seq U64.t) (x: U64.t)
  : Lemma (requires Seq.length q == 2 /\ minor_wosize ms x == 1 /\ minor_wosize ms (Seq.index q 0) == 1)
          (ensures (PR.fails_at a ms g0 st0 q 0 x <==> po_o (po a ms g0 x st0) == 0UL) /\
                   (PR.fails_at a ms g0 st0 q 1 x <==>
                      (let r0 = po a ms g0 (Seq.index q 0) st0 in po_o (po a ms (po_h r0) x (po_s r0)) == 0UL)))
  = ()
#pop-options

let pat (#s: Type0) (a: P.tal s) (ms: minor_state) (g: heap) (st: s) (x: U64.t)
  : Lemma (requires minor_wosize ms x == 1) (ensures PR.promote_at a ms g st x == P.promote_object a ms g x st 1)
  = ()

let inst_ne (q: seq U64.t) (k: nat) (x: U64.t) (j: nat)
  : Lemma (requires k <= Seq.length q /\ (forall (i: nat). i < k ==> Seq.index q i =!= x) /\ j < k)
          (ensures Seq.index q j =!= x)
  = ()

/// Every first promotion succeeds; so does Y1's after Y2's.
#push-options "--z3rlimit 40"
let first_ok (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (v w: M.value)
             (g: heap) (s: U64.t) (m: M.mheap) (f: nat) (o: nat)
  : Lemma (requires 7 <= f /\ pre2 ms v w g s m f /\ (o == 0 \/ o == 2))
          (ensures 8 * o + 8 < pow2 64 /\ po_o (po (ptal ph st0) ms g (PC.yobj o) s) <> 0UL)
  = pre2_def ms v w g s m f;
    nursery ms v w;
    yo_v ();
    below_top m f;
    objp_facts (f - 1) (f - 3);
    promo1 ph st0 ms (YW.ym2 v w) o g s m f

let second_ok (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (v w: M.value)
              (g: heap) (s: U64.t) (m: M.mheap) (f: nat)
  : Lemma (requires 7 <= f /\ pre2 ms v w g s m f)
          (ensures (let r0 = po (ptal ph st0) ms g yo2 s in po_o (po (ptal ph st0) ms (po_h r0) yo1 (po_s r0)) <> 0UL))
  = pre2_def ms v w g s m f;
    let y = YW.ym2 v w in
    nursery ms v w;
    yo_v ();
    below_top m f;
    promo1 ph st0 ms y 2 g s m f;
    let (g1, s1, _) = P.promote_object (ptal ph st0) ms g yo2 s 1 in
    head_after m f (c1 ph f) w;
    below_top (promoted m f (c1 ph f) w) (f - 2);
    objp_facts (f - 3) (f - 1);
    promo1 ph st0 ms y 0 g1 s1 (promoted m f (c1 ph f) w) (f - 2)
#pop-options

let no_fail1 (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (v w: M.value)
             (g: heap) (s: U64.t) (m: M.mheap) (f: nat) (q: seq U64.t) (x: U64.t)
  : Lemma (requires 7 <= f /\ pre2 ms v w g s m f /\ Seq.length q == 2 /\ Seq.index q 0 == yo2 /\ x == yo1 /\
                    minor_wosize ms yo1 == 1 /\ minor_wosize ms yo2 == 1)
          (ensures ~(PR.fails_at (ptal ph st0) ms g s q 1 x))
  = pre2_def ms v w g s m f;
    fails01 (ptal ph st0) ms g s q x;
    second_ok ph st0 ms v w g s m f

let no_fail2 (q: seq U64.t) (k: nat) (x: U64.t)
  : Lemma (requires Seq.length q == 2 /\ Seq.index q 0 == yo2 /\ Seq.index q 1 == yo1 /\ k == 2 /\
                    (x == yo1 \/ x == yo2) /\ (forall (j: nat). j < k ==> Seq.index q j =!= x))
          (ensures False)
  = assert (Seq.index q 0 =!= x);
    assert (Seq.index q 1 =!= x)

#push-options "--z3rlimit 40"
let no_fail (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (v w: M.value)
            (g: heap) (s: U64.t) (m: M.mheap) (f: nat) (q: seq U64.t) (k: nat) (x: U64.t)
  : Lemma (requires 7 <= f /\ pre2 ms v w g s m f /\ Seq.length q == 2 /\ Seq.index q 0 == yo2 /\ Seq.index q 1 == yo1 /\
                    k <= 2 /\ Seq.mem x (minor_objects ms) /\ (forall (j: nat). j < k ==> Seq.index q j =!= x))
          (ensures ~(PR.fails_at (ptal ph st0) ms g s q k x))
  = let a = ptal ph st0 in
    if k = 0 then begin
      pre2_def ms v w g s m f;
      nursery ms v w;
      yo_v ();
      only_two ms v w x;
      fails01 a ms g s q x;
      if x = yo2 then first_ok ph st0 ms v w g s m f 2 else first_ok ph st0 ms v w g s m f 0
    end
    else if k = 1 then begin
      pre2_def ms v w g s m f;
      nursery ms v w;
      only_two ms v w x;
      inst_ne q k x 0;
      no_fail1 ph st0 ms v w g s m f q x
    end
    else begin
      assert (k == 2);
      pre2_def ms v w g s m f;
      only_two ms v w x;
      no_fail2 q k x
    end
#pop-options

let no_wit (ph: T.phase U64.t) (st0: ffst) (ms: minor_state) (v w: M.value) (live: U64.t -> prop)
           (g: heap) (s: U64.t) (m: M.mheap) (f: nat) (q: seq U64.t)
  : Lemma (requires 7 <= f /\ pre2 ms v w g s m f /\ Seq.length q == 2 /\ Seq.index q 0 == yo2 /\ Seq.index q 1 == yo1)
          (ensures ~(PR.wit (ptal ph st0) ms live g s q))
  = let aux (k: nat) (x: U64.t)
      : Lemma (~(k <= Seq.length q /\ Seq.mem x (minor_objects ms) /\ ~(is_infix_in_minor ms x) /\
                 minor_wosize ms x > 0 /\ live x /\ (forall (j: nat). j < k ==> Seq.index q j =!= x) /\
                 PR.fails_at (ptal ph st0) ms g s q k x))
      = FStar.Classical.move_requires (no_fail ph st0 ms v w g s m f q k) x in
    FStar.Classical.forall_intro_2 aux

/// ---------------------------------------------------------------------------
/// The pointer update writes nothing
/// ---------------------------------------------------------------------------

/// Every field word of the object at `obj` is no nursery address.
let fout (g: heap) (obj: U64.t) (wz: nat) : prop =
  forall (j: nat). j < wz /\ U64.v obj + j * 8 + 8 <= heap_size /\ (U64.v obj + j * 8) % 8 = 0 ==>
    out (read_word g (U64.uint_to_t (U64.v obj + j * 8)))

#push-options "--fuel 1 --z3rlimit 40"
let rec uop_out (g: heap) (obj: U64.t) (wz: nat) (fwd: forwarding_map) (i: nat)
  : Lemma (requires fout g obj wz) (ensures update_object_pointers g obj wz fwd i == g) (decreases (wz - i))
  = if i < wz then begin
      let fo = U64.v obj + i * 8 in
      if fo + 8 <= heap_size && fo % 8 = 0 then begin
        update_object_pointers_step g obj wz fwd i;
        LV.tmo_id (read_word g (U64.uint_to_t fo));
        out_none (GC.Spec.Top.FFWMinor0.ms0) (read_word g (U64.uint_to_t fo))
      end;
      uop_out g obj wz fwd (i + 1)
    end
#pop-options

#push-options "--fuel 1"
let rec uwa_out (g: heap) (objs: seq obj_addr) (upd: obj_addr -> GTot bool) (fwd: forwarding_map) (idx: nat)
  : Lemma (requires forall (x: obj_addr). Seq.mem x objs ==> fout g x (U64.v (wosize_of_object x g)))
          (ensures update_walk_aux g objs upd fwd idx == g) (decreases (Seq.length objs - idx))
  = if idx < Seq.length objs then begin
      let obj = Seq.index objs idx in
      Seq.lemma_index_is_nth objs idx;
      Seq.contains_intro objs idx obj;
      uop_out g obj (U64.v (wosize_of_object obj g)) fwd 0;
      uwa_out g objs upd fwd (idx + 1)
    end
#pop-options

/// Every word of a model heap's bodies is no nursery address.
let body_hv (m: M.mheap) : prop = forall (w: nat). hv (m.M.body w)

let hv_out' (v: M.value) : Lemma (requires hv v) (ensures out (concv v)) = hv_out v

/// The byte address of field `j` of the block at `b` (arithmetic only).
let hp_field (b j: nat) (x: U64.t)
  : Lemma (requires pos b + 8 == U64.v x /\ U64.v x + j * 8 + 8 <= heap_size)
          (ensures pos (b + 1 + j) < heap_size /\ hp (b + 1 + j) == U64.uint_to_t (U64.v x + j * 8))
  = assert (pos (b + 1 + j) == U64.v x + j * 8)

#push-options "--z3rlimit 40"
let fout_of (g: heap) (m: M.mheap) (x: obj_addr)
  : Lemma (requires brepr m g /\ brep_ok m /\ body_hv m /\ Seq.mem x (objects zero_addr g))
          (ensures fout g x (U64.v (wosize_of_object x g)))
  = obj_maddr g x;
    let b = maddr x in
    abs_header g b;
    let one (j: nat)
      : Lemma (j < U64.v (wosize_of_object x g) /\ U64.v x + j * 8 + 8 <= heap_size /\ (U64.v x + j * 8) % 8 = 0 ==>
               out (read_word g (U64.uint_to_t (U64.v x + j * 8))))
      = if j < U64.v (wosize_of_object x g) && U64.v x + j * 8 + 8 <= heap_size then begin
          let k = b + 1 + j in
          brep_size m;
          assert (M.covers m b k);
          brep_block m b;
          msize_pos k;
          FWW.words_of_heq g m k;
          if M.is_block m k then brep_uniq m b k k;
          hp_field b j x;
          hv_out' (m.M.body k)
        end in
    FStar.Classical.forall_intro one
#pop-options

/// **akhil's pointer update writes nothing here.**
let upw_out (free: free_def) (g: heap) (m: M.mheap) (fwd: forwarding_map)
  : Lemma (requires brepr m g /\ brep_ok m /\ body_hv m)
          (ensures update_pointers_with free g fwd == g)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (fout_of g m));
    uwa_out g (objects zero_addr g) (in_use free g) fwd 0

#push-options "--fuel 2"
let hv_promoted (m: M.mheap) (f: nat{3 <= f}) (col: M.colour) (v: M.value)
  : Lemma (requires body_hv m /\ hv v) (ensures body_hv (promoted m f col v))
  = FWA.split_def m f 1 0 col
#pop-options

/// ---------------------------------------------------------------------------
/// The roots
/// ---------------------------------------------------------------------------

#push-options "--fuel 2"
let rec no_young_roots (y: M.mheap) (rs: list M.value)
  : Lemma (requires GC.Spec.Top.FFWStep.no_young rs == true) (ensures Seq.equal (LV.yroots y rs) Seq.empty)
          (decreases rs)
  = match rs with
    | [] -> ()
    | v :: tl -> no_young_roots y tl
#pop-options

let young_word (ms: minor_state) (v w: M.value) (a: nat)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ (a == 0 \/ a == 2))
          (ensures Seq.equal (LV.yword (Y.ycabs ms) (M.VPtr (M.Young a))) (Seq.create 1 (PC.yobj a)))
  = ym2_facts v w;
    BM.yrepr_heq (YW.ym2 v w) ms;
    base_facts ();
    Y.msz ();
    assert (M.resolve (Y.ycabs ms) a == Some a)

/// The roots `Y2 :: Y1 :: majors`, as the promotion reads them.
#push-options "--z3rlimit 40 --fuel 2"
let roots_of2 (cw: T.cworld heap minor_state) (v w: M.value) (rest: list M.value)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) cw.T.cyng /\
                    cw.T.croots == M.VPtr (M.Young 2) :: M.VPtr (M.Young 0) :: rest /\
                    GC.Spec.Top.FFWStep.no_young rest == true /\ cw.T.crem == [])
          (ensures roots2 (LV.roots_of (BM.cview cw)))
  = let y = Y.ycabs cw.T.cyng in
    young_word cw.T.cyng v w 2;
    young_word cw.T.cyng v w 0;
    no_young_roots y rest;
    yo_v ();
    assert (Seq.equal (LV.yrem (cabs cw.T.cmaj) y []) Seq.empty);
    let r = LV.roots_of (BM.cview cw) in
    assert (LV.yroots y cw.T.croots ==
            Seq.append (LV.yword y (M.VPtr (M.Young 2))) (Seq.append (LV.yword y (M.VPtr (M.Young 0))) (LV.yroots y rest)));
    assert (Seq.length r == 2)
#pop-options

/// ---------------------------------------------------------------------------
/// **The collection**
/// ---------------------------------------------------------------------------

/// The forwarding: Y1 (at 0) to `f - 3`, Y2 (at 2) to `f - 1`.
let cps2 (f: nat) : list (nat & nat) = [(0, sub f 3); (2, sub f 1)]

#push-options "--fuel 3"
let copies2 (q: seq U64.t) (fwd: forwarding_map) (f: nat)
  : Lemma (requires Seq.length q == 2 /\ Seq.index q 0 == yo2 /\ Seq.index q 1 == yo1 /\
                    maddr (fwd yo2) == f - 1 /\ maddr (fwd yo1) == f - 3 /\ 3 <= f)
          (ensures Q0.copies q fwd (Seq.length q) == cps2 f)
  = assert_norm (Q.yof yo1 == 0 /\ Q.yof yo2 == 2)
#pop-options

let maddr_obj_of (k: nat) : Lemma (requires pos k + 8 < heap_size) (ensures maddr (obj_of k) == k)
  = maddr_obj k

/// An address that is not infix is covered when both nursery objects are
/// forwarded.
let cov2 (ms: minor_state) (v w: M.value) (cs: P.gstate U64.t) (addr: U64.t)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ cs.P.fwd yo1 <> 0UL /\ cs.P.fwd yo2 <> 0UL /\
                    ~(is_infix_in_minor ms addr))
          (ensures PR.covered ms cs addr)
  = PR.covered_def ms cs addr;
    FStar.Classical.move_requires (only_two ms v w) (resolve_minor ms addr)

/// The closure, from its four instances.
let closure_of4 (ms: minor_state) (cs: P.gstate U64.t) (r: seq U64.t)
  : Lemma (requires roots2 r /\
                    Seq.length cs.P.queue == 2 /\ Seq.index cs.P.queue 0 == yo2 /\ Seq.index cs.P.queue 1 == yo1 /\
                    PR.nsc ms yo1 == 1 /\ PR.nsc ms yo2 == 1 /\
                    PR.covered ms cs yo1 /\ PR.covered ms cs yo2 /\
                    PR.covered ms cs (PR.fld ms yo1 0) /\ PR.covered ms cs (PR.fld ms yo2 0))
          (ensures closure ms cs r)
  = let rt (i: nat) : Lemma (i < Seq.length r ==> PR.covered ms cs (Seq.index r i))
      = if i = 0 then () else if i = 1 then () else () in
    FStar.Classical.forall_intro rt;
    let sc (j i: nat)
      : Lemma (j < Seq.length cs.P.queue /\ j < Seq.length cs.P.queue /\ i < PR.nsc ms (Seq.index cs.P.queue j) ==>
               PR.covered ms cs (PR.fld ms (Seq.index cs.P.queue j) i))
      = if j = 0 then (if i = 0 then () else ())
        else if j = 1 then (if i = 0 then () else ())
        else () in
    FStar.Classical.forall_intro_2 sc

/// **Nothing is left unforwarded** (`FFMinor.closure`): both roots and both
/// fields are covered.
let closure2 (ms: minor_state) (v w: M.value) (cs: P.gstate U64.t) (r: seq U64.t)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ hv v /\ hv w /\ roots2 r /\
                    Seq.length cs.P.queue == 2 /\ Seq.index cs.P.queue 0 == yo2 /\ Seq.index cs.P.queue 1 == yo1 /\
                    cs.P.fwd yo1 <> 0UL /\ cs.P.fwd yo2 <> 0UL)
          (ensures closure ms cs r)
  = nursery ms v w;
    cov2 ms v w cs yo1; cov2 ms v w cs yo2;
    out_none ms (to_minor_offset (minor_read_field ms yo1 0));
    out_none ms (to_minor_offset (minor_read_field ms yo2 0));
    PR.fld_def ms yo1 0; PR.fld_def ms yo2 0;
    PR.nsc_def ms yo1; PR.nsc_def ms yo2;
    cov2 ms v w cs (PR.fld ms yo1 0); cov2 ms v w cs (PR.fld ms yo2 0);
    closure_of4 ms cs r

/// `pcollect`, unfolded.
let pcollect_unfold (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state)
  : Lemma (let ms = cw.T.cyng in
           let tl = ptal ph st in
           let g0 = gl cw.T.cmaj st in
           let w = BM.cview cw in
           let roots = LV.roots_of w in
           let cs = P.promote tl ms g0 st.fp roots in
           closure ms cs roots ==>
           pcollect ph st cw ==
             (let r = P.collect tl ms g0 st.fp roots in
              let cps = Q0.copies cs.P.queue cs.P.fwd (Seq.length cs.P.queue) in
              T.Done r.P.rmajor (tst r.P.rmajor r.P.rst) (L.map (T.fwdv (Y.ycabs ms) (F.fwd_of cps)) cw.T.croots)
                     (F.fwd_of cps)))
  = ()

let fwd_eq (q: seq U64.t) (fwd: forwarding_map) (f: nat)
  : Lemma (requires Q0.copies q fwd (Seq.length q) == cps2 f)
          (ensures F.fwd_of (Q0.copies q fwd (Seq.length q)) == F.fwd_of (cps2 f))
  = ()

/// The result, from the promotion's facts.
#push-options "--z3rlimit 40"
let assemble (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (v w: M.value) (m: M.mheap) (f: nat)
  : Lemma (requires 7 <= f /\
                    (let ms = cw.T.cyng in
                     let tl = ptal ph st in
                     let g0 = gl cw.T.cmaj st in
                     let wv = BM.cview cw in
                     let roots = LV.roots_of wv in
                     let cs = P.promote tl ms g0 st.fp roots in
                     closure ms cs roots /\
                     update_pointers_with tl.P.free cs.P.major cs.P.fwd == cs.P.major /\
                     cs.P.st == st.fp /\ brepr (m2 ph v w m f) cs.P.major /\
                     F.fwd_of (Q0.copies cs.P.queue cs.P.fwd (Seq.length cs.P.queue)) == F.fwd_of (cps2 f)))
          (ensures (match pcollect ph st cw with
                    | T.Done h' st' rs fwd ->
                      brepr (m2 ph v w m f) h' /\ st'.fp == st.fp /\ fwd == F.fwd_of (cps2 f) /\
                      rs == L.map (T.fwdv (Y.ycabs cw.T.cyng) (F.fwd_of (cps2 f))) cw.T.croots
                    | T.OutOfRoom -> False))
  = pcollect_unfold ph st cw
#pop-options

/// **The first-fit minor collection of Y1 and Y2**: `Done`, both promoted
/// once through first-fit (Y2 at `f - 1`, Y1 at `f - 3`, in the colour
/// rule's colours), their fields copied, the heap otherwise unchanged, the
/// roots rewritten through the forwarding.
#push-options "--z3rlimit 40"
let pcollect_two (ph: T.phase U64.t) (st: ffst) (cw: T.cworld heap minor_state) (v w: M.value)
                 (m: M.mheap) (f: nat) (rest: list M.value)
  : Lemma (requires 7 <= f /\ pre2 cw.T.cyng v w cw.T.cmaj st.fp m f /\ body_hv m /\
                    cw.T.croots == M.VPtr (M.Young 2) :: M.VPtr (M.Young 0) :: rest /\
                    GC.Spec.Top.FFWStep.no_young rest == true /\ cw.T.crem == [])
          (ensures (match pcollect ph st cw with
                    | T.Done h' st' rs fwd ->
                      brepr (m2 ph v w m f) h' /\ st'.fp == st.fp /\ fwd == F.fwd_of (cps2 f) /\
                      rs == L.map (T.fwdv (Y.ycabs cw.T.cyng) (F.fwd_of (cps2 f))) cw.T.croots
                    | T.OutOfRoom -> False))
  = pre2_def cw.T.cyng v w cw.T.cmaj st.fp m f; cabs_set_low cw.T.cmaj st.lo; pre2_def cw.T.cyng v w (gl cw.T.cmaj st) st.fp m f;
    let ms = cw.T.cyng in
    let tl = ptal ph st in
    let g0 = gl cw.T.cmaj st in
    cabs_set_low cw.T.cmaj st.lo;
    let wv = BM.cview cw in
    let roots = LV.roots_of wv in
    roots_of2 cw v w rest;
    promote2 ph st ms v w g0 st.fp m f roots;
    let cs = P.promote tl ms g0 st.fp roots in
    head_after m f (c1 ph f) w;
    head_after (promoted m f (c1 ph f) w) (f - 2) (c2 ph f) v;
    hv_promoted m f (c1 ph f) w;
    hv_promoted (promoted m f (c1 ph f) w) (f - 2) (c2 ph f) v;
    upw_out tl.P.free cs.P.major (m2 ph v w m f) cs.P.fwd;
    base_facts ();
    brep_size m; brep_block m 0; msize_pos (f - 1); msize_pos (f - 3);
    below_top m f;
    objp_facts (f - 1) (f - 3); objp_facts (f - 3) (f - 1);
    closure2 ms v w cs roots;
    copies2 cs.P.queue cs.P.fwd f;
    fwd_eq cs.P.queue cs.P.fwd f;
    assemble ph st cw v w m f
#pop-options

/// ---------------------------------------------------------------------------
/// The step of a run
/// ---------------------------------------------------------------------------

module FM0 = GC.Spec.Top.FFWMinor0
module FMd = GC.Spec.Top.FFWModel

/// The roots after the collection: Y2 and Y1 rewritten to their copies.
#push-options "--fuel 2"
let rec map_rest (y: M.mheap) (fwd: nat -> option nat) (rs: list M.value)
  : Lemma (requires GC.Spec.Top.FFWStep.no_young rs == true) (ensures L.map (T.fwdv y fwd) rs == rs) (decreases rs)
  = match rs with
    | [] -> ()
    | _ :: tl -> map_rest y fwd tl
#pop-options

#push-options "--fuel 3"
let roots_fwd (ms: minor_state) (v w: M.value) (f: nat) (rest: list M.value)
  : Lemma (requires ff_room /\ Y.yrepr (YW.ym2 v w) ms /\ GC.Spec.Top.FFWStep.no_young rest == true /\ 3 <= f)
          (ensures L.map (T.fwdv (Y.ycabs ms) (F.fwd_of (cps2 f))) (M.VPtr (M.Young 2) :: M.VPtr (M.Young 0) :: rest) ==
                   M.VPtr (M.Major (f - 1)) :: M.VPtr (M.Major (f - 3)) :: rest)
  = ym2_facts v w;
    BM.yrepr_heq (YW.ym2 v w) ms;
    assert (M.resolve (Y.ycabs ms) 2 == Some 2 /\ M.resolve (Y.ycabs ms) 0 == Some 0);
    map_rest (Y.ycabs ms) (F.fwd_of (cps2 f)) rest
#pop-options

/// The collection's result, at a described configuration.
#push-options "--z3rlimit 40"
let collect_facts (x: GC.Spec.Top.Run.config FS1.fc) (d: FS1.dsc) (v w: M.value) (rest: list M.value)
  : Lemma (requires FS1.holds x d /\ ff_room /\ d.FS1.dym == YW.ym2 v w /\
                    d.FS1.drt == M.VPtr (M.Young 2) :: M.VPtr (M.Young 0) :: rest /\
                    GC.Spec.Top.FFWStep.no_young rest == true /\ hv v /\ hv w /\ storable_w v /\ storable_w w /\
                    7 <= d.FS1.dst.f /\ body_hv (mk d.FS1.dst))
          (ensures (match pcollect x.ph x.ast x.w with
                    | T.Done h' st2 rs _ ->
                      brepr (m2 x.ph v w (mk d.FS1.dst) d.FS1.dst.f) h' /\ U64.v (st2 <: ffst).fp == base + 8 /\
                      rs == M.VPtr (M.Major (d.FS1.dst.f - 1)) :: M.VPtr (M.Major (d.FS1.dst.f - 3)) :: rest
                    | T.OutOfRoom -> False))
  = FS1.holds_def x d;
    let f = d.FS1.dst.f in
    let m = mk d.FS1.dst in
    let s : ffst = x.ast in
    FMd.okm_def m;
    assert (m.M.hd 0 == Some (FWA.free_hdr f));
    pre2_def x.w.cyng v w x.w.cmaj s.fp m f;
    pcollect_two x.ph s x.w v w m f rest;
    roots_fwd x.w.cyng v w f rest
#pop-options

/// **EMinor of Y1 and Y2**: both promoted (Y2 to `f - 1`, Y1 to `f - 3`, in
/// the colour rule's colours at the phase), the nursery reset, the roots
/// rewritten.
#push-options "--z3rlimit 40"
let step_minor2 (x: GC.Spec.Top.Run.config FS1.fc) (d: FS1.dsc) (v w: M.value) (rest: list M.value) (st': wst)
  : Lemma (requires FS1.holds x d /\ ff_room /\ d.FS1.dym == YW.ym2 v w /\
                    d.FS1.drt == M.VPtr (M.Young 2) :: M.VPtr (M.Young 0) :: rest /\
                    GC.Spec.Top.FFWStep.no_young rest == true /\ hv v /\ hv w /\ storable_w v /\ storable_w w /\
                    7 <= d.FS1.dst.f /\ body_hv (mk d.FS1.dst) /\
                    R.heq (m2 d.FS1.dph v w (mk d.FS1.dst) d.FS1.dst.f) (mk st'))
          (ensures FS1.holds (GC.Spec.Top.Run.step FS1.fc x GC.Spec.Top.Run.EMinor)
                     ({ d with FS1.dst = st'; FS1.dys = FM0.ms0; FS1.dym = M.empty_heap ywords;
                               FS1.drt = M.VPtr (M.Major (d.FS1.dst.f - 1)) :: M.VPtr (M.Major (d.FS1.dst.f - 3)) :: rest }))
  = let f = d.FS1.dst.f in
    let m = mk d.FS1.dst in
    collect_facts x d v w rest;
    FS1.holds_def x d;
    FMd.okm_def m;
    head_after m f (c1 x.ph f) w;
    head_after (promoted m f (c1 x.ph f) w) (f - 2) (c2 x.ph f) v;
    FS1.brep_of_heq (m2 x.ph v w m f) (mk st');
    FMd.okm_def (mk st');
    FM0.yreset_yinit x.w.cyng;
    Y.yinit_ok' ywords;
    FM0.yinit_ms0 ywords;
    let d' = { d with FS1.dst = st'; FS1.dys = FM0.ms0; FS1.dym = M.empty_heap ywords;
                      FS1.drt = M.VPtr (M.Major (f - 1)) :: M.VPtr (M.Major (f - 3)) :: rest } in
    match pcollect x.ph x.ast x.w with
    | T.Done h' st2 rs fwd ->
      let x' = GC.Spec.Top.Run.step FS1.fc x GC.Spec.Top.Run.EMinor in
      assert (x'.GC.Spec.Top.Run.w.T.cmaj == h' /\ x'.GC.Spec.Top.Run.w.T.cyng == Y.yreset x.w.cyng /\
              x'.GC.Spec.Top.Run.w.T.croots == rs /\ x'.GC.Spec.Top.Run.w.T.crem == [] /\
              x'.GC.Spec.Top.Run.ast == st2 /\ x'.GC.Spec.Top.Run.ph == x.ph /\ x'.GC.Spec.Top.Run.stopped == false);
      assert (brepr (mk st') h');
      assert (Y.yrepr (M.empty_heap ywords) FM0.ms0);
      assert (Y.yreset x.w.cyng == FM0.ms0);
      assert (U64.v (st2 <: ffst).fp == base + 8);
      assert (FMd.okm (mk st'));
      assert (x.ph == d.FS1.dph);
      FS1.holds_def x' d'
    | T.OutOfRoom -> ()
#pop-options

/// ---------------------------------------------------------------------------
/// The closed forms' words are no nursery address; the nursery is well formed
/// ---------------------------------------------------------------------------

let st_hv (st: wst) : prop = hv st.lk /\ hv st.a0 /\ hv st.a1 /\ hv st.c0 /\ hv st.d0

let mk_hv (st: wst) : Lemma (requires st_hv st) (ensures body_hv (mk st))
  = assert_norm (hv (M.infix_word 2))

#push-options "--fuel 2 --z3rlimit 40"
let ym2_ok (v w: M.value)
  : Lemma (requires ff_room /\ hv v /\ hv w)
          (ensures M.young_ok (YW.ym2 v w) /\ T.young_follow_ok (YW.ym2 v w) /\
                   (forall (y i b: nat). M.ptr_field (YW.ym2 v w) y i /\ M.field (YW.ym2 v w) y i == M.VPtr (M.Major b) ==>
                      (y == 0 /\ v == M.VPtr (M.Major b)) \/ (y == 2 /\ w == M.VPtr (M.Major b))))
  = ym2_facts v w;
    base_facts ()
#pop-options

let empty_ok (n: nat)
  : Lemma (M.young_ok (M.empty_heap n) /\ T.young_follow_ok (M.empty_heap n) /\
           (forall (y i b: nat). ~(M.ptr_field (M.empty_heap n) y i)))
  = ()

/// The collection's result is `Done`.
let done2 (x: GC.Spec.Top.Run.config FS1.fc) (d: FS1.dsc) (v w: M.value) (rest: list M.value)
  : Lemma (requires FS1.holds x d /\ ff_room /\ d.FS1.dym == YW.ym2 v w /\
                    d.FS1.drt == M.VPtr (M.Young 2) :: M.VPtr (M.Young 0) :: rest /\
                    GC.Spec.Top.FFWStep.no_young rest == true /\ hv v /\ hv w /\ storable_w v /\ storable_w w /\
                    7 <= d.FS1.dst.f /\ body_hv (mk d.FS1.dst))
          (ensures T.Done? (pcollect x.ph x.ast x.w))
  = FS1.holds_def x d;
    FMd.okm_def (mk d.FS1.dst);
    assert ((mk d.FS1.dst).M.hd 0 == Some (FWA.free_hdr d.FS1.dst.f));
    pre2_def x.w.cyng v w x.w.cmaj (x.ast <: ffst).fp (mk d.FS1.dst) d.FS1.dst.f;
    pcollect_two x.ph x.ast x.w v w (mk d.FS1.dst) d.FS1.dst.f rest
