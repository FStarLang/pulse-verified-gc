/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Init - the start satisfies the invariant
/// ---------------------------------------------------------------------------
///
/// `init_inv`: from an all-zero bitmap, the state the main thread builds
/// (the roots' targets claimed, their entries packed into packets in the pool,
/// the count set to the number of packets, every worker idle) satisfies
/// `Inv.inv`.  `mark_correct` puts the model together: after any
/// interleaving in which every worker has finished, the bits are exactly the
/// headers of the objects reachable from the roots.

module GC.Spec.Pages.ParMark.Init

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Bits
open GC.Spec.Pages.ParMark.Model
open GC.Spec.Pages.ParMark.Reach
open GC.Spec.Pages.ParMark.Inv

module U32 = FStar.UInt32
module Seq = FStar.Seq
module L = FStar.List.Tot
module Sf = GC.Spec.Pages.ParMark.Safety
module Co = GC.Spec.Pages.ParMark.Complete

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The bitmap has no bit set.
let no_marks (bs: Seq.seq U32.t) : prop =
  Seq.length bs == bm_len /\ (forall (a: nat). ~(marked bs a))

let roots_ok (v: view) (rts: list nat) : prop =
  forall (y: nat). L.mem y rts ==> v.ok y

/// ---------------------------------------------------------------------------
/// Claiming the roots
/// ---------------------------------------------------------------------------

let claimed (p: params) (bs: Seq.seq U32.t) (rts: list nat) : Seq.seq U32.t = fst (claim_roots p bs rts)
let root_entries (p: params) (bs: Seq.seq U32.t) (rts: list nat) : list entry = snd (claim_roots p bs rts)

#push-options "--fuel 1 --z3rlimit 40"
let rec claim_roots_marks (p: params) (v: view) (rts0: list nat) (bs: Seq.seq U32.t) (rts: list nat) (a: nat)
  : Lemma (requires view_ok p v rts0 /\ Seq.length bs == bm_len /\ (forall (y: nat). L.mem y rts ==> v.ok y))
          (ensures Seq.length (claimed p bs rts) == bm_len /\
                   (marked (claimed p bs rts) a <==> (marked bs a \/ (exists (y: nat). L.mem y rts /\ a == ybit y))))
          (decreases rts)
  = match rts with
    | [] -> ()
    | y :: rest ->
      assert (y >= 8 /\ in_pages (ybit y));
      if marked bs (ybit y) then claim_roots_marks p v rts0 bs rest a
      else begin
        set_bit_marked bs (ybit y) a;
        claim_roots_marks p v rts0 (set_bit bs (ybit y)) rest a
      end

/// The fields of a newly claimed root are in the root entries.
let rec claim_roots_cover (p: params) (v: view) (rts0: list nat) (bs: Seq.seq U32.t) (rts: list nat) (x a: nat)
  : Lemma (requires view_ok p v rts0 /\ Seq.length bs == bm_len /\ (forall (y: nat). L.mem y rts ==> v.ok y) /\
                    x >= 8 /\ marked (claimed p bs rts) (ybit x) /\ ~(marked bs (ybit x)) /\ field_of p x a)
          (ensures cl (root_entries p bs rts) a)
          (decreases rts)
  = match rts with
    | [] -> ()
    | y :: rest ->
      assert (y >= 8 /\ in_pages (ybit y));
      if marked bs (ybit y) then claim_roots_cover p v rts0 bs rest x a
      else begin
        let bs1 = set_bit bs (ybit y) in
        set_bit_marked bs (ybit y) (ybit x);
        cl_append (obj_entries p y) (root_entries p bs1 rest) a;
        if marked bs1 (ybit x) then begin
          assert (x == y);
          Sf.obj_entries_covers p y a
        end
        else claim_roots_cover p v rts0 bs1 rest x a
      end

/// The root entries lie in marked objects.
let rec claim_roots_ok (p: params) (v: view) (rts0: list nat) (bs: Seq.seq U32.t) (rts: list nat)
  : Lemma (requires view_ok p v rts0 /\ Seq.length bs == bm_len /\ (forall (y: nat). L.mem y rts ==> v.ok y))
          (ensures lok p v (claimed p bs rts) (root_entries p bs rts))
          (decreases rts)
  = match rts with
    | [] -> ()
    | y :: rest ->
      assert (y >= 8 /\ in_pages (ybit y));
      if marked bs (ybit y) then claim_roots_ok p v rts0 bs rest
      else begin
        let bs1 = set_bit bs (ybit y) in
        set_bit_marked bs (ybit y) (ybit y);
        claim_roots_ok p v rts0 bs1 rest;
        claim_roots_marks p v rts0 bs1 rest (ybit y);
        Sf.obj_entries_ok p v (claimed p bs1 rest) y;
        lok_append p v (claimed p bs1 rest) (obj_entries p y) (root_entries p bs1 rest)
      end
#pop-options

/// ---------------------------------------------------------------------------
/// Packing
/// ---------------------------------------------------------------------------

#push-options "--fuel 1 --z3rlimit 40"
let rec pack_cover (pkt: pos) (cur: list entry) (pool: list (list entry)) (es: list entry) (a: nat)
  : Lemma (ensures cp (pack pkt cur pool es) a == (cl cur a || cp pool a || cl es a)) (decreases es)
  = match es with
    | [] -> ()
    | e :: rest ->
      let cur' = e :: cur in
      if L.length cur' = pkt then pack_cover pkt [] (cur' :: pool) rest a
      else pack_cover pkt cur' pool rest a

let rec pack_ok (p: params) (v: view) (bs: Seq.seq U32.t) (pkt: pos) (cur: list entry)
  (pool: list (list entry)) (es: list entry)
  : Lemma (requires pool_ok p v bs pool /\ lok p v bs cur /\ lok p v bs es)
          (ensures pool_ok p v bs (pack pkt cur pool es)) (decreases es)
  = match es with
    | [] -> ()
    | e :: rest ->
      let cur' = e :: cur in
      if L.length cur' = pkt then pack_ok p v bs pkt [] (cur' :: pool) rest
      else pack_ok p v bs pkt cur' pool rest
#pop-options

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let lok_nil (p: params) (v: view) (bs: Seq.seq U32.t) : Lemma (lok p v bs []) = ()
let pool_ok_nil (p: params) (v: view) (bs: Seq.seq U32.t) : Lemma (pool_ok p v bs []) = ()
#pop-options

let init_shape (p: params) (bs0: Seq.seq U32.t) (rts: list nat)
  : Lemma (let s = init p bs0 rts in
           Seq.length s.ws == p.k /\ s.bs == claimed p bs0 rts /\
           s.pool == pack p.pkt [] [] (root_entries p bs0 rts) /\
           (forall (w: nat). w < p.k ==> Seq.index s.ws w == idle_w))
  = ()

#push-options "--z3rlimit 40"
let init_i2 (p: params) (v: view) (rts: list nat) (bs0: Seq.seq U32.t)
  : Lemma (requires view_ok p v rts /\ no_marks bs0) (ensures i2 p v (init p bs0 rts))
  = let s = init p bs0 rts in
    init_shape p bs0 rts;
    let aux (x a y: nat)
      : Lemma (requires v.ok x /\ marked s.bs (ybit x) /\ field_of p x a /\ p.tgt a == Some y)
              (ensures cp s.pool a)
      = claim_roots_cover p v rts bs0 rts x a;
        pack_cover p.pkt [] [] (root_entries p bs0 rts) a;
        Co.cl_empty a;
        Co.cp_empty a
    in
    FStar.Classical.forall_intro_3 (fun x a -> FStar.Classical.move_requires (aux x a))

/// **The start satisfies the invariant.**
let init_inv (p: params) (v: view) (rts: list nat) (bs0: Seq.seq U32.t)
  : Lemma (requires view_ok p v rts /\ no_marks bs0) (ensures inv p v rts (init p bs0 rts))
  = let s = init p bs0 rts in
    init_shape p bs0 rts;
    let bs = claimed p bs0 rts in
    FStar.Classical.forall_intro (claim_roots_marks p v rts bs0 rts);
    let m (a: nat) : Lemma (marked bs a ==> v.ok (a + 8) /\ reach p rts (a + 8))
      = if marked bs a then
          eliminate exists (y: nat). L.mem y rts /\ a == ybit y
          with begin
            assert (v.ok y /\ y >= 8);
            assert (a + 8 == y);
            reach_root p rts y
          end
    in
    FStar.Classical.forall_intro m;
    assert (i1 p v rts bs);
    claim_roots_ok p v rts bs0 rts;
    lok_nil p v bs;
    pool_ok_nil p v bs;
    pack_ok p v bs p.pkt [] [] (root_entries p bs0 rts);
    sum_const units idle_w p.k;
    assert (held_units s == 0);
    init_i2 p v rts bs0;
    inv_reveal p v rts s
#pop-options

/// ---------------------------------------------------------------------------
/// The model's theorem
/// ---------------------------------------------------------------------------

/// **The parallel mark is correct**: from an all-zero bitmap, after any
/// interleaving of the workers' steps that ends with every worker finished,
/// the bits are exactly the headers of the objects reachable from the roots;
/// and at every point, every set bit is the header of a reachable object.
let mark_correct (p: params) (v: view) (rts: list nat) (bs0: Seq.seq U32.t) (sched: list nat)
  : Lemma (requires view_ok p v rts /\ no_marks bs0)
          (ensures (let s = run p (init p bs0 rts) sched in
                    inv p v rts s /\
                    (forall (a: nat). marked s.bs a ==> reach p rts (a + 8)) /\
                    (all_done s ==> marks_reach p rts s.bs /\ Seq.length s.bs == bm_len)))
  = init_inv p v rts bs0;
    let s = run p (init p bs0 rts) sched in
    Sf.run_inv p v rts (init p bs0 rts) sched;
    inv_reveal p v rts s;
    FStar.Classical.move_requires (Co.all_done_marks p v rts) s
