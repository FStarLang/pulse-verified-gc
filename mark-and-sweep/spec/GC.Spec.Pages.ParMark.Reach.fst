/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Reach - what the model's heap view must satisfy
/// ---------------------------------------------------------------------------
///
/// The model (`GC.Spec.Pages.ParMark.Model`) sees the heap only through
/// `tst`, `tgt` and `nf`.  This module states what it needs of them
/// (`view_ok`), over a set `ok` of claimable objects, and the reachability
/// the mark computes: `reach p rts y`, from the root targets `rts` along
/// `edge`s, an edge from `x` to the target of one of its fields.
/// `GC.Spec.Pages.ParMark.Heap` proves `view_ok` for a heap, and that `reach`
/// is the heap graph's reachability.

module GC.Spec.Pages.ParMark.Reach

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Model

module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// `a` is the address of one of the fields of `x` that the mark scans.
let field_of (p: params) (x a: nat) : prop =
  x <= a /\ a < x + 8 * p.nf x /\ (a - x) % 8 == 0

noeq type reach_t (p: params) (rts: list nat) : nat -> Type =
  | RRoot : y:nat{L.mem y rts} -> reach_t p rts y
  | RStep : x:nat -> reach_t p rts x -> a:nat{field_of p x a} -> y:nat{p.tgt a == Some y} -> reach_t p rts y

/// Reachable from the root targets.
let reach (p: params) (rts: list nat) (y: nat) : prop = exists (r: reach_t p rts y). True

let reach_root (p: params) (rts: list nat) (y: nat)
  : Lemma (requires L.mem y rts) (ensures reach p rts y)
  = introduce exists (r: reach_t p rts y). True with (RRoot #p #rts y) and ()

let reach_step (p: params) (rts: list nat) (x a y: nat)
  : Lemma (requires reach p rts x /\ field_of p x a /\ p.tgt a == Some y) (ensures reach p rts y)
  = eliminate exists (r: reach_t p rts x). True
    with introduce exists (r': reach_t p rts y). True with (RStep #p #rts x r a y) and ()

/// The claimable objects.
noeq type view = {
  ok: nat -> prop;
  univ: list nat;       (* every claimable object (for the termination measure) *)
  maxnf: nat;           (* a bound on their fields *)
}

let view_ok (p: params) (v: view) (rts: list nat) : prop =
  (* a claimable object has its header's bit in the bitmap *)
  (forall (y: nat). v.ok y ==> y >= 8 /\ in_pages (y - 8) /\ p.nf y <= v.maxnf /\ L.mem y v.univ) /\
  (* the target of a field of a claimable object is claimable *)
  (forall (x a y: nat). v.ok x /\ field_of p x a /\ p.tgt a == Some y ==> v.ok y) /\
  (* the bitmap-first test: a word whose test address is a claimable
     object's header points to that object *)
  (forall (x a y: nat). v.ok x /\ field_of p x a /\ v.ok y /\ p.tst a == Some (y - 8) ==>
     p.tgt a == Some y) /\
  (* a word that is not a pointer has no target *)
  (forall (x a: nat). v.ok x /\ field_of p x a /\ p.tst a == None ==> p.tgt a == None) /\
  (* the root targets are claimable *)
  (forall (y: nat). L.mem y rts ==> v.ok y)

/// Reachable objects are claimable.
let rec reach_t_ok (p: params) (v: view) (rts: list nat) (y: nat) (r: reach_t p rts y)
  : Lemma (requires view_ok p v rts) (ensures v.ok y) (decreases r)
  = match r with
    | RRoot _ -> ()
    | RStep x r' a _ -> reach_t_ok p v rts x r'

let reach_ok (p: params) (v: view) (rts: list nat) (y: nat)
  : Lemma (requires view_ok p v rts /\ reach p rts y) (ensures v.ok y)
  = eliminate exists (r: reach_t p rts y). True
    with reach_t_ok p v rts y r

/// A set that holds the roots and is closed under edges holds everything
/// reachable.
let rec closed_reach_t (p: params) (rts: list nat) (m: nat -> prop) (y: nat) (r: reach_t p rts y)
  : Lemma (requires (forall (z: nat). L.mem z rts ==> m z) /\
                    (forall (x a z: nat). m x /\ field_of p x a /\ p.tgt a == Some z ==> m z))
          (ensures m y) (decreases r)
  = match r with
    | RRoot _ -> ()
    | RStep x r' a _ -> closed_reach_t p rts m x r'

let closed_reach (p: params) (rts: list nat) (m: nat -> prop) (y: nat)
  : Lemma (requires (forall (z: nat). L.mem z rts ==> m z) /\
                    (forall (x a z: nat). m x /\ field_of p x a /\ p.tgt a == Some z ==> m z) /\
                    reach p rts y)
          (ensures m y)
  = eliminate exists (r: reach_t p rts y). True
    with closed_reach_t p rts m y r

/// **The mark's result**: the bits are exactly the headers of the reachable
/// objects.
let marks_reach (p: params) (rts: list nat) (bs: Seq.seq FStar.UInt32.t) : prop =
  forall (a: nat). marked bs a <==> (exists (y: nat). reach p rts y /\ a == y - 8)
