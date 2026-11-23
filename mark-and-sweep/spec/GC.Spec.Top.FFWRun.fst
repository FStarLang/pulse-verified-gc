/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFWRun - what each event of a witness run asks
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  For a configuration described by `holds x d`
/// (GC.Spec.Top.FFWStep), the conditions of `run_ok` at one event (enabled,
/// in the style, the program's obligations) as statements about the
/// description's world `wd d`, one lemma per kind of event; and the values
/// the program may hold: a pointer to a root, or to a block one field away
/// from a root.

module GC.Spec.Top.FFWRun

open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteRep
open GC.Spec.Top.Run
open GC.Spec.Top.RunFacts
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFWState
open GC.Spec.Top.FFWStep
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module FSw = GC.Spec.Top.FFSweep
module FWS = GC.Spec.Top.FFWSweep
module Y = GC.Spec.Top.Young

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The conditions of `run_ok` at one event.
let ok_at (sty: style) (x: config fc) (e: event) : prop =
  enabled fc x e /\ style_ok sty x e /\ mutator_ok x e

/// ---------------------------------------------------------------------------
/// Reachability
/// ---------------------------------------------------------------------------

/// A block a root points to is reachable.
let reach_root (w: M.world) (a o: nat)
  : Lemma (requires L.memP (M.VPtr (M.Major a)) w.M.roots /\ M.resolve w.M.maj a == Some o)
          (ensures M.reachable w o)
  = let r : M.reach w o = M.RBase o () in ()

/// A block a reachable block's field points to is reachable.
let reach_edge (w: M.world) (o i a o': nat)
  : Lemma (requires M.reachable w o /\ M.ptr_field w.M.maj o i /\ M.field w.M.maj o i == M.VPtr (M.Major a) /\
                    M.resolve w.M.maj a == Some o')
          (ensures M.reachable w o')
  = let r = FStar.IndefiniteDescription.indefinite_description_ghost (M.reach w o) (fun _ -> True) in
    let r' : M.reach w o' = M.RStep o o' r () in ()

/// A young block a root points to is young-reachable.
let yreach_root (w: M.world) (a o: nat)
  : Lemma (requires L.memP (M.VPtr (M.Young a)) w.M.roots /\ M.resolve w.M.yng a == Some o)
          (ensures M.yreachable w o)
  = let r : M.yreach w o = M.YRoot o a () in ()

/// ---------------------------------------------------------------------------
/// The events
/// ---------------------------------------------------------------------------

let ok_alloc (sty: style) (x: config fc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires holds x d /\ (Sequential? sty ==> T.Idle? d.dph) /\ tag <> M.infix_tag /\ L.length vs == sz /\
                    fill_ok (wd d) tag vs /\ R.storable_all byte_rep vs)
          (ensures ok_at sty x (EAlloc sz tag vs))
  = reveal_holds ();
    mutator_wd x d (EAlloc sz tag vs)

let ok_yalloc (sty: style) (x: config fc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires holds x d /\ (Sequential? sty ==> T.Idle? d.dph) /\ tag <> M.infix_tag /\ L.length vs == sz /\
                    fill_ok (wd d) tag vs /\ R.storable_all byte_rep vs /\ Some? (Y.yalloc d.dys sz tag vs))
          (ensures ok_at sty x (EYoungAlloc sz tag vs))
  = reveal_holds ();
    mutator_wd x d (EYoungAlloc sz tag vs)

let en_write (sty: style) (x: config fc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires holds x d /\ (Sequential? sty ==> T.Idle? d.dph))
          (ensures enabled fc x (EWrite (M.Major o) i v) /\ style_ok sty x (EWrite (M.Major o) i v))
  = reveal_holds ();
    ()

let ok_write (sty: style) (x: config fc) (d: dsc) (o i: nat) (v: M.value)
  : Lemma (requires holds x d /\ (Sequential? sty ==> T.Idle? d.dph) /\
                    M.is_block (mk d.dst) o /\ M.reachable (wd d) o /\ i < M.wz_of (mk d.dst) o /\
                    M.tag_of (mk d.dst) o <> M.closure_tag /\ value_ok (wd d) v /\ storable_w v)
          (ensures ok_at sty x (EWrite (M.Major o) i v))
  = reveal_holds ();
    mutator_wd x d (EWrite (M.Major o) i v);
    en_write sty x d o i v

let ok_read (sty: style) (x: config fc) (d: dsc) (o i: nat)
  : Lemma (requires holds x d /\ (Sequential? sty ==> T.Idle? d.dph) /\
                    M.is_block (mk d.dst) o /\ M.reachable (wd d) o /\ i < M.wz_of (mk d.dst) o)
          (ensures ok_at sty x (ERead (M.Major o) i))
  = reveal_holds ();
    mutator_wd x d (ERead (M.Major o) i)

let ok_roots (sty: style) (x: config fc) (d: dsc) (rs: list M.value)
  : Lemma (requires holds x d /\ (Sequential? sty ==> T.Idle? d.dph) /\
                    (forall (v: M.value). L.memP v rs ==> value_ok (wd d) v) /\ R.storable_all byte_rep rs)
          (ensures ok_at sty x (ERoots rs))
  = reveal_holds ();
    mutator_wd x d (ERoots rs)

let ok_minor (sty: style) (x: config fc) (d: dsc)
  : Lemma (requires holds x d) (ensures ok_at sty x EMinor)
  = reveal_holds ();
    mutator_wd x d EMinor

let ok_start (sty: style) (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ d.dph == T.Idle) (ensures ok_at sty x EStart)
  = reveal_holds ();
    mutator_wd x d EStart

let ok_slice (sty: style) (x: config fc) (d: dsc) (t: nat)
  : Lemma (requires holds x d /\ d.dph == T.Marking /\ M.is_block (mk d.dst) t /\ M.col_of (mk d.dst) t == M.Grey)
          (ensures ok_at sty x ESlice)
  = reveal_holds ();
    mutator_wd x d ESlice;
    mark_done_wd x d

let ok_handover (sty: style) (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ d.dph == T.Marking /\ T.no_grey (mk d.dst))
          (ensures ok_at sty x EHandover)
  = reveal_holds ();
    mutator_wd x d EHandover;
    mark_done_wd x d

let not_done (o: nat) : Lemma (requires o + 1 < msize) (ensures FSw.ffdone (FWS.cur o) == false)
  = base_facts (); FWS.cur_v o; msize_pos (o + 1)

let is_done (_: unit) : Lemma (FSw.ffdone (FWS.cur msize) == true)
  = base_facts (); FWS.cur_v msize

let ok_sweep (sty: style) (x: config fc) (d: dsc) (o: nat)
  : Lemma (requires holds x d /\ d.dph == T.Sweeping (FWS.cur o) /\ o + 1 < msize)
          (ensures ok_at sty x ESweep)
  = reveal_holds ();
    mutator_wd x d ESweep;
    not_done o

let ok_end (sty: style) (x: config fc) (d: dsc)
  : Lemma (requires holds x d /\ d.dph == T.Sweeping (FWS.cur msize)) (ensures ok_at sty x EEnd)
  = reveal_holds ();
    mutator_wd x d EEnd;
    is_done ()

/// ---------------------------------------------------------------------------
/// Values
/// ---------------------------------------------------------------------------

let vint_ok (w: M.world) (n: int) : Lemma (value_ok w (M.VInt n)) = ()

let vmaj_ok (w: M.world) (a o: nat)
  : Lemma (requires M.resolve w.M.maj a == Some o /\ M.reachable w o) (ensures value_ok w (M.VPtr (M.Major a)))
  = ()

let vyng_ok (w: M.world) (a o: nat)
  : Lemma (requires M.resolve w.M.yng a == Some o /\ M.yreachable w o) (ensures value_ok w (M.VPtr (M.Young a)))
  = ()

/// The words the runs store.
let st_int (n: nat) : Lemma (requires n < pow2 64 /\ n % 2 == 1) (ensures storable_w (M.VInt n)) = odd_storable n

let st_iw (_: unit) : Lemma (storable_w (M.infix_word 2) /\ M.infix_word 2 == M.VInt 2297)
  = assert_norm (M.infix_word 2 == M.VInt 2297);
    assert_norm (2297 < pow2 64);
    odd_storable 2297

let st_maj (a: nat) : Lemma (requires a + 1 < msize) (ensures storable_w (M.VPtr (M.Major a))) = major_storable a

let st_yng (a: nat) : Lemma (requires a + 1 < ywords) (ensures storable_w (M.VPtr (M.Young a))) = young_storable a
