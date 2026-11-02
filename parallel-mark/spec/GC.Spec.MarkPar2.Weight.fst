/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Weight — the parts of the termination measure
///
/// `measure` is the objects' weight (`objs_w`), the workers' weight
/// (`wks_w`: inbox entries and program counters), and 1 until marking is
/// done.  These lemmas say how each part moves:
///   * wks_w under one record replaced, and an inbox entry appended;
///   * wks_w and fields_to_scan do not depend on colours, only on the heap's
///     layout, so they are the same in every recoloured heap;
///   * objs_w is monotone in the objects' weights, and drops by at least d
///     if one object's weight drops by d.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Weight

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
open FStar.List.Tot { (@) }

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar2.Model

module M1 = GC.Spec.MarkPar.Model
module Own = GC.Spec.MarkPar.Own

/// ---------------------------------------------------------------------------
/// The workers' weight
/// ---------------------------------------------------------------------------

let wkw (k: cfg) (h: heap) (w: wk) : nat = inbox_w k h w.inbox + pc_w k h w.pc

let rec wks_w_set (k: cfg) (h: heap) (ws: list wk) (i: nat) (w: wk)
  : Lemma (ensures (match M1.nth ws i with
                    | Some w0 -> wks_w k h (M1.set_nth ws i w) + wkw k h w0 == wks_w k h ws + wkw k h w
                    | None -> wks_w k h (M1.set_nth ws i w) == wks_w k h ws))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else wks_w_set k h r (i - 1) w

let rec wks_w_ge (k: cfg) (h: heap) (ws: list wk) (i: nat)
  : Lemma (ensures (match M1.nth ws i with Some w -> wkw k h w <= wks_w k h ws | None -> True))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else wks_w_ge k h r (i - 1)

let rec inbox_w_append (k: cfg) (h: heap) (l: list obj_addr) (v: obj_addr)
  : Lemma (ensures inbox_w k h (l @ [v]) == inbox_w k h l + entry_w k h v) (decreases l)
  = match l with [] -> () | _ :: r -> inbox_w_append k h r v

let entry_w_le (k: cfg) (h: heap) (v: obj_addr) : Lemma (entry_w k h v <= 6 /\ entry_w k h v >= 3) = ()

/// Recolouring keeps resolution, so it keeps every entry's weight.
let entry_w_rec (k: cfg) (g h: heap) (v: obj_addr)
  : Lemma (requires recoloured g h) (ensures entry_w k h v == entry_w k g v)
  = ()

let pc_w_rec (k: cfg) (g h: heap) (p: pc)
  : Lemma (requires recoloured g h) (ensures pc_w k h p == pc_w k g p)
  = match p with Got v -> entry_w_rec k g h v | _ -> ()

let rec inbox_w_rec (k: cfg) (g h: heap) (l: list obj_addr)
  : Lemma (requires recoloured g h) (ensures inbox_w k h l == inbox_w k g l) (decreases l)
  = match l with [] -> () | v :: r -> entry_w_rec k g h v; inbox_w_rec k g h r

let rec wks_w_rec (k: cfg) (g h: heap) (ws: list wk)
  : Lemma (requires recoloured g h) (ensures wks_w k h ws == wks_w k g ws) (decreases ws)
  = match ws with
    | [] -> ()
    | w :: r -> inbox_w_rec k g h w.inbox; pc_w_rec k g h w.pc; wks_w_rec k g h r

let rec wks_w_restart (k: cfg) (h: heap) (ws: list wk)
  : Lemma (requires forall (i: nat) (w: wk). M1.nth ws i == Some w ==> w.inbox == [])
          (ensures wks_w k h (restart ws) == L.length ws) (decreases ws)
  = match ws with
    | [] -> ()
    | w :: r ->
      assert (M1.nth ws 0 == Some w);
      let aux (i: nat) (w': wk) : Lemma (requires M1.nth r i == Some w') (ensures w'.inbox == []) =
        assert (M1.nth ws (i + 1) == Some w') in
      introduce forall (i: nat) (w': wk). M1.nth r i == Some w' ==> w'.inbox == []
      with introduce _ ==> _ with aux i w';
      wks_w_restart k h r

let rec wks_w_stopped (k: cfg) (h: heap) (ws: list wk)
  : Lemma (requires forall (i: nat) (w: wk). M1.nth ws i == Some w ==> w.inbox == [] /\ w.pc == Stopped)
          (ensures wks_w k h ws == 0) (decreases ws)
  = match ws with
    | [] -> ()
    | w :: r ->
      assert (M1.nth ws 0 == Some w);
      let aux (i: nat) (w': wk) : Lemma (requires M1.nth r i == Some w') (ensures w'.inbox == [] /\ w'.pc == Stopped) =
        assert (M1.nth ws (i + 1) == Some w') in
      introduce forall (i: nat) (w': wk). M1.nth r i == Some w' ==> w'.inbox == [] /\ w'.pc == Stopped
      with introduce _ ==> _ with aux i w';
      wks_w_stopped k h r

/// ---------------------------------------------------------------------------
/// The objects' weight
/// ---------------------------------------------------------------------------

let fields_rec (g h: heap) (x: obj_addr)
  : Lemma (requires recoloured g h /\ Seq.mem x (objects zero_addr g))
          (ensures M1.fields_to_scan x h == M1.fields_to_scan x g)
  = recoloured_wosize g h x; recoloured_no_scan g h x

let rec objs_w_mono (k: cfg) (h1 h2: heap) (ws1 ws2: list wk) (l: list obj_addr)
  : Lemma (requires forall (x: obj_addr). L.memP x l ==> obj_w k h2 ws2 x <= obj_w k h1 ws1 x)
          (ensures objs_w k h2 ws2 l <= objs_w k h1 ws1 l) (decreases l)
  = match l with [] -> () | _ :: r -> objs_w_mono k h1 h2 ws1 ws2 r

let rec objs_w_drop (k: cfg) (h1 h2: heap) (ws1 ws2: list wk) (l: list obj_addr) (c: obj_addr) (d: nat)
  : Lemma (requires (forall (x: obj_addr). L.memP x l ==> obj_w k h2 ws2 x <= obj_w k h1 ws1 x) /\
                    L.memP c l /\ obj_w k h2 ws2 c + d <= obj_w k h1 ws1 c)
          (ensures objs_w k h2 ws2 l + d <= objs_w k h1 ws1 l) (decreases l)
  = match l with
    | [] -> ()
    | x :: r ->
      if x = c then objs_w_mono k h1 h2 ws1 ws2 r
      else objs_w_drop k h1 h2 ws1 ws2 r c d
