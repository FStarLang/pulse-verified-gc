/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Lists — lists of workers, and the object list
///
///   * replacing one worker: what `counted`, `any_ovf` and `all_stopped`
///     become;
///   * `clear_ovf` and `restart`, element by element;
///   * the heap's objects, as a list, are in strictly increasing address
///     order (`objs_list_above`), so have no repeats; and recolouring keeps
///     the list.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Lists

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module L = FStar.List.Tot
open FStar.List.Tot { (@) }

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar2.Model

module M1 = GC.Spec.MarkPar.Model
module Own = GC.Spec.MarkPar.Own

/// ---------------------------------------------------------------------------
/// One worker replaced
/// ---------------------------------------------------------------------------

let size (w: wk) : nat = L.length w.stack + L.length w.inbox + held w.pc

let rec counted_set (ws: list wk) (i: nat) (w: wk)
  : Lemma (ensures (match M1.nth ws i with
                    | Some w0 -> counted (M1.set_nth ws i w) + size w0 == counted ws + size w
                    | None -> counted (M1.set_nth ws i w) == counted ws))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else counted_set r (i - 1) w

let rec counted_ge (ws: list wk) (i: nat)
  : Lemma (ensures (match M1.nth ws i with Some w -> size w <= counted ws | None -> True))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else counted_ge r (i - 1)

let counted_zero (ws: list wk) (i: nat) (w: wk)
  : Lemma (requires counted ws == 0 /\ M1.nth ws i == Some w)
          (ensures w.stack == [] /\ w.inbox == [] /\ held w.pc == 0)
  = counted_ge ws i

let rec any_ovf_nth (ws: list wk) (i: nat) (w: wk)
  : Lemma (requires M1.nth ws i == Some w /\ w.ovf) (ensures any_ovf ws) (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else any_ovf_nth r (i - 1) w

/// Setting worker i's record to one whose flag is no lower keeps any_ovf.
let rec any_ovf_set (ws: list wk) (i: nat) (w: wk)
  : Lemma (ensures (match M1.nth ws i with
                    | Some w0 -> (any_ovf ws /\ (w0.ovf ==> w.ovf)) ==> any_ovf (M1.set_nth ws i w)
                    | None -> any_ovf (M1.set_nth ws i w) == any_ovf ws) /\
                   (i < L.length ws /\ w.ovf ==> any_ovf (M1.set_nth ws i w)))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else any_ovf_set r (i - 1) w

/// Setting a record whose flag equals the old one leaves any_ovf.
let rec any_ovf_set_same (ws: list wk) (i: nat) (w: wk)
  : Lemma (ensures (match M1.nth ws i with
                    | Some w0 -> w0.ovf == w.ovf ==> any_ovf (M1.set_nth ws i w) == any_ovf ws
                    | None -> True))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else any_ovf_set_same r (i - 1) w

let rec all_stopped_nth (ws: list wk) (i: nat) (w: wk)
  : Lemma (requires all_stopped ws /\ M1.nth ws i == Some w) (ensures Stopped? w.pc) (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else all_stopped_nth r (i - 1) w

let rec all_stopped_intro (ws: list wk)
  : Lemma (requires forall (i: nat) (w: wk). M1.nth ws i == Some w ==> Stopped? w.pc)
          (ensures all_stopped ws) (decreases ws)
  = match ws with
    | [] -> ()
    | w :: r ->
      assert (M1.nth ws 0 == Some w);
      let aux (i: nat) (w': wk) : Lemma (requires M1.nth r i == Some w') (ensures Stopped? w'.pc) =
        assert (M1.nth ws (i + 1) == Some w') in
      FStar.Classical.forall_intro_2 (fun i w' -> FStar.Classical.move_requires (aux i) w');
      all_stopped_intro r

/// If any_ovf holds, some worker's flag is set.
let rec any_ovf_elim (ws: list wk)
  : Lemma (requires any_ovf ws) (ensures exists (i: nat) (w: wk). M1.nth ws i == Some w /\ w.ovf)
          (decreases ws)
  = match ws with
    | [] -> ()
    | w :: r ->
      if w.ovf then assert (M1.nth ws 0 == Some w)
      else begin
        any_ovf_elim r;
        let aux (i: nat) (w': wk) : Lemma (requires M1.nth r i == Some w' /\ w'.ovf)
            (ensures exists (i: nat) (w: wk). M1.nth ws i == Some w /\ w.ovf) =
          assert (M1.nth ws (i + 1) == Some w') in
        FStar.Classical.forall_intro_2 (fun i w' -> FStar.Classical.move_requires (aux i) w')
      end

let rec nth_clear_ovf (ws: list wk) (i: nat)
  : Lemma (ensures M1.nth (clear_ovf ws) i ==
                   (match M1.nth ws i with Some w -> Some { w with ovf = false } | None -> None))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else nth_clear_ovf r (i - 1)

let rec length_clear_ovf (ws: list wk)
  : Lemma (ensures L.length (clear_ovf ws) == L.length ws) (decreases ws)
  = match ws with [] -> () | _ :: r -> length_clear_ovf r

let rec counted_clear_ovf (ws: list wk)
  : Lemma (ensures counted (clear_ovf ws) == counted ws) (decreases ws)
  = match ws with [] -> () | _ :: r -> counted_clear_ovf r

let rec nth_restart (ws: list wk) (i: nat)
  : Lemma (ensures M1.nth (restart ws) i ==
                   (match M1.nth ws i with Some w -> Some { w with pc = Loop } | None -> None))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else nth_restart r (i - 1)

let rec length_restart (ws: list wk)
  : Lemma (ensures L.length (restart ws) == L.length ws) (decreases ws)
  = match ws with [] -> () | _ :: r -> length_restart r

let rec counted_restart (ws: list wk)
  : Lemma (requires forall (i: nat) (w: wk). M1.nth ws i == Some w ==> held w.pc == 0)
          (ensures counted (restart ws) == counted ws) (decreases ws)
  = match ws with
    | [] -> ()
    | w :: r ->
      assert (M1.nth ws 0 == Some w);
      let aux (i: nat) (w': wk) : Lemma (requires M1.nth r i == Some w') (ensures held w'.pc == 0) =
        assert (M1.nth ws (i + 1) == Some w') in
      FStar.Classical.forall_intro_2 (fun i w' -> FStar.Classical.move_requires (aux i) w');
      counted_restart r

let rec any_ovf_restart (ws: list wk)
  : Lemma (ensures any_ovf (restart ws) == any_ovf ws) (decreases ws)
  = match ws with [] -> () | _ :: r -> any_ovf_restart r

let rec any_ovf_clear (ws: list wk)
  : Lemma (ensures any_ovf (clear_ovf ws) == false) (decreases ws)
  = match ws with [] -> () | _ :: r -> any_ovf_clear r

/// set_nth, in the form most lemmas use.
let nth_upd (#a: Type) (l: list a) (i: nat) (v: a) (j: nat)
  : Lemma (requires i < L.length l)
          (ensures L.length (M1.set_nth l i v) == L.length l /\
                   M1.nth (M1.set_nth l i v) j == (if j = i then Some v else M1.nth l j))
  = Own.length_set_nth l i v; Own.nth_set_nth l i j v

/// ---------------------------------------------------------------------------
/// The objects, in address order
/// ---------------------------------------------------------------------------

/// Strictly increasing, and every element above b.
let rec above (b: int) (l: list obj_addr) : Tot prop (decreases l) =
  match l with
  | [] -> True
  | x :: r -> b < U64.v x /\ above (U64.v x) r

let rec above_mem (b: int) (l: list obj_addr) (z: obj_addr)
  : Lemma (requires above b l /\ L.memP z l) (ensures b < U64.v z) (decreases l)
  = match l with
    | [] -> ()
    | x :: r -> if z = x then () else above_mem (U64.v x) r z

let above_weaken (b b': int) (l: list obj_addr)
  : Lemma (requires above b l /\ b' <= b) (ensures above b' l) (decreases l)
  = match l with [] -> () | _ :: _ -> ()

let rec above_norepeats (b: int) (l: list obj_addr)
  : Lemma (requires above b l) (ensures L.noRepeats l) (decreases l)
  = match l with
    | [] -> ()
    | x :: r ->
      above_norepeats (U64.v x) r;
      if L.mem x r then begin L.mem_memP x r; above_mem (U64.v x) r x end

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec objects_above (start: hp_addr) (g: heap)
  : Lemma (ensures above (U64.v start) (Seq.seq_to_list (objects_x start g)))
          (decreases (Seq.length g - U64.v start))
  = if U64.v start + 8 >= Seq.length g then ()
    else begin
      let header = read_word g start in
      let wz = getWosize header in
      let next_start_nat = U64.v start + ((U64.v wz + 1) * 8) in
      if next_start_nat > Seq.length g || next_start_nat >= pow2 64 then ()
      else begin
        f_address_spec start;
        let obj : obj_addr = f_address start in
        if next_start_nat >= heap_size then
          Seq.lemma_seq_to_list_cons obj (Seq.empty #obj_addr)
        else begin
          let next : hp_addr = U64.uint_to_t next_start_nat in
          objects_above next g;
          Seq.lemma_seq_to_list_cons obj (objects_x next g);
          above_weaken (U64.v next) (U64.v obj) (Seq.seq_to_list (objects_x next g))
        end
      end
    end
#pop-options

let objs_list_above (h: heap)
  : Lemma (above (U64.v zero_addr) (objs_list h) /\ L.noRepeats (objs_list h))
  = objects_above zero_addr h;
    above_norepeats (U64.v zero_addr) (objs_list h)

let objs_list_mem (h: heap) (x: obj_addr)
  : Lemma (L.memP x (objs_list h) <==> Seq.mem x (objects zero_addr h))
  = SP.lemma_seq_to_list_permutation (objects_x zero_addr h);
    L.mem_memP x (objs_list h);
    L.mem_count (objs_list h) x

let objs_list_same (h1 h2: heap)
  : Lemma (requires objects zero_addr h1 == objects zero_addr h2)
          (ensures objs_list h1 == objs_list h2)
  = ()
