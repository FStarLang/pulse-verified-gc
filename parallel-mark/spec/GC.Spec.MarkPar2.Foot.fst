/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Foot — what a worker step reads and writes
///
/// From any state a run reaches, worker i's step
///   * writes only the headers of enumerated objects i owns
///     (`wstep_writes`);
///   * reads only the words `readable` allows: words in range i, and the
///     fields of the object i is scanning.  On any heap that agrees there,
///     the step gives the same workers, counter and flags, and writes the
///     same words with the same values (`wstep_reads`);
/// so a word one worker's step writes is never one another worker's step
/// may read (`race_free`).  The main thread runs only when every worker has
/// stopped (`step`'s definition).
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Foot

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Lib.Header
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar2.Model
open GC.Spec.MarkPar2.Inv

module HeapGraph = GC.Spec.HeapGraph
module M1 = GC.Spec.MarkPar.Model
module I1 = GC.Spec.MarkPar.Inv
module Own = GC.Spec.MarkPar.Own
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module St = GC.Spec.MarkPar2.Step

/// ---------------------------------------------------------------------------
/// Writes
/// ---------------------------------------------------------------------------

/// Every word that changed is the header of an enumerated object i owns.
let writes_own (k: cfg) (g: heap) (i: nat) (h h': heap) : prop =
  forall (a: hp_addr). read_word h' a <> read_word h a ==>
    (exists (x: obj_addr). Seq.mem x (objs g) /\ a == hd_address x /\ own k x == i)

let writes_none (k: cfg) (g: heap) (i: nat) (h: heap) : Lemma (writes_own k g i h h) = ()

let writes_color (k: cfg) (g: heap) (i: nat) (h: heap) (x: obj_addr) (c: color)
  : Lemma (requires Seq.mem x (objs g) /\ own k x == i)
          (ensures writes_own k g i h (set_object_color x h c))
  = FStar.Classical.forall_intro (Own.set_color_writes h x c)

let send_heap (k: cfg) (t: state) (me j: nat) (v: obj_addr)
  : Lemma ((send k t me j v).heap == t.heap)
  = ()

let grey_push_writes (k: cfg) (g: heap) (t: state) (me: nat) (c: obj_addr)
  : Lemma (requires Seq.mem c (objs g) /\ own k c == me)
          (ensures writes_own k g me t.heap (grey_push k t me c).heap)
  = makeGray_eq c t.heap;
    if is_white_x c t.heap then
      match M1.nth t.wks me with
      | Some _ -> writes_color k g me t.heap c Gray
      | None -> ()

let accept_writes (k: cfg) (g: heap) (t: state) (me: nat) (v: obj_addr)
  : Lemma (requires recoloured g t.heap /\ Seq.mem (resolve_object v g) (objs g))
          (ensures writes_own k g me t.heap (accept k t me v).heap)
  = let c = resolve_x v t.heap in
    if own k c <> me then send_heap k t me (own k c) c
    else grey_push_writes k g t me c

let route_writes (k: cfg) (g: heap) (t: state) (me: nat) (v: obj_addr)
  : Lemma (requires recoloured g t.heap /\ Seq.mem (resolve_object v g) (objs g))
          (ensures writes_own k g me t.heap (route k t me v).heap)
  = if own k v = me then accept_writes k g t me v else send_heap k t me (own k v) v

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let wstep_writes (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat)
  : Lemma (requires ctx k g roots /\ inv k g roots s)
          (ensures writes_own k g i s.heap (wstep k s i).heap)
  = U.own_heap k g s;
    match M1.nth s.wks i with
    | None -> ()
    | Some w ->
      U.own_rec k g s i w;
      match w.pc with
      | Loop ->
        (match w.stack with
         | x :: _ -> makeBlack_eq x s.heap; writes_color k g i s.heap x Black
         | [] -> ())
      | Scan sc ->
        let v = get_field_x s.heap sc.M1.sobj sc.M1.snext in
        St.scan_field k g s i w sc;
        if HeapGraph.is_pointer_field v then begin
          HeapGraph.is_pointer_field_is_obj_addr v;
          St.scan_target k g roots s sc.M1.sobj sc.M1.snext;
          route_writes k g { s with wks = M1.set_nth s.wks i { w with pc = St.next_pc sc } } i v
        end
      | Got v -> accept_writes k g { s with wks = M1.set_nth s.wks i { w with pc = Finish } } i v
      | _ -> ()
#pop-options

/// ---------------------------------------------------------------------------
/// Reads
/// ---------------------------------------------------------------------------

/// Two heaps agree on range i.
let agree_range (k: cfg) (i: nat) (h1 h2: heap) : prop =
  forall (a: hp_addr). in_range k i a ==> read_word h1 a == read_word h2 a

/// Two steps wrote the same words with the same values.
let wrel (h1 h2 h1' h2': heap) : prop =
  forall (a: hp_addr). (read_word h1' a <> read_word h1 a \/ read_word h2' a <> read_word h2 a) ==>
    read_word h1' a == read_word h2' a

/// Two states equal but for the heap.
let same_rest (t1 t2: state) : prop =
  t1.wks == t2.wks /\ t1.count == t2.count /\ t1.ovf_main == t2.ovf_main /\ t1.finished == t2.finished

let in_range_hd (k: cfg) (x: obj_addr) : Lemma (in_range k (own k x) (hd_address x)) = ()

/// What the object primitives read: the header word only.
let hd_reads (y: obj_addr) (h1 h2: heap)
  : Lemma (requires read_word h1 (hd_address y) == read_word h2 (hd_address y))
          (ensures is_white_x y h1 == is_white_x y h2 /\ wosize_x y h1 == wosize_x y h2 /\
                   is_no_scan_x y h1 == is_no_scan_x y h2 /\ resolve_x y h1 == resolve_x y h2)
  = ()

let write_rel (h1 h2: heap) (a0: hp_addr) (v: U64.t)
  : Lemma (wrel h1 h2 (write_word h1 a0 v) (write_word h2 a0 v))
  = let aux (a: hp_addr) : Lemma ((read_word (write_word h1 a0 v) a <> read_word h1 a \/
                                   read_word (write_word h2 a0 v) a <> read_word h2 a) ==>
                                  read_word (write_word h1 a0 v) a == read_word (write_word h2 a0 v) a) =
      read_write_same h1 a0 v; read_write_same h2 a0 v;
      if a = a0 then ()
      else begin
        assert (U64.v a % 8 == 0 /\ U64.v a0 % 8 == 0);
        read_write_different h1 a0 a v; read_write_different h2 a0 a v
      end
    in
    FStar.Classical.forall_intro aux

let gray_rel (y: obj_addr) (h1 h2: heap)
  : Lemma (requires read_word h1 (hd_address y) == read_word h2 (hd_address y))
          (ensures wrel h1 h2 (makeGray_x y h1) (makeGray_x y h2))
  = write_rel h1 h2 (hd_address y) (colorHeader (read_word h1 (hd_address y)) Gray)

let black_rel (y: obj_addr) (h1 h2: heap)
  : Lemma (requires read_word h1 (hd_address y) == read_word h2 (hd_address y))
          (ensures wrel h1 h2 (makeBlack_x y h1) (makeBlack_x y h2))
  = write_rel h1 h2 (hd_address y) (colorHeader (read_word h1 (hd_address y)) Black)

let send_reads (k: cfg) (t1 t2: state) (me j: nat) (v: obj_addr)
  : Lemma (requires same_rest t1 t2)
          (ensures same_rest (send k t1 me j v) (send k t2 me j v) /\
                   (send k t1 me j v).heap == t1.heap /\ (send k t2 me j v).heap == t2.heap)
  = ()

let grey_push_reads (k: cfg) (t1 t2: state) (me: nat) (c: obj_addr)
  : Lemma (requires same_rest t1 t2 /\ read_word t1.heap (hd_address c) == read_word t2.heap (hd_address c))
          (ensures same_rest (grey_push k t1 me c) (grey_push k t2 me c) /\
                   wrel t1.heap t2.heap (grey_push k t1 me c).heap (grey_push k t2 me c).heap)
  = hd_reads c t1.heap t2.heap;
    gray_rel c t1.heap t2.heap

let accept_reads (k: cfg) (t1 t2: state) (me: nat) (v: obj_addr)
  : Lemma (requires same_rest t1 t2 /\ agree_range k me t1.heap t2.heap /\ own k v == me)
          (ensures same_rest (accept k t1 me v) (accept k t2 me v) /\
                   wrel t1.heap t2.heap (accept k t1 me v).heap (accept k t2 me v).heap)
  = in_range_hd k v;
    hd_reads v t1.heap t2.heap;
    let c = resolve_x v t1.heap in
    if own k c <> me then send_reads k t1 t2 me (own k c) c
    else begin
      in_range_hd k c;
      grey_push_reads k t1 t2 me c
    end

let route_reads (k: cfg) (t1 t2: state) (me: nat) (v: obj_addr)
  : Lemma (requires same_rest t1 t2 /\ agree_range k me t1.heap t2.heap)
          (ensures same_rest (route k t1 me v) (route k t2 me v) /\
                   wrel t1.heap t2.heap (route k t1 me v).heap (route k t2 me v).heap)
  = if own k v = me then accept_reads k t1 t2 me v else send_reads k t1 t2 me (own k v) v

/// The field read in a scan step is a readable word.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let field_reads (s: state) (i: nat) (w: wk) (sc: M1.scanning) (h2: heap)
  : Lemma (requires wk_of s i == Some w /\ w.pc == Scan sc /\ U64.v sc.M1.snext <= U64.v sc.M1.sws /\
                    (forall (a: hp_addr). in_scanned s i a ==> read_word s.heap a == read_word h2 a))
          (ensures get_field_x s.heap sc.M1.sobj sc.M1.snext == get_field_x h2 sc.M1.sobj sc.M1.snext)
  = let x = sc.M1.sobj in
    let j = sc.M1.snext in
    let hd = hd_address x in
    hd_address_spec x;
    if U64.v hd + U64.v mword * U64.v j + U64.v mword <= heap_size then begin
      let fa = U64.add hd (U64.mul mword j) in
      assert (U64.v fa == U64.v x - 8 + 8 * U64.v j);
      assert (in_scanned s i fa)
    end
#pop-options

/// The heap agrees on every readable word.
let agree_readable (k: cfg) (s: state) (i: nat) (h2: heap) : prop =
  forall (a: hp_addr). readable k s i a ==> read_word s.heap a == read_word h2 a

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let wstep_reads (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (h2: heap)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ agree_readable k s i h2)
          (ensures (let s2 = { s with heap = h2 } in
                    same_rest (wstep k s i) (wstep k s2 i) /\
                    wrel s.heap h2 (wstep k s i).heap (wstep k s2 i).heap))
  = let s2 = { s with heap = h2 } in
    assert (agree_range k i s.heap h2);
    match M1.nth s.wks i with
    | None -> ()
    | Some w ->
      U.own_rec k g s i w;
      match w.pc with
      | Loop ->
        (match w.stack with
         | x :: _ ->
           in_range_hd k x;
           hd_reads x s.heap h2;
           black_rel x s.heap h2
         | [] -> ())
      | Scan sc ->
        field_reads s i w sc h2;
        let v = get_field_x s.heap sc.M1.sobj sc.M1.snext in
        let s0 = { s with wks = M1.set_nth s.wks i { w with pc = St.next_pc sc } } in
        let s0' = { s2 with wks = M1.set_nth s.wks i { w with pc = St.next_pc sc } } in
        if HeapGraph.is_pointer_field v then begin
          HeapGraph.is_pointer_field_is_obj_addr v;
          route_reads k s0 s0' i v
        end
      | Got v ->
        let s0 = { s with wks = M1.set_nth s.wks i { w with pc = Finish } } in
        let s0' = { s2 with wks = M1.set_nth s.wks i { w with pc = Finish } } in
        accept_reads k s0 s0' i v
      | _ -> ()
#pop-options

/// ---------------------------------------------------------------------------
/// No word one worker writes is one another may read
/// ---------------------------------------------------------------------------

/// A header of an object another worker owns is not a word worker i may
/// read: it lies in another range, and objects do not overlap, so it is not
/// a field of the object i is scanning (`objects_separated`).
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let other_header (k: cfg) (g: heap) (s: state) (i: nat) (y: obj_addr)
  : Lemma (requires own_ok k g s /\ Seq.mem y (objs g) /\ own k y <> i)
          (ensures ~(readable k s i (hd_address y)))
  = hd_address_spec y;
    match M1.nth s.wks i with
    | Some w ->
      U.own_rec k g s i w;
      (match w.pc with
       | Scan sc ->
         let x = sc.M1.sobj in
         assert (x <> y);
         objects_separated zero_addr g x y;
         assert (U64.v y < U64.v x \/ U64.v y > U64.v x + U64.v sc.M1.sws * 8)
       | _ -> ())
    | None -> ()
#pop-options

/// No word worker j's step writes is one worker i may read, for i <> j.
let race_free (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i j: nat) (a: hp_addr)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ i <> j /\
                    read_word (wstep k s j).heap a <> read_word s.heap a)
          (ensures ~(readable k s i a))
  = wstep_writes k g roots s j;
    let y = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
              (fun y -> Seq.mem y (objs g) /\ a == hd_address y /\ own k y == j) in
    other_header k g s i y
