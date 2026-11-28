/// ---------------------------------------------------------------------------
/// GC.Spec.Top.CodeFFDup - the remembered set as C's table, with repeats
/// ---------------------------------------------------------------------------
///
/// Design doc §18, U3.  akhil's barrier asks to remember a slot exactly when
/// the new value is young and the old one is not (`GB.modify_records`), and
/// the bridge appends the slot then; the model's barrier
/// (`ByteBarrier.remember`) appends a slot only when it is not remembered
/// already.  So a slot remembered with a young value, overwritten with an
/// old one, then with a young one again, is in C's table twice and in the
/// model's set once (`CodeFFMinor.records_agree`).  `tbl_d tv n rem`: the
/// table's first `n` entries are the words of a list of slots `sl`
/// (`CodeMinor.tbl_ok`), and the model's set is `sl` with every repeat
/// dropped (`dds sl`, the first occurrences, in order).  The glue keeps `sl`
/// as ghost state.

module GC.Spec.Top.CodeFFDup

open FStar.Seq
module M = GC.Spec.Top.Heap
module L = FStar.List.Tot
module U64 = FStar.UInt64
module CM = GC.Spec.Top.CodeMinor
module CF = GC.Spec.Top.CodeFF
module CP = GC.Spec.Top.CodePages
module FMi = GC.Spec.Top.CodeFFMinor
module Y = GC.Spec.Top.Young
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module CG = GC.Spec.Top.CodeGuard
module GP = GC.Gen.Promote
module MF = GC.Gen.MinorCollectForwarding
module MCFH = GC.Gen.MinorCollectForwarding.Helpers
module FA = GC.Gen.ForwardingArray
module GenInv = GC.Gen.HeapInvariant
module FAO = GC.Spec.Top.FFAllocOk
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.RefTable
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.Run

#set-options "--fuel 2 --ifuel 1 --z3rlimit 20"

/// The slots of `sl`, each once, at its first occurrence, after `acc`.
let rec dd_from (acc: list M.slot) (sl: list M.slot) : Tot (list M.slot) (decreases sl) =
  match sl with
  | [] -> acc
  | s :: tl -> dd_from (if L.mem s acc then acc else L.append acc [s]) tl

let dds (sl: list M.slot) : list M.slot = dd_from [] sl

/// One more slot.
let dstep (acc: list M.slot) (s: M.slot) : list M.slot = if L.mem s acc then acc else L.append acc [s]

let rec dd_snoc (acc sl: list M.slot) (s: M.slot)
  : Lemma (ensures dd_from acc (L.append sl [s]) == dstep (dd_from acc sl) s) (decreases sl)
  = match sl with
    | [] -> ()
    | h :: tl -> dd_snoc (dstep acc h) tl s

/// Membership: a slot of the result is one of `acc` or of `sl`, and back.
let rec dd_mem (acc sl: list M.slot) (s: M.slot)
  : Lemma (ensures L.mem s (dd_from acc sl) <==> (L.mem s acc \/ L.mem s sl)) (decreases sl)
  = match sl with
    | [] -> ()
    | h :: tl ->
      L.append_mem acc [h] s;
      dd_mem (dstep acc h) tl s

/// **The table with repeats**: its first `n` words are those of the slots
/// `sl`, and the model's remembered set is `sl` with repeats dropped.
let tbl_d (tv: seq U64.t) (n: nat) (sl rem: list M.slot) : prop =
  CM.tbl_ok tv n sl /\ dds sl == rem

let tbl_d_nil (tv: seq U64.t) : Lemma (tbl_d tv 0 [] []) = ()

/// A slot is remembered exactly when the table holds it.
let tbl_d_mem (tv: seq U64.t) (n: nat) (sl rem: list M.slot) (s: M.slot)
  : Lemma (requires tbl_d tv n sl rem) (ensures L.mem s rem <==> L.mem s sl)
  = dd_mem [] sl s

/// **Appending a slot to the table**: the model's set grows by it unless it
/// is remembered already -- the model's barrier (`ByteBarrier.remember`)
/// when akhil's barrier says to remember (`CodeFFMinor.records_agree`).
let tbl_d_snoc (tv: seq U64.t) (n: nat) (sl rem: list M.slot) (s: M.slot)
  : Lemma (requires tbl_d tv n sl rem /\ n < Seq.length tv)
          (ensures tbl_d (Seq.upd tv n (CM.slot_word s)) (n + 1) (L.append sl [s])
                         (if L.mem s rem then rem else L.append rem [s]))
  = CM.tbl_snoc tv n sl s;
    dd_snoc [] sl s

/// ... in particular a slot not remembered yet (the Fill's fresh slots).
let tbl_d_fresh (tv: seq U64.t) (n: nat) (sl rem: list M.slot) (s: M.slot)
  : Lemma (requires tbl_d tv n sl rem /\ n < Seq.length tv /\ ~(L.memP s rem))
          (ensures tbl_d (Seq.upd tv n (CM.slot_word s)) (n + 1) (L.append sl [s]) (L.append rem [s]))
  = L.mem_memP s rem;
    tbl_d_snoc tv n sl rem s

/// ---------------------------------------------------------------------------
/// The minor collection on the table's roots, repeats included
/// ---------------------------------------------------------------------------

let mem_iff (s: M.slot) (l: list M.slot) : Lemma (L.mem s l <==> L.memP s l) = L.mem_memP s l

/// Every slot of the table is remembered.
let sl_rem (tv: seq U64.t) (n: nat) (sl rem: list M.slot) (s: M.slot)
  : Lemma (requires tbl_d tv n sl rem /\ L.memP s sl) (ensures L.memP s rem)
  = mem_iff s sl; mem_iff s rem; tbl_d_mem tv n sl rem s

/// The words of one slot, as `LV.yrem` reads it.
let slw (m y: M.mheap) (s: M.slot) : GTot (seq U64.t) =
  let (o, i) = s in if M.ptr_field m o i then LV.yword y (M.field m o i) else Seq.empty

let rec yrem_char (m y: M.mheap) (l: list M.slot) (u: U64.t)
  : Lemma (ensures Seq.mem u (LV.yrem m y l) <==> (exists (s: M.slot). L.memP s l /\ Seq.mem u (slw m y s)))
          (decreases l)
  = match l with
    | [] -> LV.mem_empty u
    | (o, i) :: tl ->
      Seq.lemma_mem_append (slw m y (o, i)) (LV.yrem m y tl);
      yrem_char m y tl u

/// The young words of the slots with repeats are those of the slots once.
let yrem_dds (m y: M.mheap) (sl: list M.slot) (u: U64.t)
  : Lemma (Seq.mem u (LV.yrem m y sl) <==> Seq.mem u (LV.yrem m y (dds sl)))
  = yrem_char m y sl u;
    yrem_char m y (dds sl) u;
    let f (s: M.slot) : Lemma (L.memP s sl <==> L.memP s (dds sl))
      = mem_iff s sl; mem_iff s (dds sl); dd_mem [] sl s in
    FStar.Classical.forall_intro f

/// One entry of the induction, as `CodeFFMinor.yrem_one`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let yrem_one (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (k: nat)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\ k < n)
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    let y = Y.ycabs x.w.cyng in
                    k < Seq.length tv /\
                    CM.yrem_tbl g tv k n == Seq.append (CM.ysel (CM.rd g (Seq.index tv k))) (CM.yrem_tbl g tv (k + 1) n) /\
                    LV.yrem (cabs g) y (CP.ldrop k sl) ==
                    Seq.append (CM.ysel (CM.rd g (Seq.index tv k))) (LV.yrem (cabs g) y (CP.ldrop (k + 1) sl))))
  = let x = CF.xc es in
    let g = CF.hof x in
    let y = Y.ycabs x.w.cyng in
    CP.ldrop_cons k sl;
    let o = fst (L.index sl k) in
    let i = snd (L.index sl k) in
    assert (L.index sl k == (o, i));
    L.lemma_index_memP sl k;
    sl_rem tv n sl x.w.crem (o, i);
    FMi.slot_facts sty es o i;
    CM.yrem_tbl_step g tv k n;
    CM.yrem_cons (cabs g) y o i (CP.ldrop (k + 1) sl);
    let w = read_word g (hp (o + 1 + i)) in
    assert (CM.rd g (Seq.index tv k) == w);
    (if is_young_w w then begin
       CG.young_word_of w;
       assert (M.field (cabs g) o i == M.VPtr (M.Young ((U64.v w - 8) / 8)))
     end);
    CM.yword_sel y w
#pop-options

let rec yrem_from (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (k: nat)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\ k <= n)
          (ensures CM.yrem_tbl (CF.hof (CF.xc es)) tv k n ==
                   LV.yrem (cabs (CF.hof (CF.xc es))) (Y.ycabs (CF.xc es).w.cyng) (CP.ldrop k sl))
          (decreases (n - k))
  = let x = CF.xc es in
    if k = n then begin
      CP.ldrop_all sl;
      CM.yrem_tbl_end (CF.hof x) tv n;
      CM.yrem_nil (cabs (CF.hof x)) (Y.ycabs x.w.cyng)
    end
    else begin
      yrem_one sty es tv n sl k;
      yrem_from sty es tv n sl (k + 1)
    end

/// The roots the glue builds from the table with repeats.
let rsd (x: config CF.fc) (tv: seq U64.t) (n: nat) : GTot (seq U64.t) =
  Seq.append (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) (CM.ypre_tbl (CF.hof x) tv n)

/// **They have the members of the model's roots.**
let rsd_mem (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (u: U64.t)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem)
          (ensures Seq.mem u (rsd (CF.xc es) tv n) <==> Seq.mem u (FMi.mroots (CF.xc es)))
  = let x = CF.xc es in
    let g = CF.hof x in
    let y = Y.ycabs x.w.cyng in
    yrem_from sty es tv n sl 0;
    CP.ldrop_zero sl;
    CM.ypre_tbl_eq g tv n;
    yrem_dds (cabs g) y sl u;
    Seq.lemma_mem_append (LV.yroots y x.w.croots) (CM.ypre_tbl g tv n);
    Seq.lemma_mem_append (LV.yroots y x.w.croots) (LV.yrem (cabs g) y x.w.crem)

/// One entry: a remembered slot's field address, as `CodeFFMinor.slot_facts`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let entry_facts (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (k: nat)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\ k < n)
          (ensures (let x = CF.xc es in
                    let g = CF.hof x in
                    let addr = U64.v (Seq.index tv k) in
                    addr < heap_size /\ addr % 8 == 0 /\
                    (exists (obj: obj_addr) (j: nat).
                       is_block g obj /\ not ((FMi.mtal x).GC.Spec.Pages.Promote.free g obj) /\ scannable g obj /\
                       j < U64.v (wosize_of_object obj g) /\ addr == U64.v obj + j * 8)))
  = let x = CF.xc es in
    let o = fst (L.index sl k) in
    let i = snd (L.index sl k) in
    assert (L.index sl k == (o, i));
    L.lemma_index_memP sl k;
    sl_rem tv n sl x.w.crem (o, i);
    FMi.slot_facts sty es o i;
    assert (Seq.index tv k == CM.slot_word (o, i));
    pos_aligned (o + 1 + i);
    let obj : obj_addr = obj_of o in
    assert (U64.v (Seq.index tv k) == U64.v obj + i * 8)
#pop-options

/// **The table with repeats is sound** for first-fit at the phase.
let tbl_sound_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem)
          (ensures ref_table_sound_with (FMi.mtal (CF.xc es)).GC.Spec.Pages.Promote.free (CF.hof (CF.xc es)) tv n)
  = let one (k: nat)
      : Lemma (k < n ==>
               (let x = CF.xc es in
                let addr = U64.v (Seq.index tv k) in
                addr < heap_size /\ addr % 8 == 0 /\
                (exists (obj: obj_addr) (j: nat).
                   is_block (CF.hof x) obj /\ not ((FMi.mtal x).GC.Spec.Pages.Promote.free (CF.hof x) obj) /\
                   scannable (CF.hof x) obj /\
                   j < U64.v (wosize_of_object obj (CF.hof x)) /\ addr == U64.v obj + j * 8)))
      = if k < n then entry_facts sty es tv n sl k in
    FStar.Classical.forall_intro one

/// A young field of a block in use is a remembered slot, at its address.
#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let field_rem (sty: style) (es: list event) (obj: obj_addr) (j: nat)
  : Lemma (requires CF.good sty es /\
                    is_block (CF.hof (CF.xc es)) obj /\
                    not ((FMi.mtal (CF.xc es)).GC.Spec.Pages.Promote.free (CF.hof (CF.xc es)) obj) /\
                    scannable (CF.hof (CF.xc es)) obj /\
                    j < U64.v (wosize_of_object obj (CF.hof (CF.xc es))) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    GP.is_minor_pointer (to_minor_offset (read_word (CF.hof (CF.xc es)) (U64.uint_to_t (U64.v obj + j * 8)))))
          (ensures L.memP (maddr obj, j) (CF.xc es).w.crem /\
                   U64.v (CM.slot_word (maddr obj, j)) == U64.v obj + j * 8)
  = let x = CF.xc es in
    let g = CF.hof x in
    FMi.nonfree_live sty es obj;
    let o = maddr obj in
    CM.hdr_facts g o;
    assert (M.ptr_field (cabs g) o j);
    CM.field_word g o j;
    GC.Spec.Top.ByteBarrier.fword_addr o j;
    CM.slot_word_hp o j;
    U64.v_inj (hp (o + 1 + j)) (U64.uint_to_t (U64.v obj + j * 8));
    let w = read_word g (hp (o + 1 + j)) in
    CM.minor_ptr_young w;
    CG.young_word_of w;
    let a = (U64.v w - 8) / 8 in
    assert (M.field (mj x) o j == M.VPtr (M.Young a));
    FMi.young_rem sty es o j a
#pop-options

/// One covered field.
#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"
let covers_one_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (obj: obj_addr) (j: nat)
  : Lemma (requires CF.good sty es /\ tbl_d tv n sl (CF.xc es).w.crem /\
                    is_block (CF.hof (CF.xc es)) obj /\
                    not ((FMi.mtal (CF.xc es)).GC.Spec.Pages.Promote.free (CF.hof (CF.xc es)) obj) /\
                    scannable (CF.hof (CF.xc es)) obj /\
                    j < U64.v (wosize_of_object obj (CF.hof (CF.xc es))) /\
                    U64.v obj + j * 8 + 8 <= heap_size /\
                    GP.is_minor_pointer (to_minor_offset (read_word (CF.hof (CF.xc es)) (U64.uint_to_t (U64.v obj + j * 8)))))
          (ensures exists (k: nat). k < n /\ U64.v (Seq.index tv k) == U64.v obj + j * 8)
  = let x = CF.xc es in
    field_rem sty es obj j;
    mem_iff (maddr obj, j) x.w.crem;
    mem_iff (maddr obj, j) sl;
    tbl_d_mem tv n sl x.w.crem (maddr obj, j);
    CM.memP_idx sl (maddr obj, j)
#pop-options

/// **The table with repeats covers** every young pointer of a block in use.
let tbl_covers_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot)
  : Lemma (requires CF.good sty es /\ tbl_d tv n sl (CF.xc es).w.crem)
          (ensures ref_table_covers_with (FMi.mtal (CF.xc es)).GC.Spec.Pages.Promote.free (CF.hof (CF.xc es)) tv n)
  = let x = CF.xc es in
    let g = CF.hof x in
    FStar.Classical.forall_intro_2 CM.fld_aligned;
    let one (obj: obj_addr) (j: nat)
      : Lemma (is_block g obj /\ not ((FMi.mtal x).GC.Spec.Pages.Promote.free g obj) /\ scannable g obj /\
               j < U64.v (wosize_of_object obj g) /\ U64.v obj + j * 8 + 8 <= heap_size /\
               GP.is_minor_pointer (to_minor_offset (read_word g (U64.uint_to_t (U64.v obj + j * 8)))) ==>
               (exists (k: nat). k < n /\ U64.v (Seq.index tv k) == U64.v obj + j * 8))
      = FStar.Classical.move_requires (covers_one_d sty es tv n sl obj) j in
    FStar.Classical.forall_intro_2 one

/// A remembered target of one entry is among the glue's roots.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let target_one_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (i: nat)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\ i < n)
          (ensures (let g = CF.hof (CF.xc es) in
                    U64.v (Seq.index tv i) < heap_size /\ U64.v (Seq.index tv i) % U64.v mword == 0 /\
                    (let v = to_minor_offset (read_word g (Seq.index tv i <: hp_addr)) in
                     GP.is_minor_pointer v ==> Seq.mem v (rsd (CF.xc es) tv n))))
  = let x = CF.xc es in
    let g = CF.hof x in
    entry_facts sty es tv n sl i;
    let a : hp_addr = Seq.index tv i in
    let w = read_word g a in
    CM.minor_ptr_young w;
    if GP.is_minor_pointer (to_minor_offset w) then begin
      to_minor_offset_in_minor_range w;
      assert (CM.rd g a == w);
      FMi.ysel_mem w;
      FMi.ypre_tbl_mem g tv i n w;
      Seq.lemma_mem_append (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) (CM.ypre_tbl g tv n)
    end
#pop-options

/// **akhil's collection's precondition on the glue's roots** (the table's
/// repeats included), given his two nursery conditions.
let minor_pre_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (farr: seq U64.t)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\
                    Seq.length farr == FA.fwd_array_size /\
                    (forall (i: nat). i < Seq.length farr ==> Seq.index farr i == 0UL) /\
                    minor_guards_complete (CF.xc es).w.cyng /\ minor_infix_wf (CF.xc es).w.cyng)
          (ensures (let x = CF.xc es in
                    FMi.pre_with (gph x.ph) (FAO.ffree_of x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp
                      (rsd x tv n) farr tv n))
  = let x = CF.xc es in
    FMi.shape_ff sty es;
    tbl_sound_d sty es tv n sl;
    tbl_covers_d sty es tv n sl;
    let t (i: nat)
      : Lemma (i < n ==>
               U64.v (Seq.index tv i) < heap_size /\ U64.v (Seq.index tv i) % U64.v mword == 0 /\
               (let v = to_minor_offset (read_word (CF.hof x) (Seq.index tv i <: hp_addr)) in
                GP.is_minor_pointer v ==> Seq.mem v (rsd x tv n)))
      = if i < n then target_one_d sty es tv n sl i in
    FStar.Classical.forall_intro t;
    MCFH.remembered_targets_in_roots_intro_by_slots (CF.hof x) (rsd x tv n) tv n;
    let r (u: U64.t)
      : Lemma (requires Seq.mem u (rsd x tv n))
              (ensures GP.is_minor_pointer u /\
                       Seq.mem (resolve_minor x.w.cyng u) (minor_objects x.w.cyng) /\
                       minor_wosize x.w.cyng (resolve_minor x.w.cyng u) > 0)
      = rsd_mem sty es tv n sl u;
        FMi.root_valid_one sty es u in
    FStar.Classical.forall_intro (FStar.Classical.move_requires r)

/// ---------------------------------------------------------------------------
/// The repeats change nothing: the glue's roots are the model's with
/// repeats inserted
/// ---------------------------------------------------------------------------

module R = GC.Spec.Top.FFRepeat
module P = GC.Spec.Pages.Promote
module PL = GC.Spec.Pages.Promote.Loop
module FFP = GC.Spec.Top.FFPromote
module FW = GC.Spec.Top.FFWrite
module FM = GC.Spec.Top.FFMinor
module FCh = GC.Spec.Top.FFCheney
module C = GC.Gen.Cheney
module CB = GC.Gen.CheneyBFS
module CR = GC.Spec.Top.CodeRun
module SM = GC.Spec.Top.StepMinor

/// `yrem` of an append.
#push-options "--fuel 1 --ifuel 1"
let rec yrem_app (m y: M.mheap) (l1 l2: list M.slot)
  : Lemma (ensures LV.yrem m y (L.append l1 l2) == Seq.append (LV.yrem m y l1) (LV.yrem m y l2)) (decreases l1)
  = match l1 with
    | [] -> Seq.lemma_eq_elim (LV.yrem m y l2) (Seq.append Seq.empty (LV.yrem m y l2))
    | (o, i) :: tl ->
      yrem_app m y tl l2;
      Seq.append_assoc (slw m y (o, i)) (LV.yrem m y tl) (LV.yrem m y l2)

#pop-options

#push-options "--fuel 2 --ifuel 1"
let yrem_one_slot (m y: M.mheap) (s: M.slot)
  : Lemma (LV.yrem m y [s] == slw m y s)
  = match s with
    | (o, i) ->
      assert (LV.yrem m y [] == Seq.empty);
      assert (LV.yrem m y [(o, i)] == Seq.append (slw m y (o, i)) (LV.yrem m y []));
      Seq.lemma_eq_elim (Seq.append (slw m y s) Seq.empty) (slw m y s)
#pop-options

/// A slot gives no word or one.
let slw_shape (m y: M.mheap) (s: M.slot)
  : Lemma (Seq.length (slw m y s) == 0 \/ (Seq.length (slw m y s) == 1 /\ slw m y s == Seq.create 1 (Seq.index (slw m y s) 0)))
  = let (o, i) = s in
    if M.ptr_field m o i then begin
      match M.field m o i with
      | M.VPtr (M.Young a) ->
        if Some? (M.resolve y a) && 8 * a + 16 <= minor_heap_size then
          (Y.msz (); Seq.lemma_eq_elim (slw m y s) (Seq.create 1 (Seq.index (slw m y s) 0)))
      | _ -> ()
    end

let cast (#s #t: seq U64.t) (r: R.rep s t) (s' t': seq U64.t)
  : Pure (R.rep s' t') (requires s == s' /\ t == t') (ensures fun _ -> True)
  = coerce_eq () r

/// Appending one slot's words to both sides, or to the left one only when
/// the slot was there already.
#push-options "--z3rlimit 40"
let rep_slot (m y: M.mheap) (a: seq U64.t) (pre: list M.slot) (s: M.slot)
  (r: R.rep (Seq.append a (LV.yrem m y pre)) (Seq.append a (LV.yrem m y (dds pre))))
  : GTot (R.rep (Seq.append a (LV.yrem m y (L.append pre [s]))) (Seq.append a (LV.yrem m y (dds (L.append pre [s])))))
  = let sp = Seq.append a (LV.yrem m y pre) in
    let tp = Seq.append a (LV.yrem m y (dds pre)) in
    let w = slw m y s in
    yrem_app m y pre [s];
    yrem_one_slot m y s;
    dd_snoc [] pre s;
    Seq.append_assoc a (LV.yrem m y pre) w;
    let s' = Seq.append a (LV.yrem m y (L.append pre [s])) in
    let t' = Seq.append a (LV.yrem m y (dds (L.append pre [s]))) in
    assert (s' == Seq.append sp w);
    slw_shape m y s;
    if L.mem s (dds pre) then begin
      assert (dds (L.append pre [s]) == dds pre);
      if Seq.length w = 0 then begin
        Seq.lemma_eq_elim (Seq.append sp w) sp;
        cast r s' t'
      end
      else begin
        let u = Seq.index w 0 in
        dd_mem [] pre s;
        mem_iff s pre;
        yrem_char m y pre u;
        Seq.lemma_mem_append (Seq.create 1 u) (Seq.empty #U64.t);
        GC.Spec.Top.PagesLive.mem_one u u;
        Seq.lemma_mem_append a (LV.yrem m y pre);
        R.RDrop r u s'
      end
    end
    else begin
      assert (dds (L.append pre [s]) == L.append (dds pre) [s]);
      yrem_app m y (dds pre) [s];
      Seq.append_assoc a (LV.yrem m y (dds pre)) w;
      assert (t' == Seq.append tp w);
      if Seq.length w = 0 then begin
        Seq.lemma_eq_elim (Seq.append sp w) sp;
        Seq.lemma_eq_elim (Seq.append tp w) tp;
        cast r s' t'
      end
      else R.RKeep r (Seq.index w 0) s' t'
    end
#pop-options

/// Over the rest of the slots.
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec rep_from (m y: M.mheap) (a: seq U64.t) (pre post: list M.slot)
  (r: R.rep (Seq.append a (LV.yrem m y pre)) (Seq.append a (LV.yrem m y (dds pre))))
  : GTot (R.rep (Seq.append a (LV.yrem m y (L.append pre post))) (Seq.append a (LV.yrem m y (dds (L.append pre post)))))
    (decreases post)
  = match post with
    | [] -> L.append_l_nil pre; cast r (Seq.append a (LV.yrem m y (L.append pre post))) (Seq.append a (LV.yrem m y (dds (L.append pre post))))
    | s :: tl ->
      L.append_assoc pre [s] tl;
      assert (L.append [s] tl == post);
      assert (L.append (L.append pre [s]) tl == L.append pre post);
      let r1 = rep_slot m y a pre s r in
      let r2 = rep_from m y a (L.append pre [s]) tl r1 in
      cast r2 (Seq.append a (LV.yrem m y (L.append pre post))) (Seq.append a (LV.yrem m y (dds (L.append pre post))))
#pop-options

/// **The slots with repeats, and once.**
let rep_slots (m y: M.mheap) (a: seq U64.t) (sl: list M.slot)
  : GTot (R.rep (Seq.append a (LV.yrem m y sl)) (Seq.append a (LV.yrem m y (dds sl))))
  = Seq.lemma_eq_elim (Seq.append a (LV.yrem m y [])) a;
    assert (dds [] == []);
    let r0 = cast (R.rep_refl a) (Seq.append a (LV.yrem m y [])) (Seq.append a (LV.yrem m y (dds []))) in
    rep_from m y a [] sl r0

/// The glue's roots, as the slots with repeats.
let rsd_eq (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem)
          (ensures (let x = CF.xc es in
                    rsd x tv n == Seq.append (LV.yroots (Y.ycabs x.w.cyng) x.w.croots)
                                             (LV.yrem (cabs (CF.hof x)) (Y.ycabs x.w.cyng) sl) /\
                    FMi.mroots x == Seq.append (LV.yroots (Y.ycabs x.w.cyng) x.w.croots)
                                               (LV.yrem (cabs (CF.hof x)) (Y.ycabs x.w.cyng) (dds sl))))
  = yrem_from sty es tv n sl 0;
    CP.ldrop_zero sl;
    CM.ypre_tbl_eq (CF.hof (CF.xc es)) tv n

/// **The glue's roots are the model's with repeats inserted.**
let rep_tbl (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot)
  : Ghost (R.rep (rsd (CF.xc es) tv n) (FMi.mroots (CF.xc es)))
          (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem)
          (ensures fun _ -> True)
  = let x = CF.xc es in
    rsd_eq sty es tv n sl;
    let r = rep_slots (cabs (CF.hof x)) (Y.ycabs x.w.cyng) (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) sl in
    cast r (rsd x tv n) (FMi.mroots x)

/// The promotion's context at a configuration of the code's run, given
/// akhil's `minor_infix_wf` (the wrapper's trusted hypothesis).
#push-options "--z3rlimit 40"
let ctx_ff (sty: style) (es: list event)
  : Lemma (requires CF.good sty es /\ minor_infix_wf (CF.xc es).w.cyng)
          (ensures (let x = CF.xc es in
                    PL.ctx (R.tl x.ph) x.w.cyng (CF.hof x) /\ FW.fshape x.ph (CF.hof x) (CF.sof x).fp))
  = let x = CF.xc es in
    CF.components ();
    CR.rinv_cur CF.fc sty msize ywords es;
    CF.gl_ok x;
    SM.minor_pre_of x;
    vw_views x;
    FM.ctx_start x.ph (CF.sof x) x.w (vw x)
#pop-options

/// **akhil's promotion on the glue's roots is his promotion on the model's**:
/// the same heap, free-list head and forwarding map, so the same collection.
#push-options "--z3rlimit 40"
let promote_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\
                    minor_infix_wf (CF.xc es).w.cyng)
          (ensures (let x = CF.xc es in
                    let ph = gph x.ph in
                    let ms = x.w.cyng in
                    let g = CF.hof x in
                    let fp = (CF.sof x).fp in
                    let cr = C.cheney_promote ph ms g fp (rsd x tv n) in
                    let cm = C.cheney_promote ph ms g fp (FMi.mroots x) in
                    cr.GP.fp_final == cm.GP.fp_final /\ cr.GP.major_final == cm.GP.major_final /\
                    cr.GP.fwd_map == cm.GP.fwd_map /\
                    (C.cheney_collect_spec_with ph (FAO.ffree_of x.ph) ms g fp (rsd x tv n)).GP.mc_major ==
                    (C.cheney_collect_spec_with ph (FAO.ffree_of x.ph) ms g fp (FMi.mroots x)).GP.mc_major))
  = let x = CF.xc es in
    let ms = x.w.cyng in
    let g = CF.hof x in
    let fp = (CF.sof x).fp in
    ctx_ff sty es;
    let r = rep_tbl sty es tv n sl in
    R.promote_rep x.ph ms g fp (rsd x tv n) (FMi.mroots x) r;
    FCh.promote_all_eq x.ph ms g fp (rsd x tv n);
    FCh.promote_all_eq x.ph ms g fp (FMi.mroots x)
#pop-options

/// The model's roots are among the glue's.
let mroots_in_rsd (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (z: U64.t)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\
                    Seq.mem z (FMi.mroots (CF.xc es)))
          (ensures Seq.mem z (rsd (CF.xc es) tv n))
  = R.rep_mem (rsd (CF.xc es) tv n) (FMi.mroots (CF.xc es)) (rep_tbl sty es tv n sl) z

/// **akhil's `cheney_no_oom` on the glue's roots is the same on the model's.**
#push-options "--z3rlimit 40"
let no_oom_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\
                    minor_infix_wf (CF.xc es).w.cyng /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (rsd x tv n)))
          (ensures (let x = CF.xc es in
                    CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (FMi.mroots x)))
  = promote_d sty es tv n sl;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (mroots_in_rsd sty es tv n sl))
#pop-options

/// **akhil's postcondition on the glue's roots, as the model's next
/// configuration** (`CodeFFMinor.minor_post_ff`).
#push-options "--z3rlimit 40"
let minor_post_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot)
  (s2: heap) (fp2: U64.t) (ms2: minor_state)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\
                    minor_infix_wf (CF.xc es).w.cyng /\
                    (let x = CF.xc es in
                     let ms = x.w.cyng in
                     let rs = rsd x tv n in
                     s2 == (C.cheney_collect_spec_with (gph x.ph) (FAO.ffree_of x.ph) ms (CF.hof x) (CF.sof x).fp rs).GP.mc_major /\
                     fp2 == (C.cheney_promote (gph x.ph) ms (CF.hof x) (CF.sof x).fp rs).GP.fp_final /\
                     ms2 == minor_reset ms /\
                     CB.cheney_no_oom (gph x.ph) ms (CF.hof x) (CF.sof x).fp rs))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EMinor]) in
                    CF.good sty (L.append es [EMinor]) /\
                    CF.hof x' == s2 /\ (CF.sof x').fp == fp2 /\ x'.w.cyng == ms2 /\ x'.w.crem == [] /\
                    x'.ph == x.ph /\ x'.ms == x.ms /\ FMi.rem_ok x' /\
                    (C.cheney_promote (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (rsd x tv n)).GP.fwd_map ==
                    (C.cheney_promote (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (FMi.mroots x)).GP.fwd_map))
  = promote_d sty es tv n sl;
    no_oom_d sty es tv n sl;
    FMi.minor_post_ff sty es s2 fp2 ms2
#pop-options

/// The glue's roots and the model's start with the same young roots.
let prefix_same (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (i: nat)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\
                    i < Seq.length (LV.yroots (Y.ycabs (CF.xc es).w.cyng) (CF.xc es).w.croots))
          (ensures i < Seq.length (rsd (CF.xc es) tv n) /\ i < Seq.length (FMi.mroots (CF.xc es)) /\
                   Seq.index (rsd (CF.xc es) tv n) i == Seq.index (FMi.mroots (CF.xc es)) i)
  = let x = CF.xc es in
    let y = Y.ycabs x.w.cyng in
    rsd_eq sty es tv n sl;
    Seq.lemma_index_app1 (LV.yroots y x.w.croots) (LV.yrem (cabs (CF.hof x)) y sl) i;
    Seq.lemma_index_app1 (LV.yroots y x.w.croots) (LV.yrem (cabs (CF.hof x)) y (dds sl)) i

/// **The start's roots, from akhil's rewritten glue roots** (`CodeFFMinor.start_roots`).
#push-options "--z3rlimit 40"
let start_roots_d (sty: style) (es: list event) (tv: seq U64.t) (n: nat) (sl: list M.slot) (mr: seq U64.t) (u: U64.t)
  : Lemma (requires CF.good sty es /\ FMi.rem_ok (CF.xc es) /\ tbl_d tv n sl (CF.xc es).w.crem /\
                    minor_infix_wf (CF.xc es).w.cyng /\
                    (let x = CF.xc es in
                     CB.cheney_no_oom (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp (rsd x tv n) /\
                     (forall (u: U64.t). Seq.mem u mr <==>
                        (exists (a: nat). L.memP (M.VPtr (M.Major a)) x.w.croots /\ u == concv (M.VPtr (M.Major a))))))
          (ensures (let x = CF.xc es in
                    let x' = CF.xc (L.append es [EMinor]) in
                    let rs = rsd x tv n in
                    let rs2 = GP.rewrite_roots rs
                                (C.cheney_promote (gph x.ph) x.w.cyng (CF.hof x) (CF.sof x).fp rs).GP.fwd_map in
                    let k = Seq.length (LV.yroots (Y.ycabs x.w.cyng) x.w.croots) in
                    CF.good sty (L.append es [EMinor]) /\ k <= Seq.length rs2 /\
                    (Seq.mem u (Seq.append (Seq.slice rs2 0 k) mr) <==>
                     Seq.mem u (BM.root_ws (cabs (CF.hof x')) x'.w.croots))))
  = let x = CF.xc es in
    let ms = x.w.cyng in
    let g = CF.hof x in
    let fp = (CF.sof x).fp in
    let rs = rsd x tv n in
    let rm = FMi.mroots x in
    let k = Seq.length (LV.yroots (Y.ycabs ms) x.w.croots) in
    promote_d sty es tv n sl;
    no_oom_d sty es tv n sl;
    FMi.start_roots sty es mr u;
    let fwd = (C.cheney_promote (gph x.ph) ms g fp rs).GP.fwd_map in
    rsd_eq sty es tv n sl;
    FMi.prefix_mem rs fwd k u;
    FMi.prefix_mem rm fwd k u;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (prefix_same sty es tv n sl));
    Seq.lemma_mem_append (Seq.slice (GP.rewrite_roots rs fwd) 0 k) mr;
    Seq.lemma_mem_append (Seq.slice (GP.rewrite_roots rm fwd) 0 k) mr
#pop-options
