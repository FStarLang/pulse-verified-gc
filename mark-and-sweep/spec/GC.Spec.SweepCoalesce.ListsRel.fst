/// ---------------------------------------------------------------------------
/// GC.Spec.SweepCoalesce.ListsRel - the list sweep against the one-list sweep
/// ---------------------------------------------------------------------------
///
/// `fused_sweep_coalesce_lists` and `fused_sweep_coalesce` make the same writes
/// in the same order; only the value a flushed run gets in its link word
/// differs.  So, step by step:
///
///   - the two heaps agree everywhere except at the link words of the cells of
///     the one-list pass's free list;
///   - that free list, and every class list, is descending and lies below the
///     current position of the walk;
///   - class list `i` reaches exactly the cells of the one list whose class is
///     `i`.
///
/// Descending lists are what make every write of the walk, which happens at
/// or above the current position, a frame for all of them.

module GC.Spec.SweepCoalesce.ListsRel

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass
open GC.Spec.FreeLists
open GC.Lib.Header

module Defs = GC.Spec.SweepCoalesce.Defs
module SCL = GC.Spec.SweepCoalesce.Lists
module SpecCoalesce = GC.Spec.Coalesce
module FL = GC.Spec.FreeList
module FD = GC.Spec.FreeList.Descending
module Ind = GC.Spec.SweepCoalesce.Induction
module HeapGraph = GC.Spec.HeapGraph

#set-options "--z3rlimit 20 --fuel 0 --ifuel 0"

/// The class of a cell, read from its header.
let cls (g: heap) (y: U64.t) : GTot nat =
  if U64.v y >= U64.v mword && U64.v y < heap_size && U64.v y % U64.v mword = 0
  then size_class (U64.v (wosize_of_object (y <: obj_addr) g))
  else 0

/// ---------------------------------------------------------------------------
/// Descending chains
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let not_node_unreachable (g: heap) (fp y: U64.t)
  : Lemma (requires ~(FL.fl_node fp))
          (ensures ~(FL.reachable_on_fl g fp y))
  = introduce forall (n: nat). ~(FL.on_fl g fp y n)
    with (if n = 0 then () else ())
#pop-options

/// One step of a descending chain.
#push-options "--fuel 1 --ifuel 1"
let desc_unfold (g: heap) (fp: U64.t) (b: nat)
  : Lemma (requires FD.fl_desc_chain g fp b /\ fp <> 0UL)
          (ensures U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                   U64.v fp % U64.v mword = 0 /\
                   U64.v fp - U64.v mword + 2 * U64.v mword <= b /\
                   is_blue (fp <: obj_addr) g /\
                   U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
                   FD.fl_desc_chain g (read_word g (fp <: obj_addr)) (U64.v fp - U64.v mword))
  = ()
#pop-options

/// Reachability on a descending chain reads only the words below its bound,
/// and every cell lies below it.
#push-options "--z3rlimit 30"
let rec desc_reach_frame (g g': heap) (fp: U64.t) (b: nat) (y: U64.t)
  : Lemma (requires FD.fl_desc_chain g fp b /\ b <= heap_size /\
                    (forall (a: hp_addr). U64.v a + U64.v mword <= b ==> read_word g' a == read_word g a))
          (ensures (FL.reachable_on_fl g' fp y <==> FL.reachable_on_fl g fp y) /\
                   (FL.reachable_on_fl g fp y ==>
                      FL.fl_node y /\ U64.v y + U64.v mword <= b) /\
                   FD.fl_desc_chain g' fp b)
          (decreases b)
  = FD.fl_desc_chain_frame g g' fp b;
    if fp = 0UL then begin
      not_node_unreachable g fp y;
      not_node_unreachable g' fp y
    end
    else begin
      desc_unfold g fp b;
      let o : obj_addr = fp in
      let nx = read_word g o in
      assert (read_word g' o == nx);
      assert (FL.fl_node fp);
      assert (FL.fl_next g fp == nx);
      assert (FL.fl_next g' fp == nx);
      desc_reach_frame g g' nx (U64.v fp - U64.v mword) y;
      if y = fp then begin
        FL.reachable_head g fp;
        FL.reachable_head g' fp
      end
      else begin
        (if FL.reachable_on_fl g fp y then FL.reachable_uncons g fp y);
        (if FL.reachable_on_fl g' fp y then FL.reachable_uncons g' fp y);
        (if FL.reachable_on_fl g nx y then FL.reachable_cons g fp y);
        (if FL.reachable_on_fl g' nx y then FL.reachable_cons g' fp y)
      end
    end
#pop-options

/// The cells of the chain from `p` are `p` and the cells of its tail.
let reach_cons (g: heap) (p: U64.t) (y: U64.t)
  : Lemma (requires FL.fl_node p)
          (ensures FL.reachable_on_fl g p y <==>
                   (y == p \/ FL.reachable_on_fl g (FL.fl_next g p) y))
  = if y = p then FL.reachable_head g p
    else begin
      (if FL.reachable_on_fl g p y then FL.reachable_uncons g p y);
      (if FL.reachable_on_fl g (FL.fl_next g p) y then FL.reachable_cons g p y)
    end

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// `hs, fp`: the one-list pass; `hm, fls`: the list pass; `b`: everything
/// below `b` is final, everything at or above it is still to be written.
let inv (hs hm: heap) (fp: U64.t) (fls: fl_state) (b: nat) : prop =
  b <= heap_size /\
  Seq.length fls == n_lists /\
  (forall (a: hp_addr). ~(FL.reachable_on_fl hs fp (a <: U64.t)) ==>
     read_word hm a == read_word hs a) /\
  FD.fl_desc_chain hs fp b /\
  (forall (i: nat). i < n_lists ==> FD.fl_desc_chain hm (fls_head fls i) b) /\
  (forall (i: nat) (y: U64.t). i < n_lists ==>
     (FL.reachable_on_fl hm (fls_head fls i) y <==>
      (FL.reachable_on_fl hs fp y /\ cls hs y == i)))

let inv_weaken (hs hm: heap) (fp: U64.t) (fls: fl_state) (b b': nat)
  : Lemma (requires inv hs hm fp fls b /\ b <= b' /\ b' <= heap_size)
          (ensures inv hs hm fp fls b')
  = FD.fl_desc_chain_weaken hs fp b b';
    introduce forall (i: nat). i < n_lists ==> FD.fl_desc_chain hm (fls_head fls i) b'
    with introduce _ ==> _ with FD.fl_desc_chain_weaken hm (fls_head fls i) b b'

/// The header of a cell lies below the bound.
#push-options "--z3rlimit 30"
let cell_header_below (g: heap) (fp: U64.t) (b: nat) (y: U64.t)
  : Lemma (requires FD.fl_desc_chain g fp b /\ b <= heap_size /\ FL.reachable_on_fl g fp y)
          (ensures FL.fl_node y /\ U64.v y + U64.v mword <= b /\
                   U64.v (hd_address (y <: obj_addr)) + U64.v mword <= b)
  = desc_reach_frame g g fp b y;
    hd_address_spec (y <: obj_addr)
#pop-options

/// Both passes write the same values at or above `b`, and nothing below it.
#push-options "--z3rlimit 60"
let inv_frame (hs hm hs' hm': heap) (fp: U64.t) (fls: fl_state) (b: nat)
  : Lemma (requires inv hs hm fp fls b /\
                    (forall (a: hp_addr). U64.v a + U64.v mword <= b ==>
                       read_word hs' a == read_word hs a /\ read_word hm' a == read_word hm a) /\
                    (forall (a: hp_addr). U64.v a + U64.v mword > b ==>
                       read_word hm' a == read_word hs' a))
          (ensures inv hs' hm' fp fls b)
  = let rs (y: U64.t)
      : Lemma ((FL.reachable_on_fl hs' fp y <==> FL.reachable_on_fl hs fp y) /\
               (FL.reachable_on_fl hs fp y ==> cls hs' y == cls hs y))
      = desc_reach_frame hs hs' fp b y;
        if FL.reachable_on_fl hs fp y then begin
          cell_header_below hs fp b y;
          wosize_of_object_spec (y <: obj_addr) hs;
          wosize_of_object_spec (y <: obj_addr) hs'
        end
    in
    FStar.Classical.forall_intro rs;
    FD.fl_desc_chain_frame hs hs' fp b;
    let rm (i: nat{i < n_lists}) (y: U64.t)
      : Lemma (FL.reachable_on_fl hm' (fls_head fls i) y <==>
               FL.reachable_on_fl hm (fls_head fls i) y)
      = desc_reach_frame hm hm' (fls_head fls i) b y
    in
    FStar.Classical.forall_intro_2 rm;
    introduce forall (i: nat). i < n_lists ==> FD.fl_desc_chain hm' (fls_head fls i) b
    with introduce _ ==> _ with FD.fl_desc_chain_frame hm hm' (fls_head fls i) b;
    let eq (a: hp_addr)
      : Lemma (requires ~(FL.reachable_on_fl hs' fp (a <: U64.t)))
              (ensures read_word hm' a == read_word hs' a)
      = rs (a <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires eq)
#pop-options

/// ---------------------------------------------------------------------------
/// One flush
/// ---------------------------------------------------------------------------

let fls_set_same (fls: fl_state) (c: nat)
  : Lemma (requires c < Seq.length fls)
          (ensures fls_set fls c (fls_head fls c) == fls)
  = Seq.lemma_eq_intro (fls_set fls c (fls_head fls c)) fls

/// A word that is not the address of a cell lies at or above the bound, or
/// both heaps agree on it.
#push-options "--z3rlimit 40"
let header_write_step (hs hm: heap) (fp: U64.t) (fls: fl_state) (b: nat) (hd: hp_addr) (v: U64.t)
  : Lemma (requires inv hs hm fp fls b /\ U64.v hd == b)
          (ensures inv (write_word hs hd v) (write_word hm hd v) fp fls b)
  = let hs' = write_word hs hd v in
    let hm' = write_word hm hd v in
    let low (a: hp_addr)
      : Lemma (requires U64.v a + U64.v mword <= b)
              (ensures read_word hs' a == read_word hs a /\ read_word hm' a == read_word hm a)
      = read_write_different hs hd a v;
        read_write_different hm hd a v
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires low);
    let high (a: hp_addr)
      : Lemma (requires U64.v a + U64.v mword > b)
              (ensures read_word hm' a == read_word hs' a)
      = if a = hd then begin
          read_write_same hs hd v; read_write_same hm hd v
        end
        else begin
          read_write_different hs hd a v;
          read_write_different hm hd a v;
          // a is not a cell: cells lie below the bound
          if FL.reachable_on_fl hs fp (a <: U64.t) then
            cell_header_below hs fp b (a <: U64.t)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires high);
    inv_frame hs hm hs' hm' fp fls b
#pop-options

/// Pushing the run at `p` on the one list and on the list of its class.
#push-options "--z3rlimit 80"
let push_step (hs hm: heap) (fp: U64.t) (fls: fl_state) (p: obj_addr) (e: nat) (c: nat)
  : Lemma (requires inv hs hm fp fls (U64.v p - U64.v mword) /\
                    U64.v p - U64.v mword + 2 * U64.v mword <= e /\ e <= heap_size /\
                    is_blue p hs /\ is_blue p hm /\
                    U64.v (wosize_of_object p hs) >= 1 /\
                    read_word hm (hd_address p) == read_word hs (hd_address p) /\
                    c == size_class (U64.v (wosize_of_object p hs)))
          (ensures inv (write_word hs (p <: hp_addr) fp)
                       (write_word hm (p <: hp_addr) (fls_head fls c))
                       (p <: U64.t) (fls_set fls c (p <: U64.t)) e)
  = let b = U64.v p - U64.v mword in
    let hs' = write_word hs (p <: hp_addr) fp in
    let hm' = write_word hm (p <: hp_addr) (fls_head fls c) in
    let fls' = fls_set fls c (p <: U64.t) in
    hd_address_spec p;
    size_class_lt (U64.v (wosize_of_object p hs));
    let low (a: hp_addr)
      : Lemma (requires U64.v a + U64.v mword <= b)
              (ensures read_word hs' a == read_word hs a /\ read_word hm' a == read_word hm a)
      = read_write_different hs (p <: hp_addr) a fp;
        read_write_different hm (p <: hp_addr) a (fls_head fls c)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires low);
    // the header of p is unchanged by the link write
    read_write_different hs (p <: hp_addr) (hd_address p) fp;
    read_write_different hm (p <: hp_addr) (hd_address p) (fls_head fls c);
    wosize_of_object_spec p hs; wosize_of_object_spec p hs';
    wosize_of_object_spec p hm; wosize_of_object_spec p hm';
    color_of_object_spec p hs; color_of_object_spec p hs';
    color_of_object_spec p hm; color_of_object_spec p hm';
    is_blue_iff p hs; is_blue_iff p hs'; is_blue_iff p hm; is_blue_iff p hm';
    read_write_same hs (p <: hp_addr) fp;
    read_write_same hm (p <: hp_addr) (fls_head fls c);
    // the old chains, below b, are untouched
    FD.fl_desc_chain_frame hs hs' fp b;
    FD.fl_desc_chain_cons hs' p e;
    FD.fl_desc_chain_frame hm hm' (fls_head fls c) b;
    FD.fl_desc_chain_cons hm' p e;
    assert (FL.fl_node (p <: U64.t));
    assert (FL.fl_next hs' (p <: U64.t) == fp);
    assert (FL.fl_next hm' (p <: U64.t) == fls_head fls c);
    let per (i: nat{i < n_lists})
      : Lemma (FD.fl_desc_chain hm' (fls_head fls' i) e /\
               (forall (y: U64.t).
                  FL.reachable_on_fl hm' (fls_head fls' i) y <==>
                  (FL.reachable_on_fl hs' (p <: U64.t) y /\ cls hs' y == i)))
      = fls_head_set fls c i (p <: U64.t);
        let one (y: U64.t)
          : Lemma (FL.reachable_on_fl hm' (fls_head fls' i) y <==>
                   (FL.reachable_on_fl hs' (p <: U64.t) y /\ cls hs' y == i))
          = reach_cons hs' (p <: U64.t) y;
            desc_reach_frame hs hs' fp b y;
            desc_reach_frame hm hm' (fls_head fls i) b y;
            (if FL.reachable_on_fl hs fp y then begin
               cell_header_below hs fp b y;
               wosize_of_object_spec (y <: obj_addr) hs;
               wosize_of_object_spec (y <: obj_addr) hs';
               read_write_different hs (p <: hp_addr) (hd_address (y <: obj_addr)) fp
             end);
            if i = c then reach_cons hm' (p <: U64.t) y
        in
        FStar.Classical.forall_intro one;
        if i = c then ()
        else begin
          FD.fl_desc_chain_frame hm hm' (fls_head fls i) b;
          FD.fl_desc_chain_weaken hm' (fls_head fls i) b e
        end
    in
    FStar.Classical.forall_intro per;
    FD.fl_desc_chain_weaken hs' (p <: U64.t) e e;
    let eq (a: hp_addr)
      : Lemma (requires ~(FL.reachable_on_fl hs' (p <: U64.t) (a <: U64.t)))
              (ensures read_word hm' a == read_word hs' a)
      = reach_cons hs' (p <: U64.t) (a <: U64.t);
        desc_reach_frame hs hs' fp b (a <: U64.t);
        read_write_different hs (p <: hp_addr) a fp;
        read_write_different hm (p <: hp_addr) a (fls_head fls c)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires eq)
#pop-options

/// One flush of a pending run, in both passes.
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let flush_step (hs hm: heap) (fp: U64.t) (fls: fl_state) (fb: U64.t) (rw: nat) (b: nat)
  : Lemma (requires inv hs hm fp fls b /\
                    (rw > 0 ==> U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                                U64.v fb % U64.v mword == 0 /\
                                rw - 1 < pow2 54 /\
                                b == U64.v fb - U64.v mword /\
                                U64.v fb - U64.v mword + rw * U64.v mword <= heap_size))
          (ensures (let r = SpecCoalesce.flush_blue hs fb rw fp in
                    let r' = SCL.flush_blue_lists hm fb rw fls in
                    inv (fst r) (fst r') (snd r) (snd r')
                        (if rw > 0 then U64.v fb - U64.v mword + rw * U64.v mword else b)))
  = let c = SCL.run_class rw in
    (if rw >= 2 then size_class_lt (rw - 1));
    assert (c < n_lists);
    let fc = fls_head fls c in
    if rw = 0 then fls_set_same fls c
    else begin
      let p : obj_addr = fb in
      let hd = hd_address p in
      hd_address_spec p;
      let wz = rw - 1 in
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      let wz_u64 : wosize = U64.uint_to_t wz in
      let hdr = makeHeader wz_u64 Blue 0UL in
      let g1s = write_word hs hd hdr in
      let g1m = write_word hm hd hdr in
      header_write_step hs hm fp fls b hd hdr;
      let e = U64.v fb - U64.v mword + rw * U64.v mword in
      if wz >= 1 && U64.v hd + U64.v mword * 2 <= heap_size then begin
        assert (U64.add (hd_address p) (U64.mul mword 1UL) == (p <: U64.t));
        read_write_same hs hd hdr;
        read_write_same hm hd hdr;
        makeHeader_getWosize wz_u64 Blue 0UL;
        makeHeader_getColor wz_u64 Blue 0UL;
        wosize_of_object_spec p g1s;
        color_of_object_spec p g1s;
        color_of_object_spec p g1m;
        is_blue_iff p g1s;
        is_blue_iff p g1m;
        assert (c == size_class (U64.v (wosize_of_object p g1s)));
        push_step g1s g1m fp fls p e c
      end
      else begin
        fls_set_same fls c;
        inv_weaken g1s g1m fp fls b e
      end
    end
#pop-options

/// Whitening a survivor at or above the bound, in both passes.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let white_step (hs hm: heap) (fp: U64.t) (fls: fl_state) (b: nat) (obj: obj_addr)
  : Lemma (requires inv hs hm fp fls b /\ U64.v (hd_address obj) == b)
          (ensures inv (makeWhite obj hs) (makeWhite obj hm) fp fls b)
  = let hd = hd_address obj in
    makeWhite_spec obj hs;
    makeWhite_spec obj hm;
    // the header of obj is no cell's link word, so both passes read the same
    (if FL.reachable_on_fl hs fp (hd <: U64.t) then cell_header_below hs fp b (hd <: U64.t));
    assert (read_word hm hd == read_word hs hd);
    header_write_step hs hm fp fls b hd (colorHeader (read_word hs hd) White)
#pop-options

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let rec rel_aux (g0 hs hm: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat)
    (fp: U64.t) (fls: fl_state) (start: nat)
  : Lemma (requires
             Ind.objs_contiguous g0 objs /\
             (forall (x: obj_addr). Seq.mem x objs ==>
                U64.v x + U64.v (wosize_of_object x g0) * 8 <= heap_size) /\
             start % 8 == 0 /\ start <= heap_size /\
             (Seq.length objs > 0 ==> U64.v (Seq.head objs) == start + 8) /\
             (rw > 0 ==> U64.v fb >= U64.v mword /\ U64.v fb < heap_size /\
                         U64.v fb % U64.v mword == 0 /\ rw - 1 < pow2 54 /\
                         U64.v fb - U64.v mword + rw * U64.v mword == start) /\
             inv hs hm fp fls (if rw > 0 then U64.v fb - U64.v mword else start))
          (ensures (let r = Defs.fused_aux g0 hs objs fb rw fp in
                    let r' = SCL.fused_aux_lists g0 hm objs fb rw fls in
                    inv (fst r) (fst r') (snd r) (snd r') heap_size))
          (decreases Seq.length objs)
  = let b = if rw > 0 then U64.v fb - U64.v mword else start in
    if Seq.length objs = 0 then begin
      flush_step hs hm fp fls fb rw b;
      let r = SpecCoalesce.flush_blue hs fb rw fp in
      let r' = SCL.flush_blue_lists hm fb rw fls in
      inv_weaken (fst r) (fst r') (snd r) (snd r') start heap_size
    end
    else begin
      let obj = Seq.head objs in
      let rest = Seq.tail objs in
      Seq.Properties.cons_head_tail objs;
      let sub (x: obj_addr) : Lemma (Seq.mem x rest ==> Seq.mem x objs)
        = GC.Spec.Fields.mem_cons_lemma x obj rest
      in
      FStar.Classical.forall_intro sub;
      GC.Spec.Fields.mem_cons_lemma obj obj rest;
      hd_address_spec obj;
      let ws = U64.v (wosize_of_object obj g0) in
      let start' = start + (ws + 1) * 8 in
      assert (start' <= heap_size);
      assert (start' % 8 == 0);
      (if Seq.length rest > 0 then assert (U64.v (Seq.head rest) == start' + 8));
      if is_black obj g0 then begin
        flush_step hs hm fp fls fb rw b;
        let r = SpecCoalesce.flush_blue hs fb rw fp in
        let r' = SCL.flush_blue_lists hm fb rw fls in
        white_step (fst r) (fst r') (snd r) (snd r') start obj;
        inv_weaken (makeWhite obj (fst r)) (makeWhite obj (fst r')) (snd r) (snd r') start start';
        rel_aux g0 (makeWhite obj (fst r)) (makeWhite obj (fst r')) rest 0UL 0 (snd r) (snd r') start'
      end
      else begin
        let new_fb : U64.t = if rw = 0 then obj else fb in
        let new_rw = rw + ws + 1 in
        assert_norm (pow2 57 == 8 * pow2 54);
        assert (new_rw * 8 <= heap_size);
        assert (new_rw - 1 < pow2 54);
        rel_aux g0 hs hm rest new_fb new_rw fp fls start'
      end
    end
#pop-options

/// From the object walk: consecutive objects are contiguous ...
#push-options "--z3rlimit 25 --fuel 2 --ifuel 1"
private let rec objects_contiguous_lemma (start: hp_addr) (g: heap)
  : Lemma (requires Seq.length g == heap_size)
          (ensures Ind.objs_contiguous g (objects start g))
          (decreases Seq.length g - U64.v start)
  = let objs = objects start g in
    if Seq.length objs <= 1 then ()
    else begin
      objects_nonempty_next start g;
      f_address_spec start;
      let wz = getWosize (read_word g start) in
      let next_nat = U64.v start + (U64.v wz + 1) * 8 in
      if next_nat >= heap_size then ()
      else begin
        let next : hp_addr = U64.uint_to_t next_nat in
        let hd = f_address start in
        hd_address_spec hd;
        wosize_of_object_spec hd g;
        assert (Seq.length (objects next g) > 0);
        objects_nonempty_next next g;
        f_address_spec next;
        assert (U64.v hd + (U64.v wz + 1) * 8 == next_nat + 8);
        assert (Seq.equal (Seq.tail objs) (objects next g));
        objects_contiguous_lemma next g
      end
    end
#pop-options

/// ... and every object fits in the heap.
#push-options "--z3rlimit 12 --fuel 1 --ifuel 0"
private let objects_fit_lemma (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g))
          (ensures U64.v x + U64.v (wosize_of_object x g) * 8 <= heap_size)
  = objects_member_size_bound zero_addr g x;
    hd_address_spec x;
    wosize_of_object_spec x g
#pop-options

/// **The list pass against the one-list pass.**
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let fused_lists_rel (g: heap)
  : Lemma (let r = Defs.fused_sweep_coalesce g in
           let r' = SCL.fused_sweep_coalesce_lists g in
           inv (fst r) (fst r') (snd r) (snd r') heap_size)
  = let objs = objects zero_addr g in
    objects_contiguous_lemma zero_addr g;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (objects_fit_lemma g));
    if Seq.length objs > 0 then begin
      objects_nonempty_head zero_addr g;
      f_address_spec zero_addr
    end;
    let fls0 = fls_empty in
    let init (i: nat{i < n_lists}) (y: U64.t)
      : Lemma (FD.fl_desc_chain g (fls_head fls0 i) (U64.v zero_addr) /\
               ~(FL.reachable_on_fl g (fls_head fls0 i) y))
      = not_node_unreachable g (fls_head fls0 i) y
    in
    FStar.Classical.forall_intro_2 init;
    introduce forall (y: U64.t). ~(FL.reachable_on_fl g 0UL y)
    with not_node_unreachable g 0UL y;
    assert (inv g g 0UL fls0 (U64.v zero_addr));
    rel_aux g g g objs 0UL 0 0UL fls0 (U64.v zero_addr)
#pop-options
