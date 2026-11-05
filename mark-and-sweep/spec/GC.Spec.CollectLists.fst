/// ---------------------------------------------------------------------------
/// GC.Spec.CollectLists - where the collector's free lists come from
/// ---------------------------------------------------------------------------
///
/// The collector's result is related to the reference spec `coalesce (sweep
/// h_mark 0UL)` of some correct mark `h_mark`, which builds one free list.  The
/// heap agrees with it modulo free blocks' bodies and link words
/// (`heaps_agree_mod_free_links`), and the lists are its one list split by
/// class (`fls_of_chain`).  The sweep rebuilds every list, so the reference
/// sweep starts from an empty list, `0UL`.

module GC.Spec.CollectLists

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass
open GC.Spec.FreeLists

module U64 = FStar.UInt64
module Corr = GC.Spec.Correctness
module Coalesce = GC.Spec.Coalesce
module CC = GC.Spec.Coalesce.Complete
module FL = GC.Spec.FreeList
module FD = GC.Spec.FreeList.Descending
module HA = GC.Spec.HeapAgree
module HAL = GC.Spec.HeapAgree.Lists
module SC = GC.Spec.SweepCoalesce
module Defs = GC.Spec.SweepCoalesce.Defs
module SCL = GC.Spec.SweepCoalesce.Lists
module Rel = GC.Spec.SweepCoalesce.ListsRel
module SpecSweep = GC.Spec.Sweep

/// The lists `fls` in `s2` are the chain from `fp` in `c` split by class: list
/// `i` reaches exactly the cells of class `i`, and each list is descending
/// (strictly decreasing addresses).  The chain from `fp` is descending too
/// (`GC.Spec.Coalesce.Descending`), so each list is that chain's class-`i`
/// cells in the same order.
let fls_of_chain (s2: heap) (fls: fl_state) (c: heap) (fp: U64.t) : prop =
  Seq.length fls == n_lists /\
  (forall (i: nat). i < n_lists ==> FD.fl_desc_chain s2 (fls_head fls i) heap_size) /\
  (forall (i: nat) (y: U64.t). i < n_lists ==>
     (FL.reachable_on_fl s2 (fls_head fls i) y <==>
      (FL.reachable_on_fl c fp y /\ Rel.cls c y == i)))

/// The free lists `fls` and the heap `s2` come from coalescing the sweep of a
/// correct mark of `h_init`.
let gc_coalesce_source_lists
  (h_init s2: heap) (roots: seq obj_addr) (fls: fl_state) : prop =
  exists (h_mark: heap).
    Corr.mark_post h_init h_mark roots 0UL /\
    (let r = Coalesce.coalesce (fst (SpecSweep.sweep h_mark 0UL)) in
     HA.heaps_agree_mod_free_links s2 (fst r) /\ fls_of_chain s2 fls (fst r) (snd r))

/// The pass the collector runs produces such lists.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let gc_coalesce_source_lists_intro
  (h_init h_mark: heap) (roots: seq obj_addr) (s2: heap) (fls: fl_state)
  : Lemma (requires Corr.mark_post h_init h_mark roots 0UL /\
                    well_formed_heap h_mark /\
                    heap_objects_dense h_mark /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr h_mark) ==>
                       ~(is_gray x h_mark)) /\
                    (s2, fls) == SCL.fused_sweep_coalesce_lists h_mark)
          (ensures gc_coalesce_source_lists h_init s2 roots fls /\
                   HA.heaps_agree_mod_free_links s2
                     (fst (Coalesce.coalesce (fst (SpecSweep.sweep h_mark 0UL)))))
  = let hs = fst (Defs.fused_sweep_coalesce h_mark) in
    let fp = snd (Defs.fused_sweep_coalesce h_mark) in
    let g = fst (SpecSweep.sweep h_mark 0UL) in
    let r = Coalesce.coalesce g in
    let c = fst r in
    Rel.fused_lists_rel h_mark;
    SC.fused_agrees_sweep_coalesce h_mark 0UL;
    assert (fp == snd r);
    Corr.sweep_post_sweep_strong_gen h_init h_mark roots 0UL;
    CC.coalesce_exact g;
    assert (FL.fl_exact c fp);
    HA.agree_fl_exact hs c fp;
    // s2 and hs differ only at link words of the one list's cells, which are
    // blue blocks with a field
    let not_cell (a: hp_addr)
      : Lemma (requires ~(HAL.blue_link_word hs a))
              (ensures read_word s2 a == read_word hs a)
      = if FL.reachable_on_fl hs fp (a <: U64.t) then begin
          assert (FL.fl_sound hs fp);
          assert (HAL.blue_link_word hs a)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires not_cell);
    HAL.agree_links_except_blue_links s2 hs;
    HA.agree_links_trans s2 hs c;
    // the one list, and the class of each of its cells, are the same in hs and c
    let same (i: nat{i < n_lists}) (y: U64.t)
      : Lemma (FL.reachable_on_fl s2 (fls_head fls i) y <==>
               (FL.reachable_on_fl c fp y /\ Rel.cls c y == i))
      = HAL.agree_reachable hs c fp y;
        if FL.reachable_on_fl hs fp y then begin
          assert (FL.fl_sound hs fp);
          HA.agree_block hs c (y <: obj_addr)
        end
    in
    FStar.Classical.forall_intro_2 same;
    assert (fls_of_chain s2 fls c fp)
#pop-options

/// ---------------------------------------------------------------------------
/// What the lists are
/// ---------------------------------------------------------------------------

module AL = GC.Spec.Allocator.Lemmas
module AC = GC.Spec.Allocator.Lemmas.Chain

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let rec on_fl_not_avoids (g: heap) (fp y: U64.t) (n: nat)
  : Lemma (requires FL.on_fl g fp y n)
          (ensures AL.chain_avoids g fp y n = false)
          (decreases n)
  = if fp = y then begin
      if AL.chain_avoids g fp y n then AL.chain_avoids_head_ne g fp y n
    end
    else begin
      hd_address_spec (fp <: obj_addr);
      on_fl_not_avoids g (FL.fl_next g fp) y (n - 1);
      AC.chain_avoids_unfold_step g fp y n
    end

private let rec not_avoids_on_fl (g: heap) (fp y: U64.t) (n: nat)
  : Lemma (requires AL.chain_avoids g fp y n = false /\ FL.fl_node y)
          (ensures FL.on_fl g fp y n)
          (decreases n)
  = if n = 0 then AC.chain_avoids_zero g fp y
    else if fp = y then ()
    else if not (FL.fl_node fp) then begin
      if U64.v fp >= U64.v mword && U64.v fp % U64.v mword = 0 && U64.v fp < heap_size
      then hd_address_spec (fp <: obj_addr);
      AC.chain_avoids_terminal g fp y n
    end
    else begin
      hd_address_spec (fp <: obj_addr);
      AC.chain_avoids_unfold_step g fp y n;
      not_avoids_on_fl g (FL.fl_next g fp) y (n - 1)
    end

/// The successor of a reached cell is reached, if it is a cell.
#push-options "--fuel 2"
private let rec on_fl_next (g: heap) (fp y: U64.t) (n: nat)
  : Lemma (requires FL.on_fl g fp y n /\ FL.fl_node y /\ FL.fl_node (FL.fl_next g y))
          (ensures FL.on_fl g fp (FL.fl_next g y) (n + 1))
          (decreases n)
  = if fp = y then ()
    else on_fl_next g (FL.fl_next g fp) y (n - 1)
#pop-options
#pop-options

/// On a terminating chain, being reached is being met within `heap_words` steps.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let reachable_iff_met (g: heap) (fp y: U64.t)
  : Lemma (requires AL.fl_chain_terminates g fp heap_words)
          (ensures FL.reachable_on_fl g fp y <==>
                   (FL.fl_node y /\ AL.chain_avoids g fp y heap_words = false))
  = introduce FL.reachable_on_fl g fp y ==>
              (FL.fl_node y /\ AL.chain_avoids g fp y heap_words = false)
    with begin
      FL.reachable_is_node g fp y;
      eliminate exists (n: nat). FL.on_fl g fp y n
      with begin
        on_fl_not_avoids g fp y n;
        if AL.chain_avoids g fp y heap_words then begin
          if n <= heap_words then AC.chain_avoids_weaken g fp y heap_words n
          else AC.chain_avoids_strengthen g fp y heap_words n
        end
      end
    end;
    introduce (FL.fl_node y /\ AL.chain_avoids g fp y heap_words = false) ==>
              FL.reachable_on_fl g fp y
    with not_avoids_on_fl g fp y heap_words

let reachable_next (g: heap) (fp y: U64.t)
  : Lemma (requires FL.reachable_on_fl g fp y /\ FL.fl_node y /\ FL.fl_node (FL.fl_next g y))
          (ensures FL.reachable_on_fl g fp (FL.fl_next g y))
  = eliminate exists (n: nat). FL.on_fl g fp y n
    with on_fl_next g fp y n
#pop-options

/// On a descending chain, the successor of a reached cell is the end of the
/// chain or another reached cell.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let rec desc_next (g: heap) (fp: U64.t) (b: nat) (y: U64.t)
  : Lemma (requires FD.fl_desc_chain g fp b /\ b <= heap_size /\ FL.reachable_on_fl g fp y)
          (ensures FL.fl_node y /\
                   (FL.fl_next g y == 0UL \/
                    (FL.fl_node (FL.fl_next g y) /\ FL.reachable_on_fl g fp (FL.fl_next g y))))
          (decreases b)
  = Rel.desc_reach_frame g g fp b y;
    if fp = 0UL then ()
    else begin
      Rel.desc_unfold g fp b;
      let nx = read_word g (fp <: obj_addr) in
      assert (FL.fl_next g fp == nx);
      if y = fp then begin
        if nx = 0UL then ()
        else begin
          Rel.desc_unfold g nx (U64.v fp - U64.v mword);
          assert (FL.fl_node nx);
          reachable_next g fp y
        end
      end
      else begin
        FL.reachable_uncons g fp y;
        desc_next g nx (U64.v fp - U64.v mword) y;
        let ny = FL.fl_next g y in
        if ny <> 0UL then FL.reachable_cons g fp ny
      end
    end
#pop-options

/// The pieces of the source, at a chosen marked heap.
let source_at (h_init s2: heap) (roots: seq obj_addr) (fls: fl_state) (h_mark: heap) : prop =
  Corr.mark_post h_init h_mark roots 0UL /\
  (let r = Coalesce.coalesce (fst (SpecSweep.sweep h_mark 0UL)) in
   HA.heaps_agree_mod_free_links s2 (fst r) /\ fls_of_chain s2 fls (fst r) (snd r))

/// **What the collector's lists are**: valid, terminating lists of their
/// classes, exact, holding no live object, whose heads and links are null or
/// pointers.
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let gc_coalesce_source_lists_facts
  (h_init s2: heap) (roots: seq obj_addr) (fls: fl_state)
  : Lemma (requires gc_coalesce_source_lists h_init s2 roots fls)
          (ensures fls_valid s2 fls /\ fls_terminates s2 fls /\ fls_exact s2 fls /\
                   (forall (obj: obj_addr). Seq.mem obj (objects zero_addr s2) /\
                      ~(is_blue obj s2) ==> fls_avoids s2 fls (obj <: U64.t)) /\
                   (forall (i: nat). i < n_lists ==>
                      fls_head fls i == 0UL \/ HeapGraph.is_pointer_field (fls_head fls i)) /\
                   (forall (a: obj_addr).
                      Seq.mem a (objects zero_addr s2) /\ is_blue a s2 /\
                      U64.v (wosize_of_object a s2) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size ==>
                      (let v = read_word s2 a in v = 0UL \/ HeapGraph.is_pointer_field v)))
  = let h_mark = FStar.IndefiniteDescription.indefinite_description_ghost heap
      (fun h_mark -> source_at h_init s2 roots fls h_mark) in
    let g = fst (SpecSweep.sweep h_mark 0UL) in
    let r = Coalesce.coalesce g in
    let c = fst r in
    let fp = snd r in
    Corr.sweep_post_sweep_strong_gen h_init h_mark roots 0UL;
    CC.coalesce_exact g;
    assert (FL.fl_exact c fp);
    HA.agree_objects_links s2 c;
    let blk (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr c) ==>
               is_blue x s2 == is_blue x c /\ wosize_of_object x s2 == wosize_of_object x c)
      = if Seq.mem x (objects zero_addr c) then HA.agree_block_links s2 c x
    in
    FStar.Classical.forall_intro blk;
    // A reached cell of any list is a blue object with a field.
    let cell (i: nat{i < n_lists}) (y: U64.t)
      : Lemma (requires FL.reachable_on_fl s2 (fls_head fls i) y)
              (ensures FL.fl_node y /\
                       U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0 /\
                       Seq.mem (y <: obj_addr) (objects zero_addr s2) /\
                       is_blue (y <: obj_addr) s2 /\
                       U64.v (wosize_of_object (y <: obj_addr) s2) >= 1 /\
                       size_class (U64.v (wosize_of_object (y <: obj_addr) s2)) == i /\
                       U64.v y >= U64.v zero_addr + U64.v mword)
      = assert (FL.fl_sound c fp);
        objects_addresses_gt_start zero_addr c (y <: obj_addr)
    in
    // The successor of a cell of a list is null or a cell of that list.
    let link (i: nat{i < n_lists}) (y: U64.t)
      : Lemma (requires FL.reachable_on_fl s2 (fls_head fls i) y)
              (ensures read_word s2 (y <: obj_addr) == 0UL \/
                       FL.reachable_on_fl s2 (fls_head fls i) (read_word s2 (y <: obj_addr)))
      = cell i y;
        desc_next s2 (fls_head fls i) heap_size y
    in
    // Every blue object with a field is a cell of the list of its class.
    let member (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr s2) /\ is_blue x s2 /\
                        U64.v (wosize_of_object x s2) >= 1)
              (ensures (let k = size_class (U64.v (wosize_of_object x s2)) in
                        k < n_lists /\ FL.reachable_on_fl s2 (fls_head fls k) (x <: U64.t)))
      = size_class_lt (U64.v (wosize_of_object x s2));
        assert (FL.fl_complete c fp)
    in
    // Each list is valid and terminates.
    let per (i: nat{i < n_lists})
      : Lemma (AL.fl_valid s2 (fls_head fls i) heap_words /\
               AL.fl_chain_terminates s2 (fls_head fls i) heap_words)
      = let mem_step (a: U64.t)
          : Lemma (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\
                            U64.v a % U64.v mword == 0 /\
                            Seq.mem (a <: obj_addr) (objects zero_addr s2) /\
                            is_blue (a <: obj_addr) s2 /\
                            U64.v (wosize_of_object (a <: obj_addr) s2) >= 1)
                  (ensures (let n = read_word s2 (a <: obj_addr) in
                            n == 0UL \/
                            (U64.v n >= U64.v mword /\ U64.v n < heap_size /\
                             U64.v n % U64.v mword == 0 /\
                             Seq.mem (n <: obj_addr) (objects zero_addr s2))))
          = member (a <: obj_addr);
            let k = size_class (U64.v (wosize_of_object (a <: obj_addr) s2)) in
            link k a;
            let n = read_word s2 (a <: obj_addr) in
            if n <> 0UL then cell k n
        in
        let hd0 = fls_head fls i in
        (if hd0 <> 0UL then begin
           Rel.desc_unfold s2 hd0 heap_size;
           FL.reachable_head s2 hd0;
           cell i hd0
         end);
        FD.fl_desc_chain_gives_valid s2 hd0 mem_step
    in
    FStar.Classical.forall_intro per;
    // Each list holds only its own class.
    let cls_ok (i: nat{i < n_lists})
      : Lemma (chain_class s2 (fls_head fls i) i)
      = let one (y: obj_addr)
          : Lemma (requires Seq.mem y (objects zero_addr s2) /\
                            size_class (U64.v (wosize_of_object y s2)) <> i)
                  (ensures AL.chain_avoids s2 (fls_head fls i) (y <: U64.t) heap_words = true)
          = per i;
            reachable_iff_met s2 (fls_head fls i) (y <: U64.t);
            if FL.reachable_on_fl s2 (fls_head fls i) (y <: U64.t) then cell i (y <: U64.t)
            else begin
              hd_address_spec y;
              wosize_of_object_bound y s2;
              objects_member_size_bound zero_addr s2 y
            end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires one)
    in
    FStar.Classical.forall_intro cls_ok;
    fls_valid_intro s2 fls;
    fls_terminates_intro s2 fls;
    // Exactness.
    introduce forall (i: nat) (y: U64.t). i < n_lists /\ FL.reachable_on_fl s2 (fls_head fls i) y ==>
      (FL.fl_node y /\
       (U64.v y >= U64.v mword /\ U64.v y < heap_size /\ U64.v y % U64.v mword == 0) /\
       Seq.mem (y <: obj_addr) (objects zero_addr s2) /\
       is_blue (y <: obj_addr) s2 /\
       U64.v (wosize_of_object (y <: obj_addr) s2) >= 1)
    with introduce _ ==> _ with cell i y;
    assert (fls_sound s2 fls);
    FStar.Classical.forall_intro (FStar.Classical.move_requires member);
    assert (fls_complete s2 fls);
    // No live object is on a list.
    let live (obj: obj_addr)
      : Lemma (requires Seq.mem obj (objects zero_addr s2) /\ ~(is_blue obj s2))
              (ensures fls_avoids s2 fls (obj <: U64.t))
      = let one (i: nat{i < n_lists})
          : Lemma (AL.chain_avoids s2 (fls_head fls i) (obj <: U64.t) heap_words = true)
          = per i;
            reachable_iff_met s2 (fls_head fls i) (obj <: U64.t);
            if FL.reachable_on_fl s2 (fls_head fls i) (obj <: U64.t) then cell i (obj <: U64.t)
            else begin
              hd_address_spec obj;
              objects_member_size_bound zero_addr s2 obj
            end
        in
        FStar.Classical.forall_intro one;
        fls_avoids_iff s2 fls (obj <: U64.t)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires live);
    // Heads.
    let head (i: nat{i < n_lists})
      : Lemma (fls_head fls i == 0UL \/ HeapGraph.is_pointer_field (fls_head fls i))
      = let hd0 = fls_head fls i in
        if hd0 <> 0UL then begin
          Rel.desc_unfold s2 hd0 heap_size;
          FL.reachable_head s2 hd0;
          cell i hd0
        end
    in
    FStar.Classical.forall_intro head;
    // Link words of blue blocks.
    let lnk (a: obj_addr)
      : Lemma (requires Seq.mem a (objects zero_addr s2) /\ is_blue a s2 /\
                        U64.v (wosize_of_object a s2) >= 1 /\
                        U64.v (hd_address a) + 16 <= heap_size)
              (ensures (let v = read_word s2 a in v = 0UL \/ HeapGraph.is_pointer_field v))
      = member a;
        let k = size_class (U64.v (wosize_of_object a s2)) in
        link k (a <: U64.t);
        let n = read_word s2 a in
        if n <> 0UL then cell k n
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires lnk)
#pop-options
