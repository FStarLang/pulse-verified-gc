module GC.Spec.FreeLists.Push

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass
open GC.Spec.FreeLists

module U64 = FStar.UInt64
module Seq = FStar.Seq
module AL = GC.Spec.Allocator.Lemmas
module AC = GC.Spec.Allocator.Lemmas.Chain
module G = GC.Spec.Graph
module HG = GC.Spec.HeapGraph
module HM = GC.Spec.HeapModel

/// ---------------------------------------------------------------------------
/// Counting the cells of a chain
/// ---------------------------------------------------------------------------

/// The cells the chain from `fp` visits within `n` steps, in order.
let rec cells (g: heap) (fp: U64.t) (n: nat) : GTot G.vertex_list (decreases n) =
  if n = 0 || fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size ||
     U64.v fp % U64.v mword <> 0
  then Seq.empty
  else begin
    let hd = hd_address (fp <: obj_addr) in
    if U64.v hd + 16 > heap_size then Seq.create 1 (fp <: hp_addr)
    else Seq.cons (fp <: hp_addr) (cells g (read_word g (fp <: obj_addr)) (n - 1))
  end

/// The cells are distinct objects, exactly the addresses the walk meets, and
/// the walk ends after as many steps as there are cells.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let rec cells_props (g: heap) (fp: U64.t) (n: nat)
  : Lemma (requires AL.fl_valid g fp n /\ AL.fl_chain_terminates g fp n)
          (ensures (let s = cells g fp n in
                    G.is_vertex_set s /\
                    Seq.length s <= n /\
                    AL.fl_chain_terminates g fp (Seq.length s) /\
                    (forall (y: hp_addr). Seq.mem y s <==>
                       AL.chain_avoids g fp (y <: U64.t) n = false) /\
                    (forall (y: hp_addr). Seq.mem y s ==>
                       U64.v y >= U64.v mword /\
                       Seq.mem (y <: obj_addr) (objects zero_addr g))))
          (decreases n)
  = let s = cells g fp n in
    if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size ||
       U64.v fp % U64.v mword <> 0 then begin
      AL.fl_chain_terminates_terminal g fp 0;
      introduce forall (y: hp_addr). Seq.mem y s <==> AL.chain_avoids g fp (y <: U64.t) n = false
      with AC.chain_avoids_terminal g fp (y <: U64.t) n
    end
    else if n = 0 then AL.fl_chain_terminates_valid_zero g fp
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      AL.fl_valid_elim g fp n;
      (if AL.chain_avoids g fp fp n then AL.chain_avoids_head_ne g fp fp n);
      if U64.v hd + 16 > heap_size then begin
        AL.fl_chain_terminates_step g fp 1;
        G.is_vertex_set_singleton (fp <: hp_addr);
        assert (Seq.equal s (Seq.cons (fp <: hp_addr) Seq.empty));
        introduce forall (y: hp_addr). Seq.mem y s <==> AL.chain_avoids g fp (y <: U64.t) n = false
        with begin
          Seq.mem_cons (fp <: hp_addr) (Seq.empty #hp_addr);
          if (y <: U64.t) = fp then () else AC.chain_avoids_terminal g fp (y <: U64.t) n
        end;
        introduce forall (y: hp_addr). Seq.mem y s ==>
          U64.v y >= U64.v mword /\ Seq.mem (y <: obj_addr) (objects zero_addr g)
        with Seq.mem_cons (fp <: hp_addr) (Seq.empty #hp_addr)
      end
      else begin
        let next = read_word g obj in
        AL.fl_chain_terminates_elim g fp n;
        cells_props g next (n - 1);
        let t = cells g next (n - 1) in
        // fp is not met again after itself
        AC.fl_chain_predecessor_not_in_suffix_b g fp n;
        AC.not_in_fl_chain_b_is_chain_avoids g next fp (n - 1);
        assert (not (Seq.mem (fp <: hp_addr) t));
        G.is_vertex_set_cons (fp <: hp_addr) t;
        assert (Seq.equal s (Seq.cons (fp <: hp_addr) t));
        AL.fl_chain_terminates_step g fp (Seq.length s);
        introduce forall (y: hp_addr). Seq.mem y s <==> AL.chain_avoids g fp (y <: U64.t) n = false
        with begin
          Seq.mem_cons (fp <: hp_addr) t;
          if (y <: U64.t) = fp then () else AC.chain_avoids_unfold_step g fp (y <: U64.t) n
        end;
        introduce forall (y: hp_addr). Seq.mem y s ==>
          U64.v y >= U64.v mword /\ Seq.mem (y <: obj_addr) (objects zero_addr g)
        with Seq.mem_cons (fp <: hp_addr) t
      end
    end
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let rec coerce_length (s: Seq.seq obj_addr)
  : Lemma (ensures Seq.length (HG.coerce_to_vertex_list s) == Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then () else coerce_length (Seq.tail s)
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let terminates_with_room g fp c =
  cells_props g fp heap_words;
  let s = cells g fp heap_words in
  assert (not (Seq.mem (c <: hp_addr) s));
  G.is_vertex_set_cons (c <: hp_addr) s;
  let s' = Seq.cons (c <: hp_addr) s in
  let objs = HG.coerce_to_vertex_list (objects zero_addr g) in
  HM.objects_is_vertex_set g;
  introduce forall (y: hp_addr). Seq.mem y s' ==> Seq.mem y objs
  with introduce _ ==> _
  with begin
    Seq.mem_cons (c <: hp_addr) s;
    if y = (c <: hp_addr) then HG.coerce_mem_lemma (objects zero_addr g) c
    else HG.coerce_mem_lemma (objects zero_addr g) (y <: obj_addr)
  end;
  G.subset_vertices_length_lemma s' objs;
  coerce_length (objects zero_addr g);
  objects_count_le_remaining zero_addr g;
  assert (Seq.length s + 1 <= heap_words);
  AC.fl_chain_terminates_weaken g fp (Seq.length s) (heap_words - 1)
#pop-options

/// ---------------------------------------------------------------------------
/// The push
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let fls_push g fls c =
  let r = size_class (U64.v (wosize_of_object c g)) in
  size_class_lt (U64.v (wosize_of_object c g));
  let old = fls_head fls r in
  let g' = write_word g (c <: hp_addr) old in
  let fls' = fls_set fls r (c <: U64.t) in
  fls_valid_elim g fls;
  fls_terminates_elim g fls;
  // The write is the link word of `c`, inside its body.
  hd_address_spec c;
  wosize_of_object_spec c g;
  wfh_part1_obj_bound g c;
  AL.write_body_preserves_objects_local zero_addr g c (c <: hp_addr) old;
  introduce forall (a: hp_addr). a <> (c <: hp_addr) ==> read_word g' a == read_word g a
  with introduce _ ==> _ with read_write_different g (c <: hp_addr) a old;
  let ext (a: hp_addr)
    : Lemma (requires U64.v a + U64.v mword <= U64.v (hd_address c) \/
                      U64.v a >= U64.v c + U64.v (wosize_of_object c g) * U64.v mword)
            (ensures read_word g' a == read_word g a)
    = read_write_different g (c <: hp_addr) a old
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires ext);
  fls_frame_extent g g' fls c;
  fls_valid_elim g' fls;
  fls_terminates_elim g' fls;
  fls_avoids_iff g fls (c <: U64.t);
  // The old head of list r is not c, and its chain avoids c.
  assert (AL.chain_avoids g old (c <: U64.t) heap_words = true);
  assert (AL.chain_avoids g' old (c <: U64.t) heap_words = true);
  (if old = (c <: U64.t) then AL.chain_avoids_head_ne g old (c <: U64.t) heap_words);
  // Room for one more step.
  terminates_with_room g' old c;
  read_write_same g (c <: hp_addr) old;
  wosize_of_object_spec c g';
  assert (read_word g' (hd_address c) == read_word g (hd_address c));
  GC.Spec.Allocator.Lemmas.Common.fl_valid_weaken g' old heap_words (heap_words - 1);
  AL.fl_valid_step g' (c <: U64.t) heap_words;
  AL.fl_chain_terminates_step g' (c <: U64.t) heap_words;
  // What the new list visits: c, then the old list.
  let met (y: U64.t)
    : Lemma (AL.chain_avoids g' (c <: U64.t) y heap_words ==
             (AL.chain_avoids g old y heap_words && y <> (c <: U64.t)))
    = if y = (c <: U64.t) then begin
        if AL.chain_avoids g' (c <: U64.t) y heap_words
        then AL.chain_avoids_head_ne g' (c <: U64.t) y heap_words
      end
      else begin
        AC.chain_avoids_unfold_step g' (c <: U64.t) y heap_words;
        if AL.chain_avoids g' old y (heap_words - 1) then
          AC.chain_avoids_strengthen g' old y (heap_words - 1) heap_words
        else if AL.chain_avoids g' old y heap_words
        then AC.chain_avoids_weaken g' old y heap_words (heap_words - 1)
      end
  in
  FStar.Classical.forall_intro met;
  // The class of the new list: c has class r, the old cells do too.
  let cls (y: obj_addr)
    : Lemma (requires Seq.mem y (objects zero_addr g') /\
                      size_class (U64.v (wosize_of_object y g')) <> r)
            (ensures AL.chain_avoids g' (c <: U64.t) (y <: U64.t) heap_words = true)
    = met (y <: U64.t);
      assert (chain_class g' old r);
      if y = c then ()
      else assert (AL.chain_avoids g' old (y <: U64.t) heap_words = true)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires cls);
  assert (chain_class g' (c <: U64.t) r);
  let per (i: nat{i < n_lists})
    : Lemma (AL.fl_valid g' (fls_head fls' i) heap_words /\
             chain_class g' (fls_head fls' i) i /\
             AL.fl_chain_terminates g' (fls_head fls' i) heap_words /\
             (forall (y: U64.t).
                AL.chain_avoids g' (fls_head fls' i) y heap_words ==
                (AL.chain_avoids g (fls_head fls i) y heap_words &&
                 (i <> r || y <> (c <: U64.t)))))
    = fls_head_set fls r i (c <: U64.t)
  in
  FStar.Classical.forall_intro per;
  fls_valid_intro g' fls';
  fls_terminates_intro g' fls'
#pop-options
