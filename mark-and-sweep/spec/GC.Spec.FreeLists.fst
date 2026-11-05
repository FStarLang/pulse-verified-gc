module GC.Spec.FreeLists

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.SizeClass

module U64 = FStar.UInt64
module Seq = FStar.Seq
module AL = GC.Spec.Allocator.Lemmas
module AC = GC.Spec.Allocator.Lemmas.Chain
module FL = GC.Spec.FreeList

let fls_valid g fls =
  Seq.length fls == n_lists /\
  (forall (i: nat). i < n_lists ==>
     AL.fl_valid g (fls_head fls i) heap_words /\
     chain_class g (fls_head fls i) i)

let fls_terminates g fls =
  forall (i: nat). i < n_lists ==>
    AL.fl_chain_terminates g (fls_head fls i) heap_words

let fls_avoids g fls x =
  forall (i: nat). i < n_lists ==>
    AL.chain_avoids g (fls_head fls i) x heap_words = true

let fls_valid_intro g fls = reveal_opaque (`%fls_valid) (fls_valid g fls)
let fls_valid_elim g fls = reveal_opaque (`%fls_valid) (fls_valid g fls)
let fls_terminates_intro g fls = reveal_opaque (`%fls_terminates) (fls_terminates g fls)
let fls_terminates_elim g fls = reveal_opaque (`%fls_terminates) (fls_terminates g fls)
let fls_avoids_iff g fls x = reveal_opaque (`%fls_avoids) (fls_avoids g fls x)

/// ---------------------------------------------------------------------------
/// Cells
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let rec chain_cell_aux (g: heap) (fp: U64.t) (y: U64.t) (n: nat)
  : Lemma (requires AL.fl_valid g fp n /\ AL.chain_avoids g fp y n = false)
          (ensures U64.v y >= U64.v mword /\ U64.v y < heap_size /\
                   U64.v y % U64.v mword == 0 /\
                   Seq.mem (y <: obj_addr) (objects zero_addr g) /\
                   U64.v (wosize_of_object (y <: obj_addr) g) >= 1)
          (decreases n)
  = if n = 0 then AC.chain_avoids_zero g fp y
    else if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size ||
            U64.v fp % U64.v mword <> 0
    then AC.chain_avoids_terminal g fp y n
    else begin
      AL.fl_valid_elim g fp n;
      if fp = y then ()
      else begin
        let hd = hd_address (fp <: obj_addr) in
        if U64.v hd + 16 > heap_size then AC.chain_avoids_terminal g fp y n
        else begin
          AC.chain_avoids_unfold_step g fp y n;
          chain_cell_aux g (read_word g (fp <: obj_addr)) y (n - 1)
        end
      end
    end
#pop-options

let chain_cell_in_objects g fp y = chain_cell_aux g fp y heap_words

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let fls_cell_one_list g fls i j y =
  fls_valid_elim g fls;
  chain_cell_in_objects g (fls_head fls i) (y <: U64.t);
  // y is on list i, so it has class i ...
  assert (size_class (U64.v (wosize_of_object y g)) == i);
  // ... which is not class j, so list j avoids it.
  assert (chain_class g (fls_head fls j) j)
#pop-options

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

let cells_kept_n (g g': heap) (fp: U64.t) (n: nat) : prop =
  forall (a: obj_addr).
    Seq.mem a (objects zero_addr g) /\
    AL.chain_avoids g fp (a <: U64.t) n = false ==>
    Seq.mem a (objects zero_addr g') /\
    read_word g' (hd_address a) == read_word g (hd_address a) /\
    read_word g' (a <: hp_addr) == read_word g (a <: hp_addr)

/// One step down the chain: the cells of the tail are cells of the chain.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let cells_kept_tail (g g': heap) (fp: U64.t) (n: nat)
  : Lemma (requires n > 0 /\ U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size /\
                    cells_kept_n g g' fp n)
          (ensures cells_kept_n g g' (read_word g (fp <: obj_addr)) (n - 1))
  = let next = read_word g (fp <: obj_addr) in
    let aux (a: obj_addr)
      : Lemma (requires Seq.mem a (objects zero_addr g) /\
                        AL.chain_avoids g next (a <: U64.t) (n - 1) = false)
              (ensures AL.chain_avoids g fp (a <: U64.t) n = false)
      = if (a <: U64.t) = fp then begin
          if AL.chain_avoids g fp (a <: U64.t) n then
            AL.chain_avoids_head_ne g fp (a <: U64.t) n
        end
        else AC.chain_avoids_unfold_step g fp (a <: U64.t) n
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// The avoidance of one address, compared at one node.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let avoids_step_eq (g g': heap) (fp: U64.t) (n: nat) (y: U64.t)
  : Lemma (requires n > 0 /\ U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    read_word g' (fp <: obj_addr) == read_word g (fp <: obj_addr) /\
                    (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
                       AL.chain_avoids g' (read_word g (fp <: obj_addr)) y (n - 1) ==
                       AL.chain_avoids g (read_word g (fp <: obj_addr)) y (n - 1)))
          (ensures AL.chain_avoids g' fp y n == AL.chain_avoids g fp y n)
  = if fp = y then begin
      if AL.chain_avoids g fp y n then AL.chain_avoids_head_ne g fp y n;
      if AL.chain_avoids g' fp y n then AL.chain_avoids_head_ne g' fp y n
    end
    else if U64.v (hd_address (fp <: obj_addr)) + 16 > heap_size then begin
      AC.chain_avoids_terminal g fp y n;
      AC.chain_avoids_terminal g' fp y n
    end
    else begin
      AC.chain_avoids_unfold_step g fp y n;
      AC.chain_avoids_unfold_step g' fp y n
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let rec chain_frame_aux (g g': heap) (fp: U64.t) (n: nat)
  : Lemma (requires AL.fl_valid g fp n /\ cells_kept_n g g' fp n)
          (ensures AL.fl_valid g' fp n /\
                   (AL.fl_chain_terminates g fp n ==> AL.fl_chain_terminates g' fp n) /\
                   (forall (y: U64.t). AL.chain_avoids g' fp y n == AL.chain_avoids g fp y n))
          (decreases n)
  = if n = 0 then begin
      AL.fl_valid_zero g' fp;
      (if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size ||
          U64.v fp % U64.v mword <> 0
       then AL.fl_chain_terminates_terminal g' fp n
       else AL.fl_chain_terminates_valid_zero g fp);
      introduce forall (y: U64.t). AL.chain_avoids g' fp y n == AL.chain_avoids g fp y n
      with (AC.chain_avoids_zero g fp y; AC.chain_avoids_zero g' fp y)
    end
    else if fp = 0UL || U64.v fp < U64.v mword || U64.v fp >= heap_size ||
            U64.v fp % U64.v mword <> 0 then begin
      AL.fl_valid_terminal g' fp n;
      AL.fl_chain_terminates_terminal g' fp n;
      introduce forall (y: U64.t). AL.chain_avoids g' fp y n == AL.chain_avoids g fp y n
      with (AC.chain_avoids_terminal g fp y n; AC.chain_avoids_terminal g' fp y n)
    end
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      AL.fl_valid_elim g fp n;
      // `fp` is itself a cell, so it is kept.
      (if AL.chain_avoids g fp fp n then AL.chain_avoids_head_ne g fp fp n);
      assert (Seq.mem obj (objects zero_addr g'));
      assert (read_word g' hd == read_word g hd);
      assert (read_word g' (obj <: hp_addr) == read_word g (obj <: hp_addr));
      wosize_of_object_spec obj g;
      wosize_of_object_spec obj g';
      if U64.v hd + 16 <= heap_size then begin
        let next = read_word g obj in
        cells_kept_tail g g' fp n;
        chain_frame_aux g g' next (n - 1);
        AL.fl_valid_step g' fp n;
        (if AL.fl_chain_terminates g fp n then begin
           AL.fl_chain_terminates_elim g fp n;
           AL.fl_chain_terminates_step g' fp n
         end);
        introduce forall (y: U64.t). AL.chain_avoids g' fp y n == AL.chain_avoids g fp y n
        with avoids_step_eq g g' fp n y
      end
      else begin
        AL.fl_valid_step g' fp n;
        AL.fl_chain_terminates_step g' fp n;
        introduce forall (y: U64.t). AL.chain_avoids g' fp y n == AL.chain_avoids g fp y n
        with avoids_step_eq g g' fp n y
      end
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let chain_frame g g' fp c =
  chain_frame_aux g g' fp heap_words;
  introduce chain_class g fp c ==> chain_class g' fp c
  with begin
    let aux (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\
                        size_class (U64.v (wosize_of_object y g')) <> c)
              (ensures AL.chain_avoids g' fp (y <: U64.t) heap_words = true)
      = if AL.chain_avoids g fp (y <: U64.t) heap_words then ()
        else begin
          // y is a cell, so it is kept, so its class is unchanged.
          chain_cell_in_objects g fp (y <: U64.t);
          wosize_of_object_spec y g;
          wosize_of_object_spec y g';
          assert (size_class (U64.v (wosize_of_object y g)) <> c)
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let fls_frame g g' fls =
  fls_valid_elim g fls;
  let per_list (i: nat{i < n_lists})
    : Lemma (AL.fl_valid g' (fls_head fls i) heap_words /\
             chain_class g' (fls_head fls i) i /\
             (AL.fl_chain_terminates g (fls_head fls i) heap_words ==>
                AL.fl_chain_terminates g' (fls_head fls i) heap_words) /\
             (forall (y: U64.t). AL.chain_avoids g' (fls_head fls i) y heap_words ==
                                 AL.chain_avoids g (fls_head fls i) y heap_words))
    = let kept (a: obj_addr)
        : Lemma (requires Seq.mem a (objects zero_addr g) /\
                          AL.chain_avoids g (fls_head fls i) (a <: U64.t) heap_words = false)
                (ensures ~(fls_avoids g fls (a <: U64.t)))
        = fls_avoids_iff g fls (a <: U64.t)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
      assert (chain_cells_kept g g' (fls_head fls i));
      chain_frame g g' (fls_head fls i) i
  in
  FStar.Classical.forall_intro per_list;
  fls_valid_intro g' fls;
  introduce fls_terminates g fls ==> fls_terminates g' fls
  with (fls_terminates_elim g fls; fls_terminates_intro g' fls);
  introduce forall (y: U64.t). fls_avoids g' fls y <==> fls_avoids g fls y
  with (fls_avoids_iff g fls y; fls_avoids_iff g' fls y)
#pop-options

/// Two distinct objects: the header and the first field of one lie outside
/// the extent of the other.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let outside_extent (g: heap) (a d: obj_addr)
  : Lemma (requires Seq.mem a (objects zero_addr g) /\ Seq.mem d (objects zero_addr g) /\
                    a <> d /\ U64.v (wosize_of_object a g) >= 1)
          (ensures (let lo = U64.v (hd_address d) in
                    let hi = U64.v d + U64.v (wosize_of_object d g) * U64.v mword in
                    (U64.v (hd_address a) + U64.v mword <= lo \/ U64.v (hd_address a) >= hi) /\
                    (U64.v a + U64.v mword <= lo \/ U64.v a >= hi)))
  = hd_address_spec a;
    hd_address_spec d;
    objects_separated zero_addr g a d;
    objects_separated zero_addr g d a
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let fls_frame_extent g g' fls d =
  let kept (a: obj_addr)
    : Lemma (requires Seq.mem a (objects zero_addr g) /\ ~(fls_avoids g fls (a <: U64.t)))
            (ensures Seq.mem a (objects zero_addr g') /\
                     read_word g' (hd_address a) == read_word g (hd_address a) /\
                     read_word g' (a <: hp_addr) == read_word g (a <: hp_addr))
    = // `a` is on some list, so it is a cell with a link word, and not `d`.
      fls_avoids_iff g fls (a <: U64.t);
      fls_valid_elim g fls;
      eliminate exists (i: nat). i < n_lists /\
        AL.chain_avoids g (fls_head fls i) (a <: U64.t) heap_words <> true
      with begin
        chain_cell_in_objects g (fls_head fls i) (a <: U64.t);
        fls_avoids_iff g fls (d <: U64.t);
        assert (AL.chain_avoids g (fls_head fls i) (d <: U64.t) heap_words = true);
        assert (a <> d);
        outside_extent g a d
      end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
  fls_frame g g' fls
#pop-options
