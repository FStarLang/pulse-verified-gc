module GC.Gen.AllocLists

/// The allocation from list `j` that `alloc_lists_spec` performs
/// (`alloc_lists_list`) is either the single-list allocation on that list
/// (`alloc_on_plain`), so every lemma is the single-list lemma, or a relist:
/// the block is allocated whole, split, and its remainder pushed on the list
/// of its class.  A relist writes the same words as the single-list allocation
/// except two links, the predecessor's and the remainder's, so its heap is
/// that allocation's with two link writes (`relist_heap`), and every heap fact
/// carries over.  The lists are handled per list: the lists other than `j` keep
/// their cells (`chain_frame`), list `j` is the single-list allocation's, and
/// the remainder is pushed (`fls_push`).

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FreeLists
open GC.Spec.Allocator.Lists
open GC.Lib.Header

module U64 = FStar.UInt64
module Seq = FStar.Seq
module Mark = GC.Spec.Mark
module SC = GC.Spec.SizeClass
module SA = GC.Spec.Allocator
module AL = GC.Spec.Allocator.Lemmas
module AP = GC.Gen.AllocProps
module Dense = GC.Spec.Allocator.Dense
module HE = GC.Gen.HeapExtensional
module Push = GC.Spec.FreeLists.Push

/// ---------------------------------------------------------------------------
/// Words of distinct objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let extents_apart g x y a b
  = hd_address_spec x; hd_address_spec y;
    if U64.v x < U64.v y then objects_separated zero_addr g x y
    else objects_separated zero_addr g y x
#pop-options

/// The header and the first field of an object of wosize >= 1.
let extent_header (g: heap) (x: obj_addr)
  : Lemma (in_extent g x (U64.v (hd_address x)) \/ U64.v (wosize_of_object x g) == 0)
  = hd_address_spec x

let extent_link (g: heap) (x: obj_addr)
  : Lemma (requires U64.v (wosize_of_object x g) >= 1)
          (ensures in_extent g x (U64.v x) /\ in_extent g x (U64.v (hd_address x)))
  = hd_address_spec x

/// ---------------------------------------------------------------------------
/// Headers
/// ---------------------------------------------------------------------------

/// What an unchanged header keeps.
let same_header (g g': heap) (x: obj_addr)
  : Lemma (requires read_word g' (hd_address x) == read_word g (hd_address x))
          (ensures wosize_of_object x g' == wosize_of_object x g /\
                   color_of_object x g' == color_of_object x g /\
                   is_blue x g' == is_blue x g /\ is_white x g' == is_white x g /\
                   is_black x g' == is_black x g /\
                   is_infix x g' == is_infix x g)
  = wosize_of_object_spec x g; wosize_of_object_spec x g';
    color_of_object_spec x g; color_of_object_spec x g';
    is_blue_iff x g; is_blue_iff x g'; is_white_iff x g; is_white_iff x g';
    is_black_iff x g; is_black_iff x g';
    is_infix_spec x g; is_infix_spec x g';
    tag_of_object_spec x g; tag_of_object_spec x g'

/// ---------------------------------------------------------------------------
/// One link write
/// ---------------------------------------------------------------------------

/// Writing the link word of an object of wosize >= 1 changes no object and no
/// header.
#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let link_write (g: heap) (x: obj_addr) (v: U64.t)
  : Lemma (requires well_formed_heap_part1 g /\ Seq.mem x (objects zero_addr g) /\
                    U64.v (wosize_of_object x g) >= 1)
          (ensures (let g' = write_word g (x <: hp_addr) v in
                    objects zero_addr g' == objects zero_addr g /\
                    well_formed_heap_part1 g' /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                       read_word g' (hd_address y) == read_word g (hd_address y)) /\
                    (forall (a: hp_addr). a <> (x <: hp_addr) ==> read_word g' a == read_word g a) /\
                    read_word g' (x <: hp_addr) == v /\
                    (heap_objects_dense g ==> heap_objects_dense g') /\
                    (well_formed_heap_part4 g ==> well_formed_heap_part4 g') /\
                    (Mark.no_black_objects g ==> Mark.no_black_objects g')))
  = let g' = write_word g (x <: hp_addr) v in
    hd_address_spec x;
    wosize_of_object_spec x g;
    AL.write_body_preserves_objects_local zero_addr g x (x <: hp_addr) v;
    AL.write_body_preserves_wfh_part1 g x (x <: hp_addr) v;
    read_write_same g (x <: hp_addr) v;
    let other (a: hp_addr) : Lemma (a <> (x <: hp_addr) ==> read_word g' a == read_word g a)
      = if a <> (x <: hp_addr) then begin
          aligned_apart a (x <: hp_addr);
          read_write_different g (x <: hp_addr) a v
        end
    in
    FStar.Classical.forall_intro other;
    let hdr (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g) ==>
               read_word g' (hd_address y) == read_word g (hd_address y) /\
               is_infix y g' == is_infix y g /\ is_black y g' == is_black y g)
      = if Seq.mem y (objects zero_addr g) then begin
          hd_address_spec y;
          extent_link g x;
          (if y = x then ()
           else begin
             extent_header g y;
             wosize_of_object_spec y g;
             extents_apart g x y (U64.v x) (U64.v (hd_address y))
           end);
          same_header g g' y
        end
    in
    FStar.Classical.forall_intro hdr;
    (if heap_objects_dense g then Dense.write_field_preserves_dense g x v);
    ()
#pop-options

/// ---------------------------------------------------------------------------
/// Writes confined to a block and a link
/// ---------------------------------------------------------------------------

/// `g'` differs from `g` only in the extent of `c` and, when `pw`, at `p`.
let confined (g g': heap) (c: obj_addr) (pw: bool) (p: U64.t) : prop =
  forall (a: hp_addr). read_word g' a <> read_word g a ==>
    in_extent g c (U64.v a) \/ (pw /\ U64.v a == U64.v p)

/// The predecessor, when it is written, is an object of wosize >= 1.
let pred_ok (g: heap) (pw: bool) (p: U64.t) : prop =
  pw ==> (U64.v p >= U64.v mword /\ U64.v p < heap_size /\ U64.v p % U64.v mword == 0 /\
          Seq.mem (p <: obj_addr) (objects zero_addr g) /\
          U64.v (wosize_of_object (p <: obj_addr) g) >= 1)

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
/// The header of every other object is kept.
let header_kept (g g': heap) (c: obj_addr) (pw: bool) (p: U64.t) (x: obj_addr)
  : Lemma (requires confined g g' c pw p /\ pred_ok g pw p /\
                    Seq.mem c (objects zero_addr g) /\
                    Seq.mem x (objects zero_addr g) /\ x <> c)
          (ensures read_word g' (hd_address x) == read_word g (hd_address x))
  = let h = hd_address x in
    hd_address_spec x;
    if read_word g' h <> read_word g h then begin
      extent_header g x;
      wosize_of_object_spec x g;
      (if in_extent g c (U64.v h) then extents_apart g x c (U64.v h) (U64.v h));
      if pw then begin
        let po : obj_addr = p in
        extent_link g po;
        if po = x then () else extents_apart g x po (U64.v h) (U64.v p)
      end
    end

/// Every word of an object other than `c` and `p` is kept.
let extent_kept (g g': heap) (c: obj_addr) (pw: bool) (p: U64.t) (x: obj_addr) (a: hp_addr)
  : Lemma (requires confined g g' c pw p /\ pred_ok g pw p /\
                    Seq.mem c (objects zero_addr g) /\
                    Seq.mem x (objects zero_addr g) /\ x <> c /\
                    (pw ==> (x <: U64.t) <> p) /\ in_extent g x (U64.v a))
          (ensures read_word g' a == read_word g a)
  = if read_word g' a <> read_word g a then begin
      (if in_extent g c (U64.v a) then extents_apart g x c (U64.v a) (U64.v a));
      if pw then begin
        let po : obj_addr = p in
        extent_link g po;
        extents_apart g x po (U64.v a) (U64.v p)
      end
    end
#pop-options

/// `found_heap` writes only `c`'s extent and the predecessor's link.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let found_confined (g: heap) (p: U64.t) (c: obj_addr) (wz: pos)
  : Lemma (requires (let bw = U64.v (getWosize (read_word g (hd_address c))) in
                     bw >= wz /\ U64.v (hd_address c) + (bw - wz) * 8 + 8 < heap_size))
          (ensures confined g (found_heap g p c wz) c (pv p c) p)
  = hd_address_spec c;
    wosize_of_object_spec c g;
    let aux (a: hp_addr)
      : Lemma (read_word (found_heap g p c wz) a <> read_word g a ==>
               in_extent g c (U64.v a) \/ (pv p c /\ U64.v a == U64.v p))
      = found_heap_read g p c wz a
    in
    FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// The lists other than the one allocated from
/// ---------------------------------------------------------------------------

/// A write confined to a cell `c` of list `j` and the link of a cell `p` of
/// list `j` keeps every other list.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let others_kept (g g': heap) (fls: fl_state) (j: nat) (c: obj_addr) (pw: bool) (p: U64.t)
  : Lemma (requires fls_valid g fls /\ j < SC.n_lists /\
                    confined g g' c pw p /\ pred_ok g pw p /\
                    AL.chain_avoids g (fls_head fls j) (c <: U64.t) heap_words = false /\
                    (pw ==> AL.chain_avoids g (fls_head fls j) p heap_words = false) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                                           Seq.mem x (objects zero_addr g')))
          (ensures forall (k: nat). k < SC.n_lists /\ k <> j ==>
                     chain_cells_kept g g' (fls_head fls k))
  = fls_valid_elim g fls;
    chain_cell_in_objects g (fls_head fls j) (c <: U64.t);
    let one (k: nat) (a: obj_addr)
      : Lemma (requires k < SC.n_lists /\ k <> j /\
                        Seq.mem a (objects zero_addr g) /\
                        AL.chain_avoids g (fls_head fls k) (a <: U64.t) heap_words = false)
              (ensures Seq.mem a (objects zero_addr g') /\
                       read_word g' (hd_address a) == read_word g (hd_address a) /\
                       read_word g' (a <: hp_addr) == read_word g (a <: hp_addr))
      = chain_cell_in_objects g (fls_head fls k) (a <: U64.t);
        fls_cell_one_list g fls k j a;
        extent_link g a;
        extent_kept g g' c pw p a (hd_address a);
        extent_kept g g' c pw p a (a <: hp_addr)
    in
    let one' (k: nat) (a: obj_addr)
      : Lemma (k < SC.n_lists /\ k <> j /\
               Seq.mem a (objects zero_addr g) /\
               AL.chain_avoids g (fls_head fls k) (a <: U64.t) heap_words = false ==>
               Seq.mem a (objects zero_addr g') /\
               read_word g' (hd_address a) == read_word g (hd_address a) /\
               read_word g' (a <: hp_addr) == read_word g (a <: hp_addr))
      = FStar.Classical.move_requires (one k) a
    in
    FStar.Classical.forall_intro_2 one'
#pop-options

/// ---------------------------------------------------------------------------
/// Where a successful allocation on one list stops
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let on_found (g: heap) (fp: U64.t) (wz: pos)
  : Lemma (requires well_formed_heap_part1 g /\ AL.fl_valid g fp heap_words /\
                    (SA.alloc_spec g fp wz).SA.obj_out <> 0UL)
          (ensures (let c = first_fit_block g fp wz heap_words in
                    let w = first_fit_size g fp wz heap_words in
                    let p = found_prev g 0UL fp wz heap_words in
                    U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword == 0 /\
                    (let obj : obj_addr = c in
                     Seq.mem obj (objects zero_addr g) /\
                     U64.v (getWosize (read_word g (hd_address obj))) == w /\
                     U64.v (wosize_of_object obj g) == w /\ w >= wz /\
                     U64.v (hd_address obj) + (w - wz) * 8 + 8 < heap_size /\
                     AL.chain_avoids g fp c heap_words = false /\
                     pred_ok g (pv p obj) p /\
                     (pv p obj ==> AL.chain_avoids g fp p heap_words = false) /\
                     (let r = SA.alloc_spec g fp wz in
                      U64.v r.SA.obj_out == U64.v c + (w - wz) * 8 /\
                      r.SA.heap_out == found_heap g p obj wz /\
                      r.SA.fp_out == found_fp g fp p obj wz) /\
                     (let r = SA.alloc_spec g fp w in
                      r.SA.obj_out == c /\
                      r.SA.heap_out == found_heap g p obj w /\
                      r.SA.fp_out == found_fp g fp p obj w))))
  = let w = first_fit_size g fp wz heap_words in
    first_fit_same_block g fp 0UL fp wz heap_words;
    search_at g fp 0UL fp wz wz heap_words;
    search_at g fp 0UL fp wz w heap_words;
    found_cells g fp 0UL fp wz heap_words;
    let c = first_fit_block g fp wz heap_words in
    let p = found_prev g 0UL fp wz heap_words in
    let obj : obj_addr = c in
    chain_cell_in_objects g fp c;
    wosize_of_object_spec obj g;
    assert (U64.v (SA.alloc_spec g fp w).SA.obj_out == U64.v c);
    if p = 0UL then () else chain_cell_in_objects g fp p
#pop-options

/// ---------------------------------------------------------------------------
/// The list allocated from keeps its class
/// ---------------------------------------------------------------------------

/// After allocating `wz'` words from block `c` of list `j`, the list is still
/// of class `j`, provided the remainder it keeps (wosize `w - wz' - 1`) is.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let list_class_after (g: heap) (fp: U64.t) (j: nat) (c: obj_addr) (p: U64.t)
                     (w: nat) (wz': pos)
  : Lemma (requires well_formed_heap_part1 g /\ AL.fl_valid g fp heap_words /\
                    AL.fl_chain_terminates g fp heap_words /\
                    chain_class g fp j /\
                    Seq.mem c (objects zero_addr g) /\
                    U64.v (getWosize (read_word g (hd_address c))) == w /\ w >= wz' /\
                    U64.v (hd_address c) + (w - wz') * 8 + 8 < heap_size /\
                    pred_ok g (pv p c) p /\
                    (let r = SA.alloc_spec g fp wz' in
                     r.SA.obj_out <> 0UL /\
                     U64.v r.SA.obj_out == U64.v c + (w - wz') * 8 /\
                     r.SA.heap_out == found_heap g p c wz') /\
                    (w - wz' >= 2 ==> SC.size_class (w - wz' - 1) == j))
          (ensures (let r = SA.alloc_spec g fp wz' in
                    chain_class r.SA.heap_out r.SA.fp_out j))
  = let r = SA.alloc_spec g fp wz' in
    let gA = r.SA.heap_out in
    let lo = w - wz' in
    AL.alloc_spec_only_new_is_obj_out_part1 g fp wz';
    AL.alloc_spec_obj_not_in_chain_part1 g fp wz';
    AL.alloc_spec_preserves_fl_valid_part1 g fp wz';
    found_confined g p c wz';
    hd_address_spec c;
    let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr gA) /\
                        SC.size_class (U64.v (wosize_of_object x gA)) <> j)
              (ensures AL.chain_avoids gA r.SA.fp_out (x <: U64.t) heap_words = true)
      = if (x <: U64.t) = r.SA.obj_out then ()
        else if x = c then begin
          found_heap_read g p c wz' (hd_address c);
          wosize_of_object_spec c gA;
          AL.make_header_getWosize (U64.uint_to_t (lo - 1)) SA.blue_bits 0UL;
          if AL.chain_avoids gA r.SA.fp_out (x <: U64.t) heap_words then ()
          else chain_cell_in_objects gA r.SA.fp_out (x <: U64.t)
        end
        else begin
          header_kept g gA c (pv p c) p x;
          same_header g gA x;
          if AL.chain_avoids g fp (x <: U64.t) heap_words then
            AL.alloc_spec_preserves_chain_avoids_other g fp wz' (x <: U64.t)
          else ()
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// ---------------------------------------------------------------------------
/// Inside a block
/// ---------------------------------------------------------------------------

/// An address strictly inside the body of `c` is not an object of `g`.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let inside_not_object (g: heap) (c: obj_addr) (o: obj_addr)
  : Lemma (requires Seq.mem c (objects zero_addr g) /\
                    U64.v c < U64.v o /\ U64.v o < U64.v c + U64.v (wosize_of_object c g) * 8)
          (ensures ~(Seq.mem o (objects zero_addr g)))
  = if Seq.mem o (objects zero_addr g) then objects_separated zero_addr g c o
#pop-options

/// A chain of `g` visits only objects of `g`.
let not_object_avoided (g: heap) (fp: U64.t) (o: U64.t)
  : Lemma (requires AL.fl_valid g fp heap_words /\
                    U64.v o >= U64.v mword /\ U64.v o < heap_size /\ U64.v o % U64.v mword == 0 /\
                    ~(Seq.mem (o <: obj_addr) (objects zero_addr g)))
          (ensures AL.chain_avoids g fp o heap_words = true)
  = if AL.chain_avoids g fp o heap_words then () else chain_cell_in_objects g fp o

/// ---------------------------------------------------------------------------
/// The lists after a plain allocation
/// ---------------------------------------------------------------------------

/// What the kit needs of the lists after an allocation from list `j`.
let lists_post (g: heap) (fls: fl_state) (r: alloc_lists_result) : prop =
  fls_valid r.heap_out r.fls_out /\ fls_terminates r.heap_out r.fls_out /\
  fls_avoids r.heap_out r.fls_out r.obj_out /\
  (forall (excl: U64.t).
     fls_avoids g fls excl /\
     U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\ U64.v excl % U64.v mword == 0 /\
     Seq.mem (excl <: obj_addr) (objects zero_addr g) ==>
     fls_avoids r.heap_out r.fls_out excl)

/// The shape of the lists after an allocation from list `j`: list `j` is the
/// single-list allocation's at `wz`, or on a relist at the block's size `w`;
/// every other list keeps its cells; a relisted block is on a list.
let struct_post (g: heap) (fls: fl_state) (j: nat) (wz: pos) : prop =
  let fp = fls_head fls j in
  let w = first_fit_size g fp wz heap_words in
  let rl = relists j w wz in
  let rS = SA.alloc_spec g fp (if rl then w else wz) in
  let r = alloc_on g fls j wz in
  rS.SA.obj_out <> 0UL /\
  fls_head r.fls_out j == rS.SA.fp_out /\
  (forall (y: U64.t). AL.chain_avoids r.heap_out rS.SA.fp_out y heap_words ==
                      AL.chain_avoids rS.SA.heap_out rS.SA.fp_out y heap_words) /\
  (forall (k: nat) (y: U64.t).
     k < SC.n_lists /\ k <> j /\ AL.chain_avoids g (fls_head fls k) y heap_words = false ==>
     AL.chain_avoids r.heap_out (fls_head r.fls_out k) y heap_words = false) /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ (y <: U64.t) <> rS.SA.obj_out ==>
     read_word r.heap_out (hd_address y) == read_word rS.SA.heap_out (hd_address y)) /\
  (rl ==> ~(fls_avoids r.heap_out r.fls_out rS.SA.obj_out)) /\
  (not rl ==> r.heap_out == rS.SA.heap_out) /\
  (forall (k: nat). k < SC.n_lists /\ k <> j ==>
     fls_head r.fls_out k == fls_head fls k \/ (rl /\ fls_head r.fls_out k == rS.SA.obj_out)) /\
  (rl ==> U64.v rS.SA.obj_out >= U64.v mword /\ U64.v rS.SA.obj_out < heap_size /\
          U64.v rS.SA.obj_out % U64.v mword == 0 /\
          Seq.mem (rS.SA.obj_out <: obj_addr) (objects zero_addr g) /\
          (forall (a: hp_addr). read_word r.heap_out a <> read_word rS.SA.heap_out a ==>
             in_extent g (rS.SA.obj_out <: obj_addr) (U64.v a)) /\
          read_word r.heap_out (rS.SA.obj_out <: hp_addr) ==
            fls_head fls (SC.size_class (w - wz - 1)))

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let plain_lists (g: heap) (fls: fl_state) (j: nat) (wz: pos)
  : Lemma (requires well_formed_heap_part1 g /\ fls_valid g fls /\ fls_terminates g fls /\
                    j < SC.n_lists /\
                    (let fp = fls_head fls j in
                     (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                     not (relists j (first_fit_size g fp wz heap_words) wz)))
          (ensures lists_post g fls (alloc_on g fls j wz) /\ struct_post g fls j wz)
  = let fp = fls_head fls j in
    fls_valid_elim g fls;
    fls_terminates_elim g fls;
    on_found g fp wz;
    alloc_on_plain g fls j wz;
    let w = first_fit_size g fp wz heap_words in
    let c : obj_addr = first_fit_block g fp wz heap_words in
    let p = found_prev g 0UL fp wz heap_words in
    let pw = pv p c in
    let rA = SA.alloc_spec g fp wz in
    let gA = rA.SA.heap_out in
    let fls' = fls_set fls j rA.SA.fp_out in
    let obj = rA.SA.obj_out in
    AP.alloc_spec_obj_valid g fp wz;
    hd_address_spec c;
    AL.alloc_spec_preserves_fl_valid_part1 g fp wz;
    AL.alloc_spec_preserves_fl_chain_terminates_part1 g fp wz;
    AL.alloc_spec_preserves_objects_part1 g fp wz;
    AL.alloc_spec_obj_not_in_chain_part1 g fp wz;
    found_confined g p c wz;
    others_kept g gA fls j c pw p;
    list_class_after g fp j c p w wz;
    // the allocated object was not visited by any other list
    let obj_before (k: nat)
      : Lemma (requires k < SC.n_lists /\ k <> j)
              (ensures AL.chain_avoids g (fls_head fls k) obj heap_words = true)
      = if w - wz = 0 then fls_cell_one_list g fls j k c
        else begin
          wosize_of_object_spec c g;
          inside_not_object g c (obj <: obj_addr);
          not_object_avoided g (fls_head fls k) obj
        end
    in
    let per (k: nat)
      : Lemma (requires k < SC.n_lists)
              (ensures AL.fl_valid gA (fls_head fls' k) heap_words /\
                       chain_class gA (fls_head fls' k) k /\
                       AL.fl_chain_terminates gA (fls_head fls' k) heap_words /\
                       AL.chain_avoids gA (fls_head fls' k) obj heap_words = true /\
                       (forall (excl: U64.t).
                          AL.chain_avoids g (fls_head fls k) excl heap_words = true /\
                          U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                          U64.v excl % U64.v mword == 0 /\
                          Seq.mem (excl <: obj_addr) (objects zero_addr g) ==>
                          AL.chain_avoids gA (fls_head fls' k) excl heap_words = true))
      = fls_head_set fls j k rA.SA.fp_out;
        if k = j then begin
          let aux (excl: U64.t)
            : Lemma (AL.chain_avoids g fp excl heap_words = true /\
                     U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                     U64.v excl % U64.v mword == 0 /\
                     Seq.mem (excl <: obj_addr) (objects zero_addr g) ==>
                     AL.chain_avoids gA rA.SA.fp_out excl heap_words = true)
            = FStar.Classical.move_requires (AL.alloc_spec_preserves_chain_avoids_other g fp wz) excl
          in
          FStar.Classical.forall_intro aux
        end
        else begin
          chain_frame g gA (fls_head fls k) k;
          obj_before k
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires per);
    fls_valid_intro gA fls';
    fls_terminates_intro gA fls';
    fls_avoids_iff gA fls' obj;
    let ex (excl: U64.t)
      : Lemma (fls_avoids g fls excl /\
               U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
               U64.v excl % U64.v mword == 0 /\
               Seq.mem (excl <: obj_addr) (objects zero_addr g) ==>
               fls_avoids gA fls' excl)
      = fls_avoids_iff g fls excl; fls_avoids_iff gA fls' excl
    in
    FStar.Classical.forall_intro ex;
    fls_head_set fls j j rA.SA.fp_out;
    let others (k: nat) (y: U64.t)
      : Lemma (k < SC.n_lists /\ k <> j /\ AL.chain_avoids g (fls_head fls k) y heap_words = false ==>
               AL.chain_avoids gA (fls_head fls' k) y heap_words = false)
      = if k < SC.n_lists && k <> j then begin
          fls_head_set fls j k rA.SA.fp_out;
          chain_frame g gA (fls_head fls k) k
        end
    in
    FStar.Classical.forall_intro_2 others;
    let heads (k: nat) : Lemma (fls_head fls' k == fls_head fls k \/ k == j)
      = fls_head_set fls j k rA.SA.fp_out
    in
    FStar.Classical.forall_intro heads
#pop-options

/// ---------------------------------------------------------------------------
/// The relist heap
/// ---------------------------------------------------------------------------

/// The single-list allocation's heap with the predecessor unlinking the block.
let relist_mid (g: heap) (fp: U64.t) (wz: pos) : GTot heap =
  let gA = (SA.alloc_spec g fp wz).SA.heap_out in
  let c = first_fit_block g fp wz heap_words in
  let p = found_prev g 0UL fp wz heap_words in
  if U64.v c >= U64.v mword && U64.v c < heap_size && U64.v c % U64.v mword = 0 &&
     pv p (c <: obj_addr)
  then write_word gA (p <: hp_addr) (SA.spec_next_fp g (c <: obj_addr))
  else gA

/// A relist is the single-list allocation, then the predecessor's link moves
/// past the block, then the remainder's link is pushed.
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let relist_heap (g: heap) (fls: fl_state) (j: nat) (wz: pos)
  : Lemma (requires well_formed_heap_part1 g /\ fls_valid g fls /\ j < SC.n_lists /\
                    (let fp = fls_head fls j in
                     (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                     relists j (first_fit_size g fp wz heap_words) wz))
          (ensures (let fp = fls_head fls j in
                    let w = first_fit_size g fp wz heap_words in
                    let c = first_fit_block g fp wz heap_words in
                    U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword == 0 /\
                    (alloc_on g fls j wz).heap_out ==
                    write_word (relist_mid g fp wz) (c <: hp_addr)
                               (fls_head fls (SC.size_class (w - wz - 1)))))
  = let fp = fls_head fls j in
    fls_valid_elim g fls;
    on_found g fp wz;
    let w = first_fit_size g fp wz heap_words in
    let c : obj_addr = first_fit_block g fp wz heap_words in
    let p = found_prev g 0UL fp wz heap_words in
    let pw = pv p c in
    let next = SA.spec_next_fp g c in
    let rA = SA.alloc_spec g fp wz in
    let gA = rA.SA.heap_out in
    let mid = relist_mid g fp wz in
    let hrc = fls_head fls (SC.size_class (w - wz - 1)) in
    let g3 = (alloc_on g fls j wz).heap_out in
    let rhs = write_word mid (c <: hp_addr) hrc in
    hd_address_spec c;
    wosize_of_object_spec c g;
    SA.alloc_replacement_fp_eq g c wz next;
    // the predecessor is a cell other than the block, so its link is not
    // the object header
    (if pw then begin
       let po : obj_addr = p in
       if po = c then ()
       else begin
         extent_link g po;
         extents_apart g c po (U64.v (hd_address c) + (w - wz) * 8) (U64.v p)
       end
     end);
    let aux (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word g3 (U64.uint_to_t a) == read_word rhs (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          let ad : hp_addr = U64.uint_to_t a in
          relist_read g fls j wz ad;
          if ad = (c <: hp_addr) then read_write_same mid (c <: hp_addr) hrc
          else begin
            aligned_apart (c <: hp_addr) ad;
            read_write_different mid (c <: hp_addr) ad hrc;
            found_heap_read g p c wz ad;
            if pw then begin
              let pa : hp_addr = p in
              if ad = pa then read_write_same gA pa next
              else (aligned_apart pa ad; read_write_different gA pa ad next)
            end
          end
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext g3 rhs
#pop-options

/// The heap facts of a relist are those of the single-list allocation: the
/// two link writes change no object and no header.
#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
let relist_heap_facts (g: heap) (fls: fl_state) (j: nat) (wz: pos)
  : Lemma (requires well_formed_heap_part1 g /\ fls_valid g fls /\ fls_terminates g fls /\
                    j < SC.n_lists /\
                    (let fp = fls_head fls j in
                     (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                     relists j (first_fit_size g fp wz heap_words) wz))
          (ensures (let fp = fls_head fls j in
                    let gA = (SA.alloc_spec g fp wz).SA.heap_out in
                    let mid = relist_mid g fp wz in
                    let g3 = (alloc_on g fls j wz).heap_out in
                    let c = first_fit_block g fp wz heap_words in
                    let w = first_fit_size g fp wz heap_words in
                    U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword == 0 /\
                    objects zero_addr mid == objects zero_addr gA /\
                    objects zero_addr g3 == objects zero_addr gA /\
                    well_formed_heap_part1 mid /\ well_formed_heap_part1 g3 /\
                    Seq.mem (c <: obj_addr) (objects zero_addr gA) /\
                    U64.v (wosize_of_object (c <: obj_addr) mid) == w - wz - 1 /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr gA) ==>
                       read_word mid (hd_address y) == read_word gA (hd_address y) /\
                       read_word g3 (hd_address y) == read_word gA (hd_address y)) /\
                    (heap_objects_dense gA ==> heap_objects_dense g3) /\
                    (well_formed_heap_part4 gA ==> well_formed_heap_part4 g3) /\
                    (Mark.no_black_objects gA ==> Mark.no_black_objects g3)))
  = let fp = fls_head fls j in
    fls_valid_elim g fls;
    fls_terminates_elim g fls;
    on_found g fp wz;
    relist_heap g fls j wz;
    let w = first_fit_size g fp wz heap_words in
    let c : obj_addr = first_fit_block g fp wz heap_words in
    let p = found_prev g 0UL fp wz heap_words in
    let pw = pv p c in
    let next = SA.spec_next_fp g c in
    let gA = (SA.alloc_spec g fp wz).SA.heap_out in
    let mid = relist_mid g fp wz in
    let hrc = fls_head fls (SC.size_class (w - wz - 1)) in
    AL.alloc_spec_preserves_wfh_part1 g fp wz;
    AL.alloc_spec_preserves_objects_part1 g fp wz;
    found_confined g p c wz;
    hd_address_spec c;
    // the remainder header, in gA
    found_heap_read g p c wz (hd_address c);
    wosize_of_object_spec c gA;
    AL.make_header_getWosize (U64.uint_to_t (w - wz - 1)) SA.blue_bits 0UL;
    assert (U64.v (wosize_of_object c gA) == w - wz - 1);
    if pw then begin
      let po : obj_addr = p in
      (if po = c then ()
       else begin
         header_kept g gA c pw p po;
         same_header g gA po
       end);
      link_write gA po next;
      same_header gA mid c
    end;
    link_write mid c hrc
#pop-options

/// ---------------------------------------------------------------------------
/// The lists after a relist
/// ---------------------------------------------------------------------------

/// `mid` is the whole-block allocation with the block split: it differs from
/// that allocation only in the block.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let mid_vs_whole (g: heap) (fp: U64.t) (wz: pos)
  : Lemma (requires well_formed_heap_part1 g /\ AL.fl_valid g fp heap_words /\
                    (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                    first_fit_size g fp wz heap_words >= wz + 2)
          (ensures (let w = first_fit_size g fp wz heap_words in
                    let c = first_fit_block g fp wz heap_words in
                    let p = found_prev g 0UL fp wz heap_words in
                    U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword == 0 /\
                    (let g1 = (SA.alloc_spec g fp w).SA.heap_out in
                     let mid = relist_mid g fp wz in
                     U64.v (wosize_of_object (c <: obj_addr) g1) == w /\
                     confined g1 mid (c <: obj_addr) false p /\
                     confined g mid (c <: obj_addr) (pv p (c <: obj_addr)) p)))
  = on_found g fp wz;
    let w = first_fit_size g fp wz heap_words in
    let c : obj_addr = first_fit_block g fp wz heap_words in
    let p = found_prev g 0UL fp wz heap_words in
    let pw = pv p c in
    let next = SA.spec_next_fp g c in
    let gA = (SA.alloc_spec g fp wz).SA.heap_out in
    let g1 = (SA.alloc_spec g fp w).SA.heap_out in
    let mid = relist_mid g fp wz in
    hd_address_spec c;
    wosize_of_object_spec c g;
    found_heap_read g p c w (hd_address c);
    wosize_of_object_spec c g1;
    AL.make_header_getWosize (U64.uint_to_t w) SA.white_bits 0UL;
    SA.alloc_replacement_fp_eq g c wz next;
    SA.alloc_replacement_fp_eq g c w next;
    let aux (a: hp_addr)
      : Lemma ((read_word mid a <> read_word g1 a ==> in_extent g1 c (U64.v a)) /\
               (read_word mid a <> read_word g a ==> in_extent g c (U64.v a) \/
                                                     (pw /\ U64.v a == U64.v p)))
      = found_heap_read g p c wz a;
        found_heap_read g p c w a;
        if pw then begin
          let pa : hp_addr = p in
          if a = pa then read_write_same gA pa next
          else (aligned_apart pa a; read_write_different gA pa a next)
        end
    in
    FStar.Classical.forall_intro aux
#pop-options

#push-options "--z3rlimit 120 --fuel 0 --ifuel 0"
let relist_lists (g: heap) (fls: fl_state) (j: nat) (wz: pos)
  : Lemma (requires well_formed_heap_part1 g /\ fls_valid g fls /\ fls_terminates g fls /\
                    j < SC.n_lists /\
                    (let fp = fls_head fls j in
                     (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                     relists j (first_fit_size g fp wz heap_words) wz))
          (ensures lists_post g fls (alloc_on g fls j wz) /\ struct_post g fls j wz)
  = let fp = fls_head fls j in
    fls_valid_elim g fls;
    fls_terminates_elim g fls;
    on_found g fp wz;
    relist_heap g fls j wz;
    relist_heap_facts g fls j wz;
    mid_vs_whole g fp wz;
    let w = first_fit_size g fp wz heap_words in
    let c : obj_addr = first_fit_block g fp wz heap_words in
    let p = found_prev g 0UL fp wz heap_words in
    let pw = pv p c in
    let next = SA.spec_next_fp g c in
    let rc = SC.size_class (w - wz - 1) in
    relist_read g fls j wz (c <: hp_addr);
    let r = alloc_on g fls j wz in
    let obj = r.obj_out in
    let r1 = SA.alloc_spec g fp w in
    let g1 = r1.SA.heap_out in
    let hj = r1.SA.fp_out in
    SA.alloc_replacement_fp_eq g c w next;
    assert (hj == (if pw then fp else next));
    let mid = relist_mid g fp wz in
    let fls1 = fls_set fls j hj in
    hd_address_spec c;
    wosize_of_object_spec c g;
    // the whole-block allocation, on list j
    AL.alloc_spec_preserves_fl_valid_part1 g fp w;
    AL.alloc_spec_preserves_fl_chain_terminates_part1 g fp w;
    AL.alloc_spec_obj_not_in_chain_part1 g fp w;
    AL.alloc_spec_preserves_objects_part1 g fp w;
    AL.alloc_spec_only_new_is_obj_out_part1 g fp w;
    AL.alloc_spec_preserves_objects_part1 g fp wz;
    list_class_after g fp j c p w w;
    // ... carried to mid
    let kept1 (a: obj_addr)
      : Lemma (requires Seq.mem a (objects zero_addr g1) /\
                        AL.chain_avoids g1 hj (a <: U64.t) heap_words = false)
              (ensures Seq.mem a (objects zero_addr mid) /\
                       read_word mid (hd_address a) == read_word g1 (hd_address a) /\
                       read_word mid (a <: hp_addr) == read_word g1 (a <: hp_addr))
      = chain_cell_in_objects g1 hj (a <: U64.t);
        extent_link g1 a;
        extent_kept g1 mid c false p a (hd_address a);
        extent_kept g1 mid c false p a (a <: hp_addr)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kept1);
    assert (chain_cells_kept g1 mid hj);
    chain_frame g1 mid hj j;
    // the other lists
    others_kept g mid fls j c pw p;
    let obj_not_obj (_: unit)
      : Lemma (~(Seq.mem (obj <: obj_addr) (objects zero_addr g)) /\
               ~(Seq.mem (obj <: obj_addr) (objects zero_addr g1)))
      = inside_not_object g c (obj <: obj_addr)
    in
    obj_not_obj ();
    let per (k: nat)
      : Lemma (requires k < SC.n_lists)
              (ensures AL.fl_valid mid (fls_head fls1 k) heap_words /\
                       chain_class mid (fls_head fls1 k) k /\
                       AL.fl_chain_terminates mid (fls_head fls1 k) heap_words /\
                       AL.chain_avoids mid (fls_head fls1 k) (c <: U64.t) heap_words = true /\
                       AL.chain_avoids mid (fls_head fls1 k) obj heap_words = true /\
                       (forall (excl: U64.t).
                          AL.chain_avoids g (fls_head fls k) excl heap_words = true /\
                          U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                          U64.v excl % U64.v mword == 0 /\
                          Seq.mem (excl <: obj_addr) (objects zero_addr g) ==>
                          AL.chain_avoids mid (fls_head fls1 k) excl heap_words = true))
      = fls_head_set fls j k hj;
        if k = j then begin
          not_object_avoided g1 hj obj;
          let aux (excl: U64.t)
            : Lemma (AL.chain_avoids g fp excl heap_words = true /\
                     U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                     U64.v excl % U64.v mword == 0 /\
                     Seq.mem (excl <: obj_addr) (objects zero_addr g) ==>
                     AL.chain_avoids g1 hj excl heap_words = true)
            = FStar.Classical.move_requires (AL.alloc_spec_preserves_chain_avoids_other g fp w) excl
          in
          FStar.Classical.forall_intro aux
        end
        else begin
          chain_frame g mid (fls_head fls k) k;
          fls_cell_one_list g fls j k c;
          not_object_avoided g (fls_head fls k) obj
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires per);
    fls_valid_intro mid fls1;
    fls_terminates_intro mid fls1;
    fls_avoids_iff mid fls1 (c <: U64.t);
    // push the remainder
    Push.fls_push mid fls1 c;
    fls_head_set fls j rc hj;
    assert (r.heap_out == write_word mid (c <: hp_addr) (fls_head fls1 rc));
    assert (r.fls_out == fls_set fls1 rc (c <: U64.t));
    assert (obj <> (c <: U64.t));
    fls_avoids_iff r.heap_out r.fls_out obj;
    let ex (excl: U64.t)
      : Lemma (fls_avoids g fls excl /\
               U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
               U64.v excl % U64.v mword == 0 /\
               Seq.mem (excl <: obj_addr) (objects zero_addr g) ==>
               fls_avoids r.heap_out r.fls_out excl)
      = fls_avoids_iff g fls excl;
        fls_avoids_iff r.heap_out r.fls_out excl;
        if fls_avoids g fls excl && U64.v excl >= U64.v mword && U64.v excl < heap_size &&
           U64.v excl % U64.v mword = 0 then
          (if excl = (c <: U64.t) then () else ())
    in
    FStar.Classical.forall_intro ex;
    // the shape: list j is the whole-block allocation's ...
    fls_head_set fls1 rc j (c <: U64.t);
    fls_head_set fls j j hj;
    let same_j (y: U64.t)
      : Lemma (AL.chain_avoids r.heap_out hj y heap_words ==
               AL.chain_avoids g1 hj y heap_words)
      = ()
    in
    FStar.Classical.forall_intro same_j;
    // ... the other lists keep their cells ...
    let others (k: nat) (y: U64.t)
      : Lemma (k < SC.n_lists /\ k <> j /\ AL.chain_avoids g (fls_head fls k) y heap_words = false ==>
               AL.chain_avoids r.heap_out (fls_head r.fls_out k) y heap_words = false)
      = if k < SC.n_lists && k <> j then begin
          fls_head_set fls j k hj;
          chain_frame g mid (fls_head fls k) k
        end
    in
    FStar.Classical.forall_intro_2 others;
    // ... headers are the whole-block allocation's but the block's ...
    let g1_g3 (a: hp_addr)
      : Lemma (read_word r.heap_out a <> read_word g1 a ==> in_extent g1 c (U64.v a))
      = relist_read g fls j wz a;
        found_heap_read g p c w a
    in
    FStar.Classical.forall_intro g1_g3;
    assert (confined g1 r.heap_out c false p);
    let hdr (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g) /\ (y <: U64.t) <> (c <: U64.t) ==>
               read_word r.heap_out (hd_address y) == read_word g1 (hd_address y))
      = if Seq.mem y (objects zero_addr g) && (y <: U64.t) <> (c <: U64.t) then
          header_kept g1 r.heap_out c false p y
    in
    FStar.Classical.forall_intro hdr;
    // ... and the block is on the list of its class
    fls_avoids_iff r.heap_out r.fls_out (c <: U64.t);
    let heads (k: nat)
      : Lemma (k <> j ==> fls_head r.fls_out k == fls_head fls k \/ fls_head r.fls_out k == (c <: U64.t))
      = fls_head_set fls1 rc k (c <: U64.t);
        fls_head_set fls j k hj
    in
    FStar.Classical.forall_intro heads;
    wosize_of_object_spec c g1;
    assert (forall (a: hp_addr). read_word r.heap_out a <> read_word g1 a ==>
              in_extent g c (U64.v a))
#pop-options

/// A relist writes only the block and the predecessor's link.
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let relist_confined (g: heap) (fls: fl_state) (j: nat) (wz: pos)
  : Lemma (requires well_formed_heap_part1 g /\ fls_valid g fls /\ j < SC.n_lists /\
                    (let fp = fls_head fls j in
                     (SA.alloc_spec g fp wz).SA.obj_out <> 0UL /\
                     relists j (first_fit_size g fp wz heap_words) wz))
          (ensures (let fp = fls_head fls j in
                    let c = first_fit_block g fp wz heap_words in
                    let p = found_prev g 0UL fp wz heap_words in
                    U64.v c >= U64.v mword /\ U64.v c < heap_size /\ U64.v c % U64.v mword == 0 /\
                    confined g (alloc_on g fls j wz).heap_out (c <: obj_addr)
                             (pv p (c <: obj_addr)) p))
  = let fp = fls_head fls j in
    fls_valid_elim g fls;
    on_found g fp wz;
    let c : obj_addr = first_fit_block g fp wz heap_words in
    hd_address_spec c;
    wosize_of_object_spec c g;
    let aux (a: hp_addr)
      : Lemma (read_word (alloc_on g fls j wz).heap_out a <> read_word g a ==>
               in_extent g c (U64.v a) \/
               (pv (found_prev g 0UL fp wz heap_words) c /\
                U64.v a == U64.v (found_prev g 0UL fp wz heap_words)))
      = relist_read g fls j wz a
    in
    FStar.Classical.forall_intro aux
#pop-options

/// ---------------------------------------------------------------------------
/// The allocation, list by list
/// ---------------------------------------------------------------------------

/// A successful allocation is an allocation on list `alloc_lists_list`; its
/// object is the single-list allocation's, and without a relist so is all of
/// it.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let on (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires (alloc_lists_spec g fls requested_wz).obj_out <> 0UL)
          (ensures (let j = alloc_lists_list g fls requested_wz in
                    let wz = req_wz requested_wz in
                    let fp = fls_head fls j in
                    let r = alloc_lists_spec g fls requested_wz in
                    let rA = SA.alloc_spec g fp wz in
                    j < SC.n_lists /\ rA.SA.obj_out <> 0UL /\
                    r == alloc_on g fls j wz /\
                    r.obj_out == rA.SA.obj_out /\
                    SA.alloc_spec g fp requested_wz == rA /\
                    (not (relists j (first_fit_size g fp wz heap_words) wz) ==>
                       r.heap_out == rA.SA.heap_out /\
                       r.fls_out == fls_set fls j rA.SA.fp_out)))
  = alloc_lists_list_spec g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let wz = req_wz requested_wz in
    let fp = fls_head fls j in
    if (SA.alloc_spec g fp wz).SA.obj_out = 0UL then ()
    else if relists j (first_fit_size g fp wz heap_words) wz then ()
    else alloc_on_plain g fls j wz
#pop-options

/// The single list's entry conditions, from the state's.
let unpack (g: heap) (fls: fl_state) (j: nat)
  : Lemma (requires fls_valid g fls /\ j < SC.n_lists)
          (ensures AL.fl_valid g (fls_head fls j) heap_words /\
                   chain_class g (fls_head fls j) j /\
                   (fls_terminates g fls ==>
                      AL.fl_chain_terminates g (fls_head fls j) heap_words) /\
                   (forall (x: U64.t). fls_avoids g fls x ==>
                      AL.chain_avoids g (fls_head fls j) x heap_words = true))
  = fls_valid_elim g fls;
    if fls_terminates g fls then fls_terminates_elim g fls;
    let av (x: U64.t)
      : Lemma (fls_avoids g fls x ==> AL.chain_avoids g (fls_head fls j) x heap_words = true)
      = fls_avoids_iff g fls x
    in
    FStar.Classical.forall_intro av

/// The relist's heap facts, at the relist's heap.
let relist_view (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires well_formed_heap_part1 g /\ fls_valid g fls /\ fls_terminates g fls /\
                    (alloc_lists_spec g fls requested_wz).obj_out <> 0UL)
          (ensures (let j = alloc_lists_list g fls requested_wz in
                    let wz = req_wz requested_wz in
                    let fp = fls_head fls j in
                    let r = alloc_lists_spec g fls requested_wz in
                    let gA = (SA.alloc_spec g fp wz).SA.heap_out in
                    objects zero_addr r.heap_out == objects zero_addr gA /\
                    well_formed_heap_part1 r.heap_out /\
                    (forall (y: obj_addr). Seq.mem y (objects zero_addr gA) ==>
                       read_word r.heap_out (hd_address y) == read_word gA (hd_address y)) /\
                    (heap_objects_dense gA ==> heap_objects_dense r.heap_out) /\
                    (well_formed_heap_part4 gA ==> well_formed_heap_part4 r.heap_out) /\
                    (Mark.no_black_objects gA ==> Mark.no_black_objects r.heap_out)))
  = on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let wz = req_wz requested_wz in
    let fp = fls_head fls j in
    unpack g fls j;
    AL.alloc_spec_preserves_wfh_part1 g fp wz;
    if relists j (first_fit_size g fp wz heap_words) wz then
      relist_heap_facts g fls j wz
    else ()

/// Header facts carried by an equal header, for every object.
let same_headers (g g': heap)
  : Lemma (requires forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                      read_word g' (hd_address y) == read_word g (hd_address y))
          (ensures forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==>
                     wosize_of_object y g' == wosize_of_object y g /\
                     color_of_object y g' == color_of_object y g /\
                     is_blue y g' == is_blue y g /\ is_white y g' == is_white y g)
  = let aux (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g) ==>
               wosize_of_object y g' == wosize_of_object y g /\
               color_of_object y g' == color_of_object y g /\
               is_blue y g' == is_blue y g /\ is_white y g' == is_white y g)
      = if Seq.mem y (objects zero_addr g) then same_header g g' y
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// The object walk and well-formedness
/// ---------------------------------------------------------------------------

let alloc_lists_preserves_objects_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then
    alloc_lists_list_spec g fls requested_wz
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    unpack g fls j;
    AL.alloc_spec_preserves_objects_part1 g (fls_head fls j) (req_wz requested_wz);
    relist_view g fls requested_wz
  end

let alloc_lists_preserves_wfh_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then
    alloc_lists_list_spec g fls requested_wz
  else relist_view g fls requested_wz

let alloc_lists_preserves_wfh_part4 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then
    alloc_lists_list_spec g fls requested_wz
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    unpack g fls j;
    AL.alloc_spec_preserves_wfh_part4 g (fls_head fls j) (req_wz requested_wz);
    relist_view g fls requested_wz
  end

let alloc_lists_preserves_no_black_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then
    alloc_lists_list_spec g fls requested_wz
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    unpack g fls j;
    AL.alloc_spec_preserves_no_black_part1 g (fls_head fls j) (req_wz requested_wz);
    relist_view g fls requested_wz
  end

let alloc_lists_preserves_dense_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then
    alloc_lists_list_spec g fls requested_wz
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    unpack g fls j;
    Dense.alloc_spec_preserves_dense_part1 g (fls_head fls j) (req_wz requested_wz);
    relist_view g fls requested_wz
  end

/// ---------------------------------------------------------------------------
/// The free lists
/// ---------------------------------------------------------------------------

let lists (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires alloc_lists_pre g fls)
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    r.obj_out == 0UL \/ lists_post g fls r))
  = if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
    else begin
      on g fls requested_wz;
      let j = alloc_lists_list g fls requested_wz in
      let wz = req_wz requested_wz in
      if relists j (first_fit_size g (fls_head fls j) wz heap_words) wz
      then relist_lists g fls j wz
      else plain_lists g fls j wz
    end

let alloc_lists_preserves_fls_valid_part1 g fls requested_wz =
  alloc_lists_list_spec g fls requested_wz;
  lists g fls requested_wz

let alloc_lists_preserves_fls_terminates_part1 g fls requested_wz =
  alloc_lists_list_spec g fls requested_wz;
  lists g fls requested_wz

let alloc_lists_obj_not_in_lists_part1 g fls requested_wz =
  lists g fls requested_wz

let alloc_lists_preserves_avoids_other g fls requested_wz excl =
  alloc_lists_list_spec g fls requested_wz;
  lists g fls requested_wz

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let alloc_lists_read_other g fls requested_wz other addr =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then
    alloc_lists_list_spec g fls requested_wz
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let wz = req_wz requested_wz in
    let fp = fls_head fls j in
    unpack g fls j;
    if relists j (first_fit_size g fp wz heap_words) wz then begin
      on_found g fp wz;
      relist_confined g fls j wz;
      let c : obj_addr = first_fit_block g fp wz heap_words in
      let p = found_prev g 0UL fp wz heap_words in
      hd_address_spec other;
      extent_kept g (alloc_lists_spec g fls requested_wz).heap_out c (pv p c) p other addr
    end
    else AL.alloc_spec_read_other g fp wz other addr
  end

let alloc_lists_read_header_other_part1 g fls requested_wz excl =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let wz = req_wz requested_wz in
    let fp = fls_head fls j in
    unpack g fls j;
    if relists j (first_fit_size g fp wz heap_words) wz then begin
      on_found g fp wz;
      relist_confined g fls j wz;
      let c : obj_addr = first_fit_block g fp wz heap_words in
      let p = found_prev g 0UL fp wz heap_words in
      header_kept g (alloc_lists_spec g fls requested_wz).heap_out c (pv p c) p excl
    end
    else AP.alloc_spec_read_header_other_part1 g fp wz excl
  end
#pop-options

let alloc_lists_oom_unchanged g fls requested_wz =
  alloc_lists_list_spec g fls requested_wz

/// ---------------------------------------------------------------------------
/// The allocated object
/// ---------------------------------------------------------------------------

let alloc_lists_obj_valid g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    AP.alloc_spec_obj_valid g (fls_head fls j) (req_wz requested_wz)
  end

let alloc_lists_obj_in_objects_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    unpack g fls j;
    AP.alloc_spec_obj_in_objects_part1 g (fls_head fls j) (req_wz requested_wz);
    relist_view g fls requested_wz
  end

let alloc_lists_obj_body_within_heap g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let fp = fls_head fls j in
    let wz = req_wz requested_wz in
    unpack g fls j;
    AP.alloc_spec_obj_in_objects_part1 g fp wz;
    AP.alloc_spec_obj_body_within_heap g fp wz;
    relist_view g fls requested_wz;
    let r = alloc_lists_spec g fls requested_wz in
    same_header (SA.alloc_spec g fp wz).SA.heap_out r.heap_out (r.obj_out <: obj_addr)
  end

/// In a relist, the object's header is the one written for it.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let relist_obj_wosize (g: heap) (fls: fl_state) (requested_wz: nat)
  : Lemma (requires (alloc_lists_spec g fls requested_wz).obj_out <> 0UL /\
                    (let j = alloc_lists_list g fls requested_wz in
                     let fp = fls_head fls j in
                     let wz = req_wz requested_wz in
                     relists j (first_fit_size g fp wz heap_words) wz))
          (ensures (let r = alloc_lists_spec g fls requested_wz in
                    U64.v r.obj_out >= U64.v mword /\ U64.v r.obj_out < heap_size /\
                    U64.v r.obj_out % U64.v mword == 0 /\
                    U64.v (wosize_of_object (r.obj_out <: obj_addr) r.heap_out) ==
                      req_wz requested_wz))
  = on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let fp = fls_head fls j in
    let wz = req_wz requested_wz in
    let w = first_fit_size g fp wz heap_words in
    let c = first_fit_block g fp wz heap_words in
    let r = alloc_lists_spec g fls requested_wz in
    AP.alloc_spec_obj_valid g fp wz;
    let o : obj_addr = r.obj_out in
    hd_address_spec o;
    relist_read g fls j wz (hd_address o);
    hd_address_spec (c <: obj_addr);
    wosize_of_object_spec o r.heap_out;
    AL.make_header_getWosize (U64.uint_to_t wz) SA.white_bits 0UL
#pop-options

let alloc_lists_obj_wosize_exact_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let fp = fls_head fls j in
    let wz = req_wz requested_wz in
    unpack g fls j;
    if relists j (first_fit_size g fp wz heap_words) wz
    then relist_obj_wosize g fls requested_wz
    else AP.alloc_spec_obj_wosize_exact_part1 g fp wz
  end

let alloc_lists_obj_wosize_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let fp = fls_head fls j in
    let wz = req_wz requested_wz in
    unpack g fls j;
    if relists j (first_fit_size g fp wz heap_words) wz
    then relist_obj_wosize g fls requested_wz
    else AP.alloc_spec_obj_wosize_part1 g fp wz
  end

let alloc_lists_obj_wosize_upper_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let fp = fls_head fls j in
    let wz = req_wz requested_wz in
    unpack g fls j;
    if relists j (first_fit_size g fp wz heap_words) wz
    then relist_obj_wosize g fls requested_wz
    else AP.alloc_spec_obj_wosize_upper_part1 g fp wz
  end

let alloc_lists_obj_ne_excl g fls requested_wz excl =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    unpack g fls j;
    AP.alloc_spec_obj_ne_excl g (fls_head fls j) (req_wz requested_wz) excl
  end

let alloc_lists_obj_not_blue_part1 g fls requested_wz =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let fp = fls_head fls j in
    let wz = req_wz requested_wz in
    unpack g fls j;
    AP.alloc_spec_obj_in_objects_part1 g fp wz;
    AP.alloc_spec_obj_not_blue_part1 g fp wz;
    relist_view g fls requested_wz;
    let r = alloc_lists_spec g fls requested_wz in
    same_header (SA.alloc_spec g fp wz).SA.heap_out r.heap_out (r.obj_out <: obj_addr)
  end

let alloc_lists_preserves_blue_part1 g fls requested_wz h =
  if (alloc_lists_spec g fls requested_wz).obj_out = 0UL then ()
  else begin
    on g fls requested_wz;
    let j = alloc_lists_list g fls requested_wz in
    let fp = fls_head fls j in
    let wz = req_wz requested_wz in
    unpack g fls j;
    AL.alloc_spec_preserves_objects_part1 g fp wz;
    AP.alloc_spec_preserves_blue_part1 g fp wz h;
    relist_view g fls requested_wz;
    let r = alloc_lists_spec g fls requested_wz in
    same_header (SA.alloc_spec g fp wz).SA.heap_out r.heap_out h
  end

let alloc_lists_new_objects_blue_part1 g fls requested_wz =
  on g fls requested_wz;
  let j = alloc_lists_list g fls requested_wz in
  let fp = fls_head fls j in
  let wz = req_wz requested_wz in
  unpack g fls j;
  AL.alloc_spec_new_objects_blue_part1 g fp wz;
  relist_view g fls requested_wz;
  let r = alloc_lists_spec g fls requested_wz in
  same_headers (SA.alloc_spec g fp wz).SA.heap_out r.heap_out

let alloc_lists_only_new_is_obj_out_part1 g fls requested_wz =
  on g fls requested_wz;
  let j = alloc_lists_list g fls requested_wz in
  let fp = fls_head fls j in
  let wz = req_wz requested_wz in
  unpack g fls j;
  AL.alloc_spec_only_new_is_obj_out_part1 g fp wz;
  relist_view g fls requested_wz

/// ---------------------------------------------------------------------------
/// The shape of the lists
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let alloc_on_succeeds g fls j wz =
  let fp = fls_head fls j in
  fls_valid_elim g fls;
  if relists j (first_fit_size g fp wz heap_words) wz then on_found g fp wz
  else alloc_on_plain g fls j wz

let alloc_lists_struct g fls requested_wz =
  on g fls requested_wz;
  let j = alloc_lists_list g fls requested_wz in
  let wz = req_wz requested_wz in
  let fp = fls_head fls j in
  unpack g fls j;
  on_found g fp wz;
  if relists j (first_fit_size g fp wz heap_words) wz
  then relist_lists g fls j wz
  else plain_lists g fls j wz
#pop-options
