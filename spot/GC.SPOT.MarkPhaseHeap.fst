module GC.SPOT.MarkPhaseHeap

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields

module U64 = FStar.UInt64
module Header = GC.Lib.Header
module MP = GC.Spec.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 10"

let at r k = mk_hp_addr (U64.v zero_addr + 8 * k)

let one : wosize = assert_norm (1 < pow2 54); 1UL

let hdr (c: color) : U64.t = makeHeader one c 0UL

let free_wz_nat (r: unit{room}) : n: nat{n < pow2 54 /\ U64.v zero_addr + 64 + (n + 1) * 8 == heap_size} =
  let d = heap_size - (U64.v zero_addr + 64) in
  FStar.Math.Lemmas.lemma_div_exact d 8;
  FStar.Math.Lemmas.pow2_plus 3 54; assert_norm (pow2 3 == 8);
  assert (d / 8 < pow2 54);
  d / 8 - 1

let free_wz (r: unit{room}) : wosize = U64.uint_to_t (free_wz_nat r)

let fhdr (r: unit{room}) : U64.t = makeHeader (free_wz r) Header.Blue 0UL

let zero_major : heap = Seq.create heap_size 0uy

let heap4 r col tg =
  let g1 = write_word zero_major (at r 0) (hdr (col 1)) in
  let g2 = write_word g1 (at r 1) (fv r (tg 1)) in
  let g3 = write_word g2 (at r 2) (hdr (col 2)) in
  let g4 = write_word g3 (at r 3) (fv r (tg 2)) in
  let g5 = write_word g4 (at r 4) (hdr (col 3)) in
  let g6 = write_word g5 (at r 5) (fv r (tg 3)) in
  let g7 = write_word g6 (at r 6) (hdr (col 4)) in
  let g8 = write_word g7 (at r 7) (fv r (tg 4)) in
  write_word g8 (at r 8) (fhdr r)

/// Reading through one write.
let rw (g: heap) (x: hp_addr) (v: U64.t) (a: hp_addr)
  : Lemma (read_word (write_word g x v) a == (if a = x then v else read_word g a))
  = if a = x then read_write_same g x v else read_write_different g x a v

/// The word written at `at r k`.
let word (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) (k: nat{k <= 8}) : U64.t =
  if k = 8 then fhdr r
  else if k % 2 = 0 then hdr (col (k / 2 + 1))
  else fv r (tg ((k + 1) / 2))

#push-options "--z3rlimit 20"
let reads (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) (k: nat{k <= 8})
  : Lemma (read_word (heap4 r col tg) (at r k) == word r col tg k)
  = let g1 = write_word zero_major (at r 0) (hdr (col 1)) in
    let g2 = write_word g1 (at r 1) (fv r (tg 1)) in
    let g3 = write_word g2 (at r 2) (hdr (col 2)) in
    let g4 = write_word g3 (at r 3) (fv r (tg 2)) in
    let g5 = write_word g4 (at r 4) (hdr (col 3)) in
    let g6 = write_word g5 (at r 5) (fv r (tg 3)) in
    let g7 = write_word g6 (at r 6) (hdr (col 4)) in
    let g8 = write_word g7 (at r 7) (fv r (tg 4)) in
    let a = at r k in
    rw g8 (at r 8) (fhdr r) a;
    rw g7 (at r 7) (fv r (tg 4)) a;
    rw g6 (at r 6) (hdr (col 4)) a;
    rw g5 (at r 5) (fv r (tg 3)) a;
    rw g4 (at r 4) (hdr (col 3)) a;
    rw g3 (at r 3) (fv r (tg 2)) a;
    rw g2 (at r 2) (hdr (col 2)) a;
    rw g1 (at r 1) (fv r (tg 1)) a;
    rw zero_major (at r 0) (hdr (col 1)) a
#pop-options

let hdr_facts (c: color)
  : Lemma (getWosize (hdr c) == one /\ getColor (hdr c) == c /\ getTag (hdr c) == 0UL)
  = makeHeader_getWosize one c 0UL;
    makeHeader_getColor one c 0UL;
    makeHeader_getTag one c 0UL

let fhdr_facts (r: unit{room})
  : Lemma (getWosize (fhdr r) == free_wz r /\ getColor (fhdr r) == Header.Blue /\ getTag (fhdr r) == 0UL)
  = makeHeader_getWosize (free_wz r) Header.Blue 0UL;
    makeHeader_getColor (free_wz r) Header.Blue 0UL;
    makeHeader_getTag (free_wz r) Header.Blue 0UL

let hd_obj (r: unit{room}) (i: idx)
  : Lemma (hd_address (obj r i) == at r (2 * i - 2))
  = hd_address_spec (obj r i)

let hd_free (r: unit{room}) : Lemma (hd_address (free_obj r) == at r 8)
  = hd_address_spec (free_obj r)

/// Header facts of object `i`.
let obj_header (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt) (i: idx)
  : Lemma (let h = heap4 r col tg in
           read_word h (hd_address (obj r i)) == hdr (col i) /\
           wosize_of_object (obj r i) h == one /\ color_of_object (obj r i) h == col i /\
           tag_of_object (obj r i) h == 0UL)
  = let h = heap4 r col tg in
    hd_obj r i;
    reads r col tg (2 * i - 2);
    hdr_facts (col i);
    wosize_of_object_spec (obj r i) h;
    color_of_object_spec (obj r i) h;
    tag_of_object_spec (obj r i) h

let free_header (r: unit{room}) (col: idx -> ccol) (tg: idx -> tgt)
  : Lemma (let h = heap4 r col tg in
           wosize_of_object (free_obj r) h == free_wz r /\ color_of_object (free_obj r) h == Header.Blue /\
           tag_of_object (free_obj r) h == 0UL)
  = let h = heap4 r col tg in
    hd_free r;
    reads r col tg 8;
    fhdr_facts r;
    wosize_of_object_spec (free_obj r) h;
    color_of_object_spec (free_obj r) h;
    tag_of_object_spec (free_obj r) h

let f_at (r: unit{room}) (k: nat{k <= 8}) : Lemma (f_address (at r k) == at r (k + 1))
  = f_address_spec (at r k)

#push-options "--z3rlimit 20"
let objects_eq r col tg =
  let h = heap4 r col tg in
  let step (k: nat{k <= 6 /\ k % 2 == 0})
    : Lemma (objects (at r k) h == Seq.cons (at r (k + 1)) (objects (at r (k + 2)) h))
    = reads r col tg k;
      hdr_facts (col (k / 2 + 1));
      f_at r k;
      objects_cons_step_to (at r k) h (at r (k + 2))
  in
  step 0; step 2; step 4; step 6;
  reads r col tg 8; fhdr_facts r; f_at r 8;
  objects_cons_end (at r 8) h;
  assert (at r 0 == zero_addr)
#pop-options

let object_cases r col tg x =
  objects_eq r col tg;
  let s4 = Seq.cons (free_obj r) Seq.empty in
  let s3 = Seq.cons (obj r 4) s4 in
  let s2 = Seq.cons (obj r 3) s3 in
  let s1 = Seq.cons (obj r 2) s2 in
  mem_cons_lemma x (obj r 1) s1;
  mem_cons_lemma x (obj r 2) s2;
  mem_cons_lemma x (obj r 3) s3;
  mem_cons_lemma x (obj r 4) s4;
  mem_cons_lemma x (free_obj r) Seq.empty;
  assert_norm (~(Seq.mem x (Seq.empty #obj_addr)))

let colour_preds (o: obj_addr) (h: heap)
  : Lemma ((is_black o h <==> color_of_object o h == Header.Black) /\
           (is_gray o h <==> color_of_object o h == Header.Gray) /\
           (is_white o h <==> color_of_object o h == Header.White) /\
           (is_blue o h <==> color_of_object o h == Header.Blue))
  = is_black_iff o h; is_gray_iff o h; is_white_iff o h; is_blue_iff o h

let tag0 (o: obj_addr) (h: heap)
  : Lemma (requires tag_of_object o h == 0UL)
          (ensures ~(is_no_scan o h) /\ ~(is_infix o h) /\ ~(is_closure o h))
  = is_no_scan_spec o h; no_scan_tag_val ();
    is_infix_spec o h; infix_tag_val ();
    is_closure_spec o h; closure_tag_val ()

let obj_facts r col tg i =
  let h = heap4 r col tg in
  object_cases r col tg (obj r i);
  obj_header r col tg i;
  colour_preds (obj r i) h;
  tag0 (obj r i) h;
  resolve_non_infix (obj r i) h;
  reads r col tg (2 * i - 1)

let free_facts r col tg =
  let h = heap4 r col tg in
  object_cases r col tg (free_obj r);
  free_header r col tg;
  colour_preds (free_obj r) h

/// `fv` is a pointer exactly when it names an object.
let fv_pointer (r: unit{room}) (t: tgt)
  : Lemma (is_pointer (fv r t) <==> t <> 0)
  = zero_addr_above_2048 ()

#push-options "--fuel 2 --z3rlimit 20"
let points_to_iff r col tg i c =
  let h = heap4 r col tg in
  let o = obj r i in
  obj_facts r col tg i;
  fv_pointer r (tg i);
  assert (U64.add_mod o (U64.mul_mod 0UL mword) == o);
  if tg i <> 0 && obj r (tg i) <> c then hd_address_injective (obj r (tg i)) c
#pop-options

let field_edge_iff r col tg i y =
  let h = heap4 r col tg in
  obj_facts r col tg i;
  FStar.Classical.forall_intro (points_to_iff r col tg i);
  if tg i <> 0 then begin
    obj_facts r col tg (tg i);
    assert (points_to h (obj r i) (obj r (tg i)))
  end

let wf r col tg =
  let h = heap4 r col tg in
  let fit (x: obj_addr)
    : Lemma (requires Seq.mem x (objects zero_addr h))
            (ensures U64.v (hd_address x) + 8 + U64.v (wosize_of_object x h) * 8 <= Seq.length h /\
                     ~(is_infix x h))
    = object_cases r col tg x;
      if x = free_obj r then begin
        hd_free r; free_header r col tg; tag0 x h
      end else if x = obj r 1 then (hd_obj r 1; obj_header r col tg 1; tag0 x h)
      else if x = obj r 2 then (hd_obj r 2; obj_header r col tg 2; tag0 x h)
      else if x = obj r 3 then (hd_obj r 3; obj_header r col tg 3; tag0 x h)
      else (hd_obj r 4; obj_header r col tg 4; tag0 x h)
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires fit);
  assert (blocks_fit h);
  assert (no_infix_block h);
  let field_closure (src: obj_addr) (j: nat)
    : Lemma (requires in_use free_stw h src /\ ~(is_no_scan src h) /\
                      j < U64.v (wosize_of_object src h) /\
                      U64.v src + j * 8 + 8 <= heap_size)
            (ensures (let w = read_word h (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==> in_use free_stw h (w <: obj_addr)))
    = object_cases r col tg src;
      free_facts r col tg;
      let one_obj (i: idx) : Lemma (requires src == obj r i) (ensures (let w = read_word h (U64.uint_to_t (U64.v src + j * 8)) in
                      is_pointer w ==> in_use free_stw h (w <: obj_addr)))
        = obj_facts r col tg i;
          fv_pointer r (tg i);
          assert (j == 0);
          assert (U64.uint_to_t (U64.v src + j * 8) == src);
          if tg i <> 0 then obj_facts r col tg (tg i)
      in
      if src = obj r 1 then one_obj 1
      else if src = obj r 2 then one_obj 2
      else if src = obj r 3 then one_obj 3
      else if src = obj r 4 then one_obj 4
      else ()
  in
  pointer_clauses_from_raw_field_closure h field_closure;
  wf_parts ()

/// ---------------------------------------------------------------------------
/// The walk and the free block
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20"
let zero_major_read_word (addr: hp_addr)
  : Lemma (requires U64.v addr + 8 <= heap_size)
          (ensures read_word zero_major addr == 0UL)
  = read_word_spec zero_major addr;
    assert (Seq.index zero_major (U64.v addr) == 0uy);
    assert (Seq.index zero_major (U64.v addr + 1) == 0uy);
    assert (Seq.index zero_major (U64.v addr + 2) == 0uy);
    assert (Seq.index zero_major (U64.v addr + 3) == 0uy);
    assert (Seq.index zero_major (U64.v addr + 4) == 0uy);
    assert (Seq.index zero_major (U64.v addr + 5) == 0uy);
    assert (Seq.index zero_major (U64.v addr + 6) == 0uy);
    assert (Seq.index zero_major (U64.v addr + 7) == 0uy);
    assert_norm (combine_bytes 0uy 0uy 0uy 0uy 0uy 0uy 0uy 0uy == 0UL)
#pop-options

#push-options "--z3rlimit 20"
let objects_from r col tg k =
  let h = heap4 r col tg in
  objects_eq r col tg;
  f_at r k;
  reads r col tg k;
  if k < 8 then begin
    hdr_facts (col (k / 2 + 1));
    let step (k: nat{k <= 6 /\ k % 2 == 0})
      : Lemma (objects (at r k) h == Seq.cons (at r (k + 1)) (objects (at r (k + 2)) h))
      = reads r col tg k;
        hdr_facts (col (k / 2 + 1));
        f_at r k;
        objects_cons_step_to (at r k) h (at r (k + 2))
    in
    step k
  end else begin
    fhdr_facts r;
    objects_cons_end (at r 8) h
  end
#pop-options

#push-options "--z3rlimit 20"
let free_block r col tg =
  let h = heap4 r col tg in
  hd_free r;
  free_header r col tg;
  let g1 = write_word zero_major (at r 0) (hdr (col 1)) in
  let g2 = write_word g1 (at r 1) (fv r (tg 1)) in
  let g3 = write_word g2 (at r 2) (hdr (col 2)) in
  let g4 = write_word g3 (at r 3) (fv r (tg 2)) in
  let g5 = write_word g4 (at r 4) (hdr (col 3)) in
  let g6 = write_word g5 (at r 5) (fv r (tg 3)) in
  let g7 = write_word g6 (at r 6) (hdr (col 4)) in
  let g8 = write_word g7 (at r 7) (fv r (tg 4)) in
  let a = free_obj r in
  rw g8 (at r 8) (fhdr r) a;
  rw g7 (at r 7) (fv r (tg 4)) a;
  rw g6 (at r 6) (hdr (col 4)) a;
  rw g5 (at r 5) (fv r (tg 3)) a;
  rw g4 (at r 4) (hdr (col 3)) a;
  rw g3 (at r 3) (fv r (tg 2)) a;
  rw g2 (at r 2) (hdr (col 2)) a;
  rw g1 (at r 1) (fv r (tg 1)) a;
  rw zero_major (at r 0) (hdr (col 1)) a;
  zero_major_read_word a
#pop-options
