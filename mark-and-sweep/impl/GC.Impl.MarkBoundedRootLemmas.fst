module GC.Impl.MarkBoundedRootLemmas

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SpecMark = GC.Spec.Mark
module SpecHeap = GC.Spec.Heap
module SpecObject = GC.Spec.Object
module SpecFields = GC.Spec.Fields
module Header = GC.Lib.Header
module MarkBounded = GC.Impl.MarkBounded

open GC.Spec.Base

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0"
let darken_roots_bounded_prefix_base
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (cap: nat)
  : Lemma
      (ensures
        MarkBounded.darken_roots_bounded_prefix_spec g st roots 0 cap == (g, st))
  =
  assert_norm (MarkBounded.darken_roots_bounded_prefix_spec g st roots 0 cap == (g, st))

let check_and_darken_bounded_spec_length_increases_at_most_one
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma
      (ensures
        Seq.length (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)) <=
        Seq.length st + 1)
  =
  if U64.v v >= U64.v zero_addr + U64.v mword &&
     U64.v v < heap_size &&
     U64.v v % U64.v mword = 0
  then
    let h = U64.sub v mword in
    if U64.v h + U64.v mword < heap_size then
      let target = SpecHeap.f_address h in
      if SpecObject.is_white target g then
        if Seq.length st < cap then
          assert (Seq.length (Seq.cons target st) == Seq.length st + 1)
        else ()
      else ()
    else ()
  else ()

let rec darken_roots_bounded_prefix_length_increases_at_most
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (ensures
        Seq.length (snd (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap)) <=
        Seq.length st + idx)
      (decreases idx)
  =
  if idx = 0 then begin
    darken_roots_bounded_prefix_base g st roots cap;
    assert (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap == (g, st))
  end
  else begin
    let idx0 = idx - 1 in
    assert (idx == idx0 + 1);
    assert (idx0 < Seq.length roots);
    darken_roots_bounded_prefix_length_increases_at_most g st roots idx0 cap;
    let (g0, st0) = MarkBounded.darken_roots_bounded_prefix_spec g st roots idx0 cap in
    MarkBounded.darken_roots_bounded_prefix_step g st roots idx0 cap;
    check_and_darken_bounded_spec_length_increases_at_most_one
      g0 st0 (Seq.index roots idx0) cap;
    assert (Seq.length (snd (MarkBounded.check_and_darken_bounded_spec
             g0 st0 (Seq.index roots idx0) cap)) <= Seq.length st0 + 1);
    assert (Seq.length st0 <= Seq.length st + idx0);
    assert (Seq.length st0 + 1 <= Seq.length st + idx);
    assert (Seq.length (snd (MarkBounded.darken_roots_bounded_prefix_spec
             g st roots idx cap)) <= Seq.length st + idx)
  end

let check_and_darken_bounded_spec_preserves_gray_objects_on_stack
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma
      (requires
        SpecMark.gray_objects_on_stack g st /\
        Seq.length st < cap)
      (ensures
        SpecMark.gray_objects_on_stack
          (fst (MarkBounded.check_and_darken_bounded_spec g st v cap))
          (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)))
  =
  let res = MarkBounded.check_and_darken_bounded_spec g st v cap in
  let g' = fst res in
  let st' = snd res in
  if U64.v v >= U64.v zero_addr + U64.v mword &&
     U64.v v < heap_size &&
     U64.v v % U64.v mword = 0
  then
    let h = U64.sub v mword in
    if U64.v h + U64.v mword < heap_size then
      let target = SpecHeap.f_address h in
      if SpecObject.is_white target g then begin
        SpecObject.makeGray_eq target g;
        MarkBounded.check_and_darken_bounded_spec_preserves_objects g st v cap;
        assert (g' == SpecObject.makeGray target g);
        assert (st' == Seq.cons target st);
        let aux (obj: obj_addr)
          : Lemma
              (requires
                Seq.mem obj (SpecFields.objects zero_addr g') /\
                SpecObject.is_gray obj g')
              (ensures Seq.mem obj st')
          =
          assert (Seq.mem obj (SpecFields.objects zero_addr g));
          if obj = target then begin
            SpecFields.mem_cons_lemma obj target st;
            assert (Seq.mem obj (Seq.cons target st))
          end
          else begin
            SpecObject.color_change_preserves_other_color target obj g Header.Gray;
            SpecObject.is_gray_iff obj g;
            SpecObject.is_gray_iff obj g';
            assert (SpecObject.is_gray obj g);
            assert (Seq.mem obj st);
            SpecFields.mem_cons_lemma obj target st;
            assert (Seq.mem obj (Seq.cons target st))
          end
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
      else begin
        let aux (obj: obj_addr)
          : Lemma
              (requires
                Seq.mem obj (SpecFields.objects zero_addr g') /\
                SpecObject.is_gray obj g')
              (ensures Seq.mem obj st')
          =
          assert (g' == g);
          assert (st' == st);
          assert (Seq.mem obj st)
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
    else begin
      let aux (obj: obj_addr)
        : Lemma
            (requires
              Seq.mem obj (SpecFields.objects zero_addr g') /\
              SpecObject.is_gray obj g')
            (ensures Seq.mem obj st')
        =
        assert (g' == g);
        assert (st' == st);
        assert (Seq.mem obj st)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end
  else begin
    let aux (obj: obj_addr)
      : Lemma
          (requires
            Seq.mem obj (SpecFields.objects zero_addr g') /\
            SpecObject.is_gray obj g')
          (ensures Seq.mem obj st')
      =
      assert (g' == g);
      assert (st' == st);
      assert (Seq.mem obj st)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
  end

let check_and_darken_bounded_spec_preserves_stack_mem
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat) (x: obj_addr)
  : Lemma
      (requires Seq.mem x st)
      (ensures
        Seq.mem x (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)))
  =
  if U64.v v >= U64.v zero_addr + U64.v mword &&
     U64.v v < heap_size &&
     U64.v v % U64.v mword = 0
  then
    let h = U64.sub v mword in
    if U64.v h + U64.v mword < heap_size then
      let target = SpecHeap.f_address h in
      if SpecObject.is_white target g then
        if Seq.length st < cap then begin
          assert (snd (MarkBounded.check_and_darken_bounded_spec g st v cap) == Seq.cons target st);
          SpecFields.mem_cons_lemma x target st
        end
        else
          assert (snd (MarkBounded.check_and_darken_bounded_spec g st v cap) == st)
      else
        assert (snd (MarkBounded.check_and_darken_bounded_spec g st v cap) == st)
    else
      assert (snd (MarkBounded.check_and_darken_bounded_spec g st v cap) == st)
  else
    assert (snd (MarkBounded.check_and_darken_bounded_spec g st v cap) == st)

let check_and_darken_bounded_spec_preserves_not_black
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat) (x: obj_addr)
  : Lemma
      (requires ~(SpecObject.is_black x g))
      (ensures
        ~(SpecObject.is_black x (fst (MarkBounded.check_and_darken_bounded_spec g st v cap))))
  =
  if U64.v v >= U64.v zero_addr + U64.v mword &&
     U64.v v < heap_size &&
     U64.v v % U64.v mword = 0
  then
    let h = U64.sub v mword in
    if U64.v h + U64.v mword < heap_size then
      let target = SpecHeap.f_address h in
      if SpecObject.is_white target g then begin
        SpecObject.makeGray_eq target g;
        assert (fst (MarkBounded.check_and_darken_bounded_spec g st v cap) ==
                SpecObject.makeGray target g);
        if x = target then begin
          SpecObject.makeGray_is_gray target g;
          SpecObject.is_gray_iff target (SpecObject.makeGray target g);
          SpecObject.is_black_iff target (SpecObject.makeGray target g)
        end
        else begin
          SpecObject.color_change_preserves_other_color target x g Header.Gray;
          SpecObject.is_black_iff x g;
          SpecObject.is_black_iff x (SpecObject.makeGray target g)
        end
      end
      else
        assert (fst (MarkBounded.check_and_darken_bounded_spec g st v cap) == g)
    else
      assert (fst (MarkBounded.check_and_darken_bounded_spec g st v cap) == g)
  else
    assert (fst (MarkBounded.check_and_darken_bounded_spec g st v cap) == g)

let check_and_darken_bounded_spec_preserves_not_blue
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat) (x: obj_addr)
  : Lemma
      (requires ~(SpecObject.is_blue x g))
      (ensures
        ~(SpecObject.is_blue x (fst (MarkBounded.check_and_darken_bounded_spec g st v cap))))
  =
  if U64.v v >= U64.v zero_addr + U64.v mword &&
     U64.v v < heap_size &&
     U64.v v % U64.v mword = 0
  then
    let h = U64.sub v mword in
    if U64.v h + U64.v mword < heap_size then
      let target = SpecHeap.f_address h in
      if SpecObject.is_white target g then begin
        SpecObject.makeGray_eq target g;
        SpecObject.set_color_preserves_not_blue target x g Header.Gray;
        assert (fst (MarkBounded.check_and_darken_bounded_spec g st v cap) ==
                SpecObject.makeGray target g)
      end
      else
        assert (fst (MarkBounded.check_and_darken_bounded_spec g st v cap) == g)
    else
      assert (fst (MarkBounded.check_and_darken_bounded_spec g st v cap) == g)
  else
    assert (fst (MarkBounded.check_and_darken_bounded_spec g st v cap) == g)

let check_and_darken_bounded_spec_pushes_valid_nonblack_nonblue_root
  (g: heap) (st: Seq.seq obj_addr) (v: U64.t) (cap: nat)
  : Lemma
      (requires
        U64.v v >= U64.v zero_addr + U64.v mword /\
        U64.v v < heap_size /\
        U64.v v % U64.v mword == 0 /\
        MarkBounded.root_points_to_object g v /\
        ~(SpecObject.is_black (v <: obj_addr) g) /\
        ~(SpecObject.is_blue (v <: obj_addr) g) /\
        SpecMark.gray_objects_on_stack g st /\
        Seq.length st < cap)
      (ensures
        Seq.mem (v <: obj_addr)
          (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)))
  =
  let obj = (v <: obj_addr) in
  let h = U64.sub v mword in
  SpecHeap.hd_address_spec obj;
  assert (U64.v h == U64.v (SpecHeap.hd_address obj));
  U64.v_inj h (SpecHeap.hd_address obj);
  assert (h == SpecHeap.hd_address obj);
  SpecHeap.f_hd_roundtrip obj;
  let target = SpecHeap.f_address h in
  assert (target == obj);
  assert (U64.v h + U64.v mword < heap_size);
  assert (Seq.mem obj (SpecFields.objects zero_addr g));
  if SpecObject.is_white obj g then begin
    assert (snd (MarkBounded.check_and_darken_bounded_spec g st v cap) == Seq.cons obj st);
    SpecFields.mem_cons_lemma obj obj st
  end
  else begin
    SpecFields.colors_exhaustive_and_exclusive obj g;
    assert (SpecObject.is_gray obj g);
    assert (Seq.mem obj st);
    assert (snd (MarkBounded.check_and_darken_bounded_spec g st v cap) == st)
  end

let check_and_darken_bounded_spec_preserves_stack_roots
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (v: U64.t) (cap: nat)
  : Lemma
      (requires
        (forall (x: obj_addr). Seq.mem x st ==> Seq.mem (x <: U64.t) roots) /\
        Seq.mem v roots)
      (ensures
        (forall (x: obj_addr).
          Seq.mem x (snd (MarkBounded.check_and_darken_bounded_spec g st v cap)) ==>
          Seq.mem (x <: U64.t) roots))
  =
  let res = MarkBounded.check_and_darken_bounded_spec g st v cap in
  let st' = snd res in
  let aux (x: obj_addr)
    : Lemma
        (requires Seq.mem x st')
        (ensures Seq.mem (x <: U64.t) roots)
    =
    if U64.v v >= U64.v zero_addr + U64.v mword &&
       U64.v v < heap_size &&
       U64.v v % U64.v mword = 0
    then
      let h = U64.sub v mword in
      if U64.v h + U64.v mword < heap_size then
        let target = SpecHeap.f_address h in
        if SpecObject.is_white target g then
          if Seq.length st < cap then begin
            assert (st' == Seq.cons target st);
            SpecFields.mem_cons_lemma x target st;
            if x = target then begin
              let obj = (v <: obj_addr) in
              SpecHeap.hd_address_spec obj;
              assert (U64.v h == U64.v (SpecHeap.hd_address obj));
              U64.v_inj h (SpecHeap.hd_address obj);
              assert (h == SpecHeap.hd_address obj);
              SpecHeap.f_hd_roundtrip obj;
              assert (target == obj);
              assert ((x <: U64.t) == v)
            end
            else
              assert (Seq.mem (x <: U64.t) roots)
          end
          else begin
            assert (st' == st);
            assert (Seq.mem (x <: U64.t) roots)
          end
        else begin
          assert (st' == st);
          assert (Seq.mem (x <: U64.t) roots)
        end
      else begin
        assert (st' == st);
        assert (Seq.mem (x <: U64.t) roots)
      end
    else begin
      assert (st' == st);
      assert (Seq.mem (x <: U64.t) roots)
    end
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let rec darken_roots_bounded_prefix_preserves_gray_objects_on_stack
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t)
  (idx: nat{idx <= Seq.length roots}) (cap: nat)
  : Lemma
      (requires
        SpecMark.gray_objects_on_stack g st /\
        Seq.length st + idx <= cap)
      (ensures
        SpecMark.gray_objects_on_stack
          (fst (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap))
          (snd (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap)))
      (decreases idx)
  =
  if idx = 0 then begin
    darken_roots_bounded_prefix_base g st roots cap;
    assert (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap == (g, st))
  end
  else begin
    let idx0 = idx - 1 in
    assert (idx == idx0 + 1);
    assert (idx0 < Seq.length roots);
    darken_roots_bounded_prefix_preserves_gray_objects_on_stack
      g st roots idx0 cap;
    let (g0, st0) = MarkBounded.darken_roots_bounded_prefix_spec g st roots idx0 cap in
    darken_roots_bounded_prefix_length_increases_at_most
      g st roots idx0 cap;
    assert (Seq.length st0 <= Seq.length st + idx0);
    assert (idx0 < idx);
    assert (Seq.length st0 < cap);
    MarkBounded.darken_roots_bounded_prefix_step g st roots idx0 cap;
    check_and_darken_bounded_spec_preserves_gray_objects_on_stack
      g0 st0 (Seq.index roots idx0) cap;
    assert (SpecMark.gray_objects_on_stack
      (fst (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap))
      (snd (MarkBounded.darken_roots_bounded_prefix_spec g st roots idx cap)))
  end

let darken_roots_bounded_spec_preserves_gray_objects_on_stack
  (g: heap) (st: Seq.seq obj_addr) (roots: Seq.seq U64.t) (cap: nat)
  : Lemma
      (requires
        SpecMark.gray_objects_on_stack g st /\
        Seq.length st + Seq.length roots <= cap)
      (ensures
        SpecMark.gray_objects_on_stack
          (fst (MarkBounded.darken_roots_bounded_spec g st roots cap))
          (snd (MarkBounded.darken_roots_bounded_spec g st roots cap)))
  =
  darken_roots_bounded_prefix_preserves_gray_objects_on_stack
    g st roots (Seq.length roots) cap
#pop-options
