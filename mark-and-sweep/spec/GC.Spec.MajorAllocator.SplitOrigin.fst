module GC.Spec.MajorAllocator.SplitOrigin

module U64 = FStar.UInt64
module Seq = FStar.Seq
module MH = GC.Spec.MajorHeap
module MHMember = GC.Spec.MajorHeap.Member
module MA = GC.Spec.MajorAllocator
module SplitShape = GC.Spec.MajorAllocator.SplitShape
module Alloc = GC.Spec.Allocator
module AllocCore = GC.Spec.Allocator.Lemmas.Core
module AllocHeader = GC.Spec.Allocator.Lemmas.Header
module Obj = GC.Spec.Object
module Header = GC.Lib.Header
module Fields = GC.Spec.Fields

open GC.Spec.Base
open GC.Spec.Heap

#push-options "--split_queries always --z3rlimit 1 --fuel 0 --ifuel 0"
private let split_remainder_wosize_sum
  (requested_wz block_wz rem_wz: nat)
  : Lemma
      (requires
        requested_wz + 2 <= block_wz /\
        rem_wz == block_wz - requested_wz - 1)
      (ensures
        (1 + requested_wz) + (rem_wz + 1) == 1 + block_wz)
  =
  assert (block_wz - requested_wz >= 2);
  assert (rem_wz + 1 == block_wz - requested_wz);
  assert (requested_wz + (block_wz - requested_wz) == block_wz);
  assert (requested_wz + rem_wz + 1 == block_wz)

private let split_remainder_obj_addr_arith
  (hdv requested_wz: nat)
  : Lemma
      (requires U64.v mword == 8)
      (ensures
        (hdv + (1 + requested_wz) * 8) + U64.v mword ==
          hdv + (requested_wz + 2) * 8 /\
        ((hdv + (1 + requested_wz) * 8) + U64.v mword) + 8 ==
          hdv + (requested_wz + 3) * 8)
  =
  FStar.Math.Lemmas.distributivity_add_left (1 + requested_wz) 1 8;
  assert ((1 + requested_wz) * 8 + 8 == (requested_wz + 2) * 8);
  FStar.Math.Lemmas.paren_add_right hdv ((1 + requested_wz) * 8) 8;
  FStar.Math.Lemmas.distributivity_add_left (requested_wz + 2) 1 8;
  assert ((requested_wz + 2) * 8 + 8 == (requested_wz + 3) * 8);
  FStar.Math.Lemmas.paren_add_right hdv ((requested_wz + 2) * 8) 8
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 0 --ifuel 0"
private let selected_head_split_header_read_region
  (mh: MH.major_heap) (idx: nat) (obj x: obj_addr) (old_hdr: U64.t)
  (requested_wz block_wz: nat) (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        Seq.mem x (MH.major_objects mh) /\
        x <> obj /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        MH.read_word_in_major mh (hd_address x) == Some old_hdr /\
        MH.object_wosize_in_chunk (Seq.index mh idx) obj == block_wz /\
        requested_wz > 0 /\
        block_wz - requested_wz >= 2 /\
        U64.v rem_hd ==
          U64.v (hd_address obj) + (1 + requested_wz) * U64.v mword /\
        U64.v rem_obj == U64.v rem_hd + U64.v mword)
      (ensures
        (let c = Seq.index mh idx in
         let hd = hd_address obj in
         let xhd = hd_address x in
         ((MH.word_in_chunk c xhd /\
           (xhd = hd \/
            U64.v xhd + U64.v mword <= U64.v hd \/
            (U64.v hd + U64.v mword <= U64.v xhd /\
             U64.v xhd + U64.v mword <= U64.v rem_hd) \/
            U64.v rem_obj + U64.v mword <= U64.v xhd)) \/
          ~(MH.chunk_contains_addr c xhd))))
  =
  let c = Seq.index mh idx in
  let hd = hd_address obj in
  let xhd = hd_address x in
  MH.read_word_in_major_lookup_index mh xhd old_hdr;
  let xidx = MH.lookup_chunk_index_value mh xhd in
  assert (MH.lookup_chunk_index mh xhd == Some xidx);
  assert (xidx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh xidx) xhd);
  if xidx = idx then begin
    assert (Seq.index mh xidx == c);
    assert (MH.word_in_chunk c xhd);
    MH.major_objects_member_in_lookup_chunk mh idx x;
    assert (Seq.mem x (MH.objects_in_chunk c));
    hd_address_spec obj;
    hd_address_spec x;
    if U64.v x < U64.v obj then begin
      MH.word_aligned_gt_at_least_mword (U64.v obj) (U64.v x);
      assert (U64.v x + U64.v mword <= U64.v obj);
      assert (U64.v hd + U64.v mword == U64.v obj);
      assert (U64.v x <= U64.v hd);
      assert (U64.v xhd + U64.v mword == U64.v x);
      assert (U64.v xhd + U64.v mword <= U64.v hd)
    end else begin
      assert (U64.v obj < U64.v x);
      MH.objects_in_chunk_separated c obj x;
      assert (U64.v x >
              U64.v obj + MH.object_wosize_in_chunk c obj * U64.v mword);
      assert (MH.object_wosize_in_chunk c obj == block_wz);
      let old_end = U64.v hd + (1 + block_wz) * U64.v mword in
      assert (old_end == U64.v obj + block_wz * U64.v mword);
      assert (U64.v x > old_end);
      MA.aligned_plus_word_product (U64.v hd) (1 + block_wz);
      assert (old_end % U64.v mword == 0);
      MH.word_aligned_gt_at_least_mword (U64.v x) old_end;
      assert (U64.v x >= old_end + U64.v mword);
      assert (U64.v xhd + U64.v mword == U64.v x);
      assert (U64.v xhd >= old_end);
      assert (requested_wz + 2 <= block_wz);
      FStar.Math.Lemmas.distributivity_add_left (requested_wz + 2) 1 8;
      assert (U64.v mword == 8);
      assert (U64.v rem_obj + U64.v mword ==
              U64.v hd + (requested_wz + 3) * U64.v mword);
      assert (requested_wz + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.lemma_mult_le_right
        (U64.v mword) (requested_wz + 3) (1 + block_wz);
      assert (U64.v rem_obj + U64.v mword <= old_end);
      assert (U64.v rem_obj + U64.v mword <= U64.v xhd)
    end
  end else begin
    if MH.chunk_contains_addr c xhd then begin
      assert (MH.chunk_contains_addr (Seq.index mh xidx) xhd);
      MH.chunks_pairwise_disjoint_index mh idx xidx;
      assert (MH.chunks_disjoint c (Seq.index mh xidx));
      MH.chunks_disjoint_no_shared_addr c (Seq.index mh xidx) xhd;
      assert False
    end
  end
#pop-options

#push-options "--split_queries always --z3rlimit 20 --fuel 3 --ifuel 1"
private let rec objects_in_chunk_from_head_split_member_origin
  (c: MH.heap_chunk) (start: hp_addr) (obj x: obj_addr)
  (requested_wz block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr)
  : Lemma
      (requires
        Seq.mem obj (MH.objects_in_chunk_from c start) /\
        requested_wz > 0 /\
        requested_wz < pow2 54 /\
        requested_wz < pow2 64 /\
        block_wz >= requested_wz /\
        block_wz < pow2 54 /\
        block_wz - requested_wz >= 2 /\
        U64.v rem_wz_u == block_wz - requested_wz - 1 /\
        MH.word_in_chunk c (hd_address obj) /\
        U64.v (Obj.getWosize
          (MH.read_word_in_chunk c (hd_address obj))) == block_wz /\
        MH.word_in_chunk c rem_hd /\
        MH.word_in_chunk c rem_obj /\
        U64.v rem_hd ==
          U64.v (hd_address obj) + (1 + requested_wz) * U64.v mword /\
        U64.v rem_obj == U64.v rem_hd + U64.v mword /\
        U64.v (hd_address obj) + (1 + block_wz) * U64.v mword <=
          MH.chunk_end c /\
        (let hd = hd_address obj in
         let alloc_hdr =
           Alloc.make_header
             (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
         let c1 = MH.write_word_in_chunk c hd alloc_hdr in
         let rem_hdr =
           Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
         let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
         let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
         Seq.mem x (MH.objects_in_chunk_from c3 start)))
      (ensures
        x == obj \/
        x == rem_obj \/
        Seq.mem x (MH.objects_in_chunk_from c start))
      (decreases MH.chunk_end c - U64.v start)
  =
  let hd = hd_address obj in
  let alloc_hdr =
    Alloc.make_header
      (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
  let c1 = MH.write_word_in_chunk c hd alloc_hdr in
  let rem_hdr =
    Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
  let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
  let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
  MH.write_word_in_chunk_preserves_range c hd alloc_hdr;
  MH.write_word_in_chunk_preserves_range c1 rem_hd rem_hdr;
  MH.write_word_in_chunk_preserves_range c2 rem_obj next_fp;
  assert (MH.chunk_start c1 == MH.chunk_start c);
  assert (MH.chunk_end c1 == MH.chunk_end c);
  assert (MH.chunk_start c2 == MH.chunk_start c);
  assert (MH.chunk_end c2 == MH.chunk_end c);
  assert (MH.chunk_start c3 == MH.chunk_start c);
  assert (MH.chunk_end c3 == MH.chunk_end c);
  if x = obj then ()
  else if x = rem_obj then ()
  else if U64.v start < MH.chunk_start c then
    assert False
  else if U64.v start + U64.v mword >= MH.chunk_end c then
    assert False
  else begin
    assert (MH.word_in_chunk c start);
    let header = MH.read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words = U64.v wz + 1 in
    let next_start_nat =
      U64.v start + obj_size_words * U64.v mword in
    if next_start_nat > MH.chunk_end c || next_start_nat >= pow2 64 then
      assert False
    else begin
      f_address_spec start;
      let first : obj_addr = f_address start in
      if first = obj then begin
        hd_f_roundtrip start;
        assert (hd == start);
        assert (MH.read_word_in_chunk c hd == header);
        assert (U64.v wz == block_wz);
        assert (obj_size_words == block_wz + 1);
        let old_next_nat =
          U64.v hd + (1 + block_wz) * U64.v mword in
        assert (next_start_nat == old_next_nat);
        assert (next_start_nat <= MH.chunk_end c);
        assert (MH.chunk_end c <= heap_size);
        AllocHeader.make_header_getWosize
          (U64.uint_to_t requested_wz) Alloc.white_bits 0UL;
        assert (Obj.getWosize alloc_hdr == U64.uint_to_t requested_wz);
        assert (U64.v (Obj.getWosize alloc_hdr) == requested_wz);
        MH.read_write_in_chunk_same c hd alloc_hdr;
        MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr hd;
        FStar.Math.Lemmas.lemma_mult_le_right
          (U64.v mword) 1 (1 + requested_wz);
        assert (U64.v hd + U64.v mword <= U64.v rem_hd);
        MH.read_write_in_chunk_different c1 rem_hd hd rem_hdr;
        MH.write_word_in_chunk_preserves_word c2 rem_obj next_fp hd;
        assert (U64.v hd + U64.v mword <= U64.v rem_obj);
        MH.read_write_in_chunk_different c2 rem_obj hd next_fp;
        assert (MH.read_word_in_chunk c3 hd == alloc_hdr);
        assert (U64.v hd +
                (U64.v (Obj.getWosize
                  (MH.read_word_in_chunk c3 hd)) + 1) * U64.v mword ==
                U64.v rem_hd);
        assert (U64.v rem_hd < MH.chunk_end c3);
        assert (U64.v rem_hd < pow2 64);
        MH.objects_in_chunk_from_cons_step c3 start;
        let tail_after_head = MH.objects_in_chunk_from c3 rem_hd in
        Fields.mem_cons_lemma x first tail_after_head;
        assert (Seq.mem x tail_after_head);
        AllocHeader.make_header_getWosize rem_wz_u Alloc.blue_bits 0UL;
        assert (Obj.getWosize rem_hdr == rem_wz_u);
        MH.read_write_in_chunk_same c1 rem_hd rem_hdr;
        MH.write_word_in_chunk_preserves_word c2 rem_obj next_fp rem_hd;
        MH.read_write_in_chunk_different c2 rem_obj rem_hd next_fp;
        assert (MH.read_word_in_chunk c3 rem_hd == rem_hdr);
        assert (U64.v rem_wz_u == block_wz - requested_wz - 1);
        split_remainder_wosize_sum requested_wz block_wz (U64.v rem_wz_u);
        FStar.Math.Lemmas.distributivity_add_left
          (1 + requested_wz) (U64.v rem_wz_u + 1) (U64.v mword);
        assert (((1 + requested_wz) + (U64.v rem_wz_u + 1)) *
                  U64.v mword ==
                (1 + requested_wz) * U64.v mword +
                (U64.v rem_wz_u + 1) * U64.v mword);
        assert ((1 + requested_wz) + (U64.v rem_wz_u + 1) ==
                1 + block_wz);
        assert (U64.v rem_hd +
                  (U64.v (Obj.getWosize
                    (MH.read_word_in_chunk c3 rem_hd)) + 1) *
                    U64.v mword ==
                old_next_nat);
        f_address_spec rem_hd;
        assert (f_address rem_hd == rem_obj);
        assert (MH.chunk_end c3 == MH.chunk_end c);
        assert (MH.chunk_end c3 <= heap_size);
        assert (heap_size < pow2 64);
        assert (old_next_nat <= MH.chunk_end c3);
        assert (old_next_nat < pow2 64);
        assert (MH.word_in_chunk c3 rem_hd);
        assert (MH.word_in_chunk c3 rem_obj);
        assert (U64.v rem_obj == U64.v rem_hd + U64.v mword);
        assert (U64.v rem_hd + U64.v mword < MH.chunk_end c3);
        if old_next_nat >= MH.chunk_end c3 then begin
          assert (~(old_next_nat < MH.chunk_end c3));
          MH.objects_in_chunk_from_cons_step c3 rem_hd;
          assert (tail_after_head == Seq.cons rem_obj (Seq.empty #obj_addr));
          Fields.mem_cons_lemma x rem_obj (Seq.empty #obj_addr);
          assert False
        end else begin
          assert (old_next_nat < MH.chunk_end c3);
          assert (old_next_nat < heap_size);
          assert (old_next_nat < pow2 64);
          assert (old_next_nat ==
                  U64.v rem_hd +
                    (U64.v rem_wz_u + 1) * U64.v mword);
          assert (U64.v mword > 0);
          assert (0 <= U64.v rem_wz_u + 1);
          FStar.Math.Lemmas.lemma_mult_le_right
            (U64.v mword) 0 (U64.v rem_wz_u + 1);
          assert (0 <= (U64.v rem_wz_u + 1) * U64.v mword);
          assert (0 <= U64.v rem_hd);
          assert (0 <= old_next_nat);
          assert (U64.v rem_hd % U64.v mword == 0);
          MH.next_object_start_aligned rem_hd (U64.v rem_wz_u + 1);
          assert (old_next_nat == next_start_nat);
          assert (old_next_nat % U64.v mword == 0);
          MH.objects_in_chunk_from_cons_step c3 rem_hd;
          let old_next : hp_addr = U64.uint_to_t old_next_nat in
          let old_tail3 = MH.objects_in_chunk_from c3 old_next in
          Fields.mem_cons_lemma x rem_obj old_tail3;
          assert (Seq.mem x old_tail3);
          assert (U64.v old_next == old_next_nat);
          assert (U64.v old_next ==
                  U64.v rem_hd +
                    (U64.v rem_wz_u + 1) * U64.v mword);
          assert (U64.v mword > 0);
          FStar.Math.Lemmas.lemma_mult_le_right
            (U64.v mword) 0 (U64.v rem_wz_u + 1);
          assert (0 <= (U64.v rem_wz_u + 1) * U64.v mword);
          assert (1 <= 1 + requested_wz);
          FStar.Math.Lemmas.lemma_mult_le_right
            (U64.v mword) 1 (1 + requested_wz);
          assert (U64.v mword <= (1 + requested_wz) * U64.v mword);
          assert (U64.v rem_hd ==
                  U64.v hd + (1 + requested_wz) * U64.v mword);
          assert (U64.v hd + U64.v mword <= U64.v rem_hd);
          assert (U64.v rem_hd <= U64.v old_next);
          assert (U64.v hd + U64.v mword <= U64.v old_next);
          MH.objects_in_chunk_from_write_before_preserves
            c old_next hd alloc_hdr;
          assert (MH.objects_in_chunk_from c1 old_next ==
                  MH.objects_in_chunk_from c old_next);
          assert (1 <= U64.v rem_wz_u + 1);
          FStar.Math.Lemmas.lemma_mult_le_right
            (U64.v mword) 1 (U64.v rem_wz_u + 1);
          assert (U64.v mword <=
                  (U64.v rem_wz_u + 1) * U64.v mword);
          assert (U64.v rem_hd + U64.v mword <= U64.v old_next);
          MH.objects_in_chunk_from_write_before_preserves
            c1 old_next rem_hd rem_hdr;
          assert (MH.objects_in_chunk_from c2 old_next ==
                  MH.objects_in_chunk_from c1 old_next);
          assert (U64.v rem_wz_u >= 1);
          assert (2 <= U64.v rem_wz_u + 1);
          FStar.Math.Lemmas.lemma_mult_le_right
            (U64.v mword) 2 (U64.v rem_wz_u + 1);
          assert (2 * U64.v mword <=
                  (U64.v rem_wz_u + 1) * U64.v mword);
          FStar.Math.Lemmas.paren_add_right
            (U64.v rem_hd) (U64.v mword) (U64.v mword);
          assert (U64.v rem_obj + U64.v mword ==
                  U64.v rem_hd + 2 * U64.v mword);
          assert (U64.v rem_obj + U64.v mword <= U64.v old_next);
          MH.objects_in_chunk_from_write_before_preserves
            c2 old_next rem_obj next_fp;
          assert (MH.objects_in_chunk_from c3 old_next ==
                  MH.objects_in_chunk_from c2 old_next);
          assert (Seq.mem x (MH.objects_in_chunk_from c old_next));
          MH.objects_in_chunk_from_tail_mem c start old_next x;
          assert (Seq.mem x (MH.objects_in_chunk_from c start))
        end
      end else begin
        let tail =
          if next_start_nat >= MH.chunk_end c then Seq.empty
          else begin
            assert (next_start_nat < heap_size);
            MH.next_object_start_aligned start obj_size_words;
            assert (next_start_nat % U64.v mword == 0);
            let next_start : hp_addr = U64.uint_to_t next_start_nat in
            MH.objects_in_chunk_from c next_start
          end in
        Fields.mem_cons_lemma obj first tail;
        assert (Seq.mem obj tail);
        assert (next_start_nat < MH.chunk_end c);
        assert (next_start_nat < heap_size);
        MH.next_object_start_aligned start obj_size_words;
        assert (next_start_nat % U64.v mword == 0);
        let next_start : hp_addr = U64.uint_to_t next_start_nat in
        MA.object_member_header_at_or_after_start c next_start obj;
        assert (U64.v next_start <= U64.v hd);
        assert (U64.v start + U64.v mword <= U64.v next_start);
        assert (U64.v start + U64.v mword <= U64.v hd);
        assert (U64.v start + U64.v mword <= U64.v rem_hd);
        assert (U64.v start + U64.v mword <= U64.v rem_obj);
        MH.write_word_in_chunk_preserves_word c hd alloc_hdr start;
        MH.read_write_in_chunk_different c hd start alloc_hdr;
        MH.write_word_in_chunk_preserves_word c1 rem_hd rem_hdr start;
        MH.read_write_in_chunk_different c1 rem_hd start rem_hdr;
        MH.write_word_in_chunk_preserves_word c2 rem_obj next_fp start;
        MH.read_write_in_chunk_different c2 rem_obj start next_fp;
        assert (MH.read_word_in_chunk c3 start == header);
        assert (Obj.getWosize (MH.read_word_in_chunk c3 start) == wz);
        assert (U64.v start +
                (U64.v (Obj.getWosize
                  (MH.read_word_in_chunk c3 start)) + 1) *
                  U64.v mword == next_start_nat);
        assert (next_start_nat < MH.chunk_end c3);
        assert (next_start_nat < pow2 64);
        assert (U64.v start >= MH.chunk_start c3);
        assert (U64.v start + U64.v mword < MH.chunk_end c3);
        MH.objects_in_chunk_from_cons_step c3 start;
        let tail3 = MH.objects_in_chunk_from c3 next_start in
        Fields.mem_cons_lemma x first tail3;
        if x = first then
          MH.objects_in_chunk_from_head_mem c start
        else begin
          assert (Seq.mem x tail3);
          objects_in_chunk_from_head_split_member_origin
            c next_start obj x requested_wz block_wz next_fp
            rem_wz_u rem_hd rem_obj;
          if x == obj then ()
          else if x == rem_obj then ()
          else begin
            assert (Seq.mem x (MH.objects_in_chunk_from c next_start));
            MH.objects_in_chunk_from_tail_mem c start next_start x
          end
        end
      end
    end
  end
#pop-options

#push-options "--split_queries always --z3rlimit 5 --fuel 0 --ifuel 0"
private let old_major_objects_member_from_index
  (mh: MH.major_heap) (idx: nat) (x: obj_addr)
  : Lemma
      (requires
        idx < Seq.length mh /\
        Seq.mem x (MH.objects_in_chunk (Seq.index mh idx)))
      (ensures Seq.mem x (MH.major_objects mh))
  =
  MHMember.major_objects_member_at_index_small mh idx x
#pop-options

#push-options "--split_queries always --z3rlimit 20 --fuel 1 --ifuel 1"
private let head_split_old_nonblue_from_index
  (mh: MH.major_heap) (idx member_idx: nat) (obj src: obj_addr)
  (requested_wz block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        member_idx < Seq.length mh /\
        Seq.mem src (MH.objects_in_chunk (Seq.index mh member_idx)) /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        src <> obj /\
        requested_wz > 0 /\
        requested_wz < pow2 54 /\
        block_wz >= requested_wz /\
        block_wz < pow2 54 /\
        block_wz - requested_wz >= 2 /\
        U64.v rem_wz_u == block_wz - requested_wz - 1 /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        MH.object_wosize_in_chunk (Seq.index mh idx) obj == block_wz /\
        MH.word_in_chunk (Seq.index mh idx) rem_hd /\
        MH.word_in_chunk (Seq.index mh idx) rem_obj /\
        U64.v rem_hd ==
          U64.v (hd_address obj) + (1 + requested_wz) * U64.v mword /\
        U64.v rem_obj == U64.v rem_hd + U64.v mword /\
        (let hd = hd_address obj in
         let alloc_hdr =
           Alloc.make_header
             (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
         let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
         let rem_hdr =
           Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
         let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
         let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
         MH.read_word_in_major mh3 (hd_address src) == Some hdr /\
         Obj.getColor hdr <> Header.Blue))
      (ensures
        Seq.mem src (MH.major_objects mh) /\
        (exists (old_hdr:U64.t).
           MH.read_word_in_major mh (hd_address src) == Some old_hdr /\
           Obj.getColor old_hdr <> Header.Blue))
  =
  old_major_objects_member_from_index mh member_idx src;
  assert (Seq.mem src (MH.major_objects mh));
  let src_hd = hd_address src in
  MH.major_objects_member_header_read_some mh src;
  match MH.read_word_in_major mh src_hd with
  | None -> assert False
  | Some old_hdr ->
    selected_head_split_header_read_region
      mh idx obj src old_hdr requested_wz block_wz rem_hd rem_obj;
    let hd = hd_address obj in
    hd_address_injective src obj;
    assert (src_hd <> hd);
    MA.head_split_major_preserves_read_at
      mh idx obj src_hd old_hdr requested_wz block_wz next_fp
      rem_wz_u rem_hd rem_obj;
    let alloc_hdr =
      Alloc.make_header
        (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
    let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
    let rem_hdr =
      Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
    let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
    let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
    assert (MH.read_word_in_major mh3 src_hd == Some old_hdr);
    assert (old_hdr == hdr);
    FStar.Classical.exists_intro
      (fun old_hdr' ->
        MH.read_word_in_major mh (hd_address src) == Some old_hdr' /\
        Obj.getColor old_hdr' <> Header.Blue)
      old_hdr
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let head_split_nonblue_origin_aux
  (mh: MH.major_heap) (idx: nat) (obj src: obj_addr)
  (requested_wz block_wz: nat) (next_fp: U64.t)
  (rem_wz_u: U64.t{U64.v rem_wz_u < pow2 54})
  (rem_hd: hp_addr) (rem_obj: obj_addr) (hdr: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        requested_wz > 0 /\
        requested_wz < pow2 54 /\
        requested_wz < pow2 64 /\
        FStar.UInt.size requested_wz 64 /\
        block_wz >= requested_wz /\
        block_wz < pow2 54 /\
        block_wz - requested_wz >= 2 /\
        U64.v rem_wz_u == block_wz - requested_wz - 1 /\
        MH.word_in_chunk (Seq.index mh idx) (hd_address obj) /\
        Seq.mem obj (MH.objects_in_chunk (Seq.index mh idx)) /\
        MH.object_wosize_in_chunk (Seq.index mh idx) obj == block_wz /\
        MH.word_in_chunk (Seq.index mh idx) rem_hd /\
        MH.word_in_chunk (Seq.index mh idx) rem_obj /\
        U64.v rem_hd ==
          U64.v (hd_address obj) + (1 + requested_wz) * U64.v mword /\
        U64.v rem_obj == U64.v rem_hd + U64.v mword /\
        U64.v (hd_address obj) + (1 + block_wz) * U64.v mword <=
          MH.chunk_end (Seq.index mh idx) /\
        hd_address rem_obj == rem_hd /\
        (let hd = hd_address obj in
         let alloc_hdr =
           Alloc.make_header
             (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
         let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
         let rem_hdr =
           Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
         let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
         let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
         MH.well_formed_major_heap mh3 /\
         Seq.mem src (MH.major_objects mh3) /\
         MH.read_word_in_major mh3 (hd_address src) == Some hdr /\
         Obj.getColor hdr <> Header.Blue))
      (ensures
        src == obj \/
        (Seq.mem src (MH.major_objects mh) /\
         (exists (old_hdr:U64.t).
            MH.read_word_in_major mh (hd_address src) == Some old_hdr /\
            Obj.getColor old_hdr <> Header.Blue)))
  =
  let c = Seq.index mh idx in
  let hd = hd_address obj in
  let alloc_hdr =
    Alloc.make_header
      (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
  let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
  let rem_hdr =
    Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
  let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
  let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
  let c1 = MH.write_word_in_chunk c hd alloc_hdr in
  let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
  let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
  MA.head_split_materialize_writes
    mh idx obj requested_wz next_fp rem_wz_u rem_hd rem_obj;
  assert (Seq.index mh3 idx == c3);
  if src = obj then ()
  else begin
    if src = rem_obj then begin
      MH.lookup_chunk_index_word_in_chunk mh rem_hd idx;
      assert (MH.lookup_chunk_index mh rem_hd == Some idx);
      SplitShape.head_split_preserves_lookup_word
        mh idx idx obj rem_hd requested_wz next_fp rem_wz_u
        rem_hd rem_obj;
      MH.read_write_in_chunk_same c1 rem_hd rem_hdr;
      MH.write_word_in_chunk_preserves_range c1 rem_hd rem_hdr;
      MH.write_word_in_chunk_preserves_range c2 rem_obj next_fp;
      assert (U64.v rem_hd + U64.v mword <= U64.v rem_obj);
      MH.read_write_in_chunk_different c2 rem_obj rem_hd next_fp;
      assert (MH.read_word_in_chunk c3 rem_hd == rem_hdr);
      MH.read_word_in_major_at_lookup_index mh3 rem_hd idx;
      assert (MH.read_word_in_major mh3 (hd_address src) == Some rem_hdr);
      assert (hdr == rem_hdr);
      AllocCore.make_header_getColor rem_wz_u Alloc.blue_bits 0UL;
      Obj.getColor_raw rem_hdr;
      assert (Header.get_color (U64.v rem_hdr) == U64.v Alloc.blue_bits);
      assert (Obj.getColor rem_hdr == Header.Blue);
      assert False
    end else begin
      let src_hd = hd_address src in
      MH.read_word_in_major_lookup_index mh3 src_hd hdr;
      let src_idx = MH.lookup_chunk_index_value mh3 src_hd in
      assert (MH.lookup_chunk_index mh3 src_hd == Some src_idx);
      assert (src_idx < Seq.length mh3);
      assert (MH.word_in_chunk (Seq.index mh3 src_idx) src_hd);
      if src_idx = idx then begin
        assert (Seq.index mh3 src_idx == c3);
        assert (MH.word_in_chunk c3 src_hd);
        assert (MH.chunk_contains_addr c3 src_hd);
        assert (MH.chunk_contains_addr (Seq.index mh3 idx) src_hd);
        MH.major_objects_member_in_lookup_chunk mh3 idx src;
        assert (Seq.mem src (MH.objects_in_chunk c3));
        objects_in_chunk_from_head_split_member_origin
          c c.base obj src requested_wz block_wz next_fp
          rem_wz_u rem_hd rem_obj;
        assert (src <> obj);
        assert (src <> rem_obj);
        assert (Seq.mem src (MH.objects_in_chunk c));
        assert (idx < Seq.length mh);
        assert (Seq.index mh idx == c);
        assert (Seq.mem src (MH.objects_in_chunk (Seq.index mh idx)));
        assert (idx < Seq.length mh /\
                Seq.mem src (MH.objects_in_chunk (Seq.index mh idx)));
        head_split_old_nonblue_from_index
          mh idx idx obj src requested_wz block_wz next_fp
          rem_wz_u rem_hd rem_obj hdr
      end else begin
        assert (Seq.length mh3 == Seq.length mh);
        assert (src_idx < Seq.length mh);
        assert (Seq.index mh3 src_idx == Seq.index mh src_idx);
        assert (MH.chunk_contains_addr (Seq.index mh3 src_idx) src_hd);
        MH.major_objects_member_in_lookup_chunk mh3 src_idx src;
        assert (Seq.mem src (MH.objects_in_chunk (Seq.index mh src_idx)));
        assert (src_idx < Seq.length mh /\
                Seq.mem src (MH.objects_in_chunk (Seq.index mh src_idx)));
        head_split_old_nonblue_from_index
          mh idx src_idx obj src requested_wz block_wz next_fp
          rem_wz_u rem_hd rem_obj hdr
      end
    end
  end
#pop-options

#push-options "--split_queries always --z3rlimit 10 --fuel 0 --ifuel 0"
let major_alloc_head_split_remainder_header_blue
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        requested_wz > 0 /\
        MH.well_formed_major_heap mh /\
        MA.major_fl_valid mh fp fuel /\
        MA.major_fl_above_zero mh fp fuel /\
        MA.major_fl_blocks_fit mh fp fuel /\
        MA.major_fl_head_wosize mh fp >= requested_wz + 2)
      (ensures
        (let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
         r.major_obj_out == fp /\
         r.major_fp_out <> 0UL /\
         exists (rem_obj: obj_addr).
           r.major_fp_out == rem_obj /\
           (match MH.read_word_in_major
                    r.major_alloc_out (hd_address rem_obj) with
            | Some hdr -> Obj.getColor hdr == Header.Blue
            | None -> False)))
  =
  MA.major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  let obj : obj_addr = fp in
  let hd = hd_address obj in
  MA.major_fl_head_wosize_current mh fp fuel;
  MA.major_fl_head_block_fits_current mh fp fuel;
  MA.major_fl_valid_link_lookup_index mh fp fuel;
  let idx = MH.lookup_chunk_index_value mh hd in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) hd);
  match MH.read_word_in_major mh hd with
  | None -> assert False
  | Some hdr ->
    let block_wz = U64.v (Obj.getWosize hdr) in
    assert (MA.major_fl_head_wosize mh fp == block_wz);
    assert (block_wz < pow2 54);
    assert (block_wz >= requested_wz + 2);
    assert (block_wz - requested_wz >= 2);
    assert (requested_wz < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (FStar.UInt.size requested_wz 64);
    match MH.read_word_in_major mh obj with
    | None -> assert False
    | Some next_fp ->
      let c = Seq.index mh idx in
      MH.read_word_in_major_at_lookup_index mh hd idx;
      assert (MH.read_word_in_chunk c hd == hdr);
      MA.major_fl_valid_gives_mem mh fp fuel;
      assert (Seq.mem obj (MH.major_objects mh));
      MH.major_objects_member_in_lookup_chunk mh idx obj;
      assert (Seq.mem obj (MH.objects_in_chunk c));
      assert (MH.object_wosize_in_chunk c obj == block_wz);
      assert (U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c);
      assert (U64.v mword == 8);
      let rem_hd_nat = U64.v hd + (1 + requested_wz) * 8 in
      let rem_obj_nat = rem_hd_nat + U64.v mword in
      assert (requested_wz + 2 <= block_wz);
      split_remainder_obj_addr_arith (U64.v hd) requested_wz;
      assert (rem_obj_nat == U64.v hd + (requested_wz + 2) * 8);
      assert (rem_obj_nat + 8 == U64.v hd + (requested_wz + 3) * 8);
      assert (requested_wz + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.lemma_mult_le_right
        8 (requested_wz + 3) (1 + block_wz);
      assert (rem_obj_nat + 8 <= U64.v hd + (1 + block_wz) * 8);
      assert (rem_obj_nat + 8 <= MH.chunk_end c);
      assert (MH.chunk_end c <= heap_size);
      assert (rem_hd_nat < heap_size);
      assert (rem_obj_nat < heap_size);
      assert (heap_size < pow2 64);
      assert (rem_hd_nat < pow2 64);
      assert (rem_obj_nat < pow2 64);
      assert (rem_obj_nat >= U64.v mword);
      hd_address_spec obj;
      MA.aligned_plus_word_product (U64.v hd) (1 + requested_wz);
      assert (rem_hd_nat % U64.v mword == 0);
      MA.aligned_plus_word_product (U64.v hd) (requested_wz + 2);
      assert (rem_obj_nat % U64.v mword == 0);
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj : obj_addr = U64.uint_to_t rem_obj_nat in
      assert (MH.word_in_chunk c rem_hd);
      assert (MH.word_in_chunk c rem_obj);
      f_address_spec rem_hd;
      hd_f_roundtrip rem_hd;
      assert (f_address rem_hd == rem_obj);
      assert (hd_address rem_obj == rem_hd);
      let rem_wz = block_wz - requested_wz - 1 in
      assert (rem_wz < pow2 54);
      assert (FStar.UInt.size rem_wz 64);
      let rem_wz_u : x:U64.t{U64.v x < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == rem_wz);
      MA.major_alloc_head_split mh obj requested_wz fuel hdr next_fp
        rem_hd rem_obj;
      let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
      assert (r.major_fp_out == rem_obj);
      assert (r.major_obj_out == fp);
      let alloc_hdr =
        Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
      let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
      let rem_hdr =
        Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
      let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
      let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
      assert (r.major_alloc_out == mh3);
      MA.head_split_materialize_writes
        mh idx obj requested_wz next_fp rem_wz_u rem_hd rem_obj;
      MH.lookup_chunk_index_word_in_chunk mh rem_hd idx;
      assert (MH.lookup_chunk_index mh rem_hd == Some idx);
      SplitShape.head_split_preserves_lookup_word
        mh idx idx obj rem_hd requested_wz next_fp rem_wz_u rem_hd rem_obj;
      assert (MH.lookup_chunk_index mh3 rem_hd == Some idx);
      assert (Seq.index mh3 idx ==
        MH.write_word_in_chunk
          (MH.write_word_in_chunk
            (MH.write_word_in_chunk (Seq.index mh idx) hd alloc_hdr)
            rem_hd rem_hdr)
          rem_obj next_fp);
      let c1 = MH.write_word_in_chunk (Seq.index mh idx) hd alloc_hdr in
      let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
      let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
      MH.read_write_in_chunk_same c1 rem_hd rem_hdr;
      MH.write_word_in_chunk_preserves_range
        c1 rem_hd rem_hdr;
      MH.write_word_in_chunk_preserves_range
        c2 rem_obj next_fp;
      assert (U64.v rem_hd + U64.v mword <= U64.v rem_obj);
      MH.read_write_in_chunk_different c2 rem_obj rem_hd next_fp;
      assert (MH.read_word_in_chunk c3 rem_hd == rem_hdr);
      MH.read_word_in_major_at_lookup_index mh3 rem_hd idx;
      assert (MH.read_word_in_major mh3 rem_hd == Some rem_hdr);
      AllocCore.make_header_getColor rem_wz_u Alloc.blue_bits 0UL;
      Obj.getColor_raw rem_hdr;
      assert (Header.get_color (U64.v rem_hdr) == U64.v Alloc.blue_bits);
      assert (Obj.getColor rem_hdr == Header.Blue);
      assert (r.major_alloc_out == mh3);
      assert (hd_address rem_obj == rem_hd);
      FStar.Classical.exists_intro
        (fun rem_obj' ->
          r.major_fp_out == rem_obj' /\
          (match MH.read_word_in_major
                   r.major_alloc_out (hd_address rem_obj') with
           | Some hdr -> Obj.getColor hdr == Header.Blue
           | None -> False))
        rem_obj
#pop-options

#push-options "--split_queries always --z3rlimit 20 --fuel 1 --ifuel 1"
let major_alloc_head_split_nonblue_origin
  (mh: MH.major_heap) (fp: U64.t)
  (requested_wz fuel: nat)
  : Lemma
      (requires
        fuel > 1 /\
        fp <> 0UL /\
        requested_wz > 0 /\
        MH.well_formed_major_heap mh /\
        MA.major_fl_valid mh fp fuel /\
        MA.major_fl_above_zero mh fp fuel /\
        MA.major_fl_blocks_fit mh fp fuel /\
        MA.major_fl_head_wosize mh fp >= requested_wz + 2)
      (ensures
        (let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
         forall (src:obj_addr). forall (hdr:U64.t).
           Seq.mem src (MH.major_objects r.major_alloc_out) /\
           MH.read_word_in_major r.major_alloc_out (hd_address src) ==
             Some hdr /\
           Obj.getColor hdr <> Header.Blue ==>
           src == fp \/
           (Seq.mem src (MH.major_objects mh) /\
            (exists (old_hdr:U64.t).
               MH.read_word_in_major mh (hd_address src) == Some old_hdr /\
               Obj.getColor old_hdr <> Header.Blue))))
  =
  MA.major_fl_above_zero_current mh fp fuel;
  assert (U64.v fp >= U64.v zero_addr + U64.v mword);
  let obj : obj_addr = fp in
  let hd = hd_address obj in
  MA.major_fl_head_wosize_current mh fp fuel;
  MA.major_fl_head_block_fits_current mh fp fuel;
  MA.major_fl_valid_link_lookup_index mh fp fuel;
  let idx = MH.lookup_chunk_index_value mh hd in
  assert (MH.lookup_chunk_index mh hd == Some idx);
  assert (idx < Seq.length mh);
  assert (MH.word_in_chunk (Seq.index mh idx) hd);
  match MH.read_word_in_major mh hd with
  | None -> assert False
  | Some old_head_hdr ->
    let block_wz = U64.v (Obj.getWosize old_head_hdr) in
    assert (MA.major_fl_head_wosize mh fp == block_wz);
    assert (block_wz < pow2 54);
    assert (block_wz >= requested_wz + 2);
    assert (block_wz - requested_wz >= 2);
    assert (requested_wz < pow2 54);
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    assert (requested_wz < pow2 64);
    assert (FStar.UInt.size requested_wz 64);
    match MH.read_word_in_major mh obj with
    | None -> assert False
    | Some next_fp ->
      let c = Seq.index mh idx in
      MH.read_word_in_major_at_lookup_index mh hd idx;
      assert (MH.read_word_in_chunk c hd == old_head_hdr);
      MA.major_fl_valid_gives_mem mh fp fuel;
      assert (Seq.mem obj (MH.major_objects mh));
      MH.major_objects_member_in_lookup_chunk mh idx obj;
      assert (Seq.mem obj (MH.objects_in_chunk c));
      assert (MH.object_wosize_in_chunk c obj == block_wz);
      assert (U64.v hd + (1 + block_wz) * U64.v mword <= MH.chunk_end c);
      assert (U64.v mword == 8);
      let rem_hd_nat = U64.v hd + (1 + requested_wz) * 8 in
      let rem_obj_nat = rem_hd_nat + U64.v mword in
      assert (requested_wz + 2 <= block_wz);
      split_remainder_obj_addr_arith (U64.v hd) requested_wz;
      assert (rem_obj_nat == U64.v hd + (requested_wz + 2) * 8);
      assert (rem_obj_nat + 8 == U64.v hd + (requested_wz + 3) * 8);
      assert (requested_wz + 3 <= 1 + block_wz);
      FStar.Math.Lemmas.lemma_mult_le_right
        8 (requested_wz + 3) (1 + block_wz);
      assert (rem_obj_nat + 8 <= U64.v hd + (1 + block_wz) * 8);
      assert (rem_obj_nat + 8 <= MH.chunk_end c);
      assert (MH.chunk_end c <= heap_size);
      assert (rem_hd_nat < heap_size);
      assert (rem_obj_nat < heap_size);
      assert (heap_size < pow2 64);
      assert (rem_hd_nat < pow2 64);
      assert (rem_obj_nat < pow2 64);
      assert (rem_obj_nat >= U64.v mword);
      hd_address_spec obj;
      MA.aligned_plus_word_product (U64.v hd) (1 + requested_wz);
      assert (rem_hd_nat % U64.v mword == 0);
      MA.aligned_plus_word_product (U64.v hd) (requested_wz + 2);
      assert (rem_obj_nat % U64.v mword == 0);
      let rem_hd : hp_addr = U64.uint_to_t rem_hd_nat in
      let rem_obj : obj_addr = U64.uint_to_t rem_obj_nat in
      assert (MH.word_in_chunk c rem_hd);
      assert (MH.word_in_chunk c rem_obj);
      f_address_spec rem_hd;
      hd_f_roundtrip rem_hd;
      assert (f_address rem_hd == rem_obj);
      assert (hd_address rem_obj == rem_hd);
      let rem_wz = block_wz - requested_wz - 1 in
      assert (rem_wz < pow2 54);
      assert (FStar.UInt.size rem_wz 64);
      let rem_wz_u : x:U64.t{U64.v x < pow2 54} =
        U64.uint_to_t rem_wz in
      assert (U64.v rem_wz_u == rem_wz);
      let alloc_hdr =
        Alloc.make_header (U64.uint_to_t requested_wz) Alloc.white_bits 0UL in
      let rem_hdr =
        Alloc.make_header rem_wz_u Alloc.blue_bits 0UL in
      let mh1 = MA.major_write_word_or_same mh hd alloc_hdr in
      let mh2 = MA.major_write_word_or_same mh1 rem_hd rem_hdr in
      let mh3 = MA.major_write_word_or_same mh2 rem_obj next_fp in
      MA.major_alloc_head_split mh obj requested_wz fuel old_head_hdr next_fp
        rem_hd rem_obj;
      let r = MA.major_alloc_spec_with_fuel mh fp requested_wz fuel in
      assert (r.major_obj_out == fp);
      assert (r.major_fp_out == rem_obj);
      assert (r.major_alloc_out == mh3);
      SplitShape.major_alloc_head_split_preserves_alloc_shape
        mh fp requested_wz fuel;
      assert (MH.well_formed_major_heap r.major_alloc_out);
      assert (MH.well_formed_major_heap mh3);
      MA.head_split_materialize_writes
        mh idx obj requested_wz next_fp rem_wz_u rem_hd rem_obj;
      assert (Seq.index mh3 idx ==
        MH.write_word_in_chunk
          (MH.write_word_in_chunk
            (MH.write_word_in_chunk (Seq.index mh idx) hd alloc_hdr)
            rem_hd rem_hdr)
          rem_obj next_fp);
      let c1 = MH.write_word_in_chunk c hd alloc_hdr in
      let c2 = MH.write_word_in_chunk c1 rem_hd rem_hdr in
      let c3 = MH.write_word_in_chunk c2 rem_obj next_fp in
      AllocCore.make_header_getColor rem_wz_u Alloc.blue_bits 0UL;
      Obj.getColor_raw rem_hdr;
      assert (Header.get_color (U64.v rem_hdr) == U64.v Alloc.blue_bits);
      assert (Obj.getColor rem_hdr == Header.Blue);
      assert (obj == fp);
      let aux (src: obj_addr) (hdr: U64.t)
        : Lemma
            (requires
              Seq.mem src (MH.major_objects r.major_alloc_out) /\
              MH.read_word_in_major r.major_alloc_out (hd_address src) ==
                Some hdr /\
              Obj.getColor hdr <> Header.Blue)
            (ensures
              src == fp \/
              (Seq.mem src (MH.major_objects mh) /\
               (exists (old_hdr:U64.t).
                  MH.read_word_in_major mh (hd_address src) ==
                    Some old_hdr /\
                  Obj.getColor old_hdr <> Header.Blue)))
        =
        head_split_nonblue_origin_aux
          mh idx obj src requested_wz block_wz next_fp
          rem_wz_u rem_hd rem_obj hdr
      in
      FStar.Classical.forall_intro_2
        (FStar.Classical.move_requires_2 aux)
#pop-options
