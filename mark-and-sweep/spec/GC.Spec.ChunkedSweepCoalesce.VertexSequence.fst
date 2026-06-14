module GC.Spec.ChunkedSweepCoalesce.VertexSequence

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SeqProps = FStar.Seq.Properties

open GC.Spec.Base
open GC.Spec.Heap

module MH = GC.Spec.MajorHeap
module Obj = GC.Spec.Object
module Defs = GC.Spec.ChunkedSweepCoalesce.Defs
module Pending = GC.Spec.ChunkedSweepCoalesce.PendingRun
module Vertex = GC.Spec.ChunkedSweepCoalesce.VertexPreservation
module Reach = GC.Spec.ChunkedSweepCoalesce.VertexReach
module ReachPrefix = GC.Spec.ChunkedSweepCoalesce.VertexReachPrefix
module VS = GC.Spec.ChunkedSweepCoalesce.VertexSteps

#set-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always --warn_error -321"

let nat_nonzero_pos (n: nat)
  : Lemma (requires n <> 0) (ensures n > 0)
  = ()

let hp_addr_of_aligned_nat
    (n: nat)
  : Pure hp_addr
      (requires n < heap_size /\ n < pow2 64 /\ n % U64.v mword == 0)
      (ensures fun a -> U64.v a == n)
  = U64.uint_to_t n

let word_in_chunk_same_range
    (c c': MH.heap_chunk)
    (addr: hp_addr)
  : Lemma
      (requires
        MH.chunk_start c' == MH.chunk_start c /\
        MH.chunk_end c' == MH.chunk_end c /\
        MH.word_in_chunk c addr)
      (ensures MH.word_in_chunk c' addr)
  = ()

let same_wosize_as_original
    (old_c mid_c new_c: MH.heap_chunk)
    (protected: obj_addr)
  : Lemma
      (requires
        MH.object_wosize_in_chunk mid_c protected ==
          MH.object_wosize_in_chunk old_c protected /\
        MH.object_wosize_in_chunk new_c protected ==
          MH.object_wosize_in_chunk mid_c protected)
      (ensures
        MH.object_wosize_in_chunk new_c protected ==
          MH.object_wosize_in_chunk old_c protected)
  = ()

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let pending_run_flush_pre
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires Pending.pending_run_before_start
        work idx base start first_blue run_words)
      (ensures
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           idx < Seq.length work /\
           MH.word_in_chunk (Seq.index work idx) hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index work idx) /\
           U64.v hd + run_words * U64.v mword <= U64.v start)))
  =
  if run_words = 0 then ()
  else begin
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    Pending.pending_run_before_start_nonempty_elim
      work idx base start first_blue rw;
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    hd_address_spec fb;
    assert (U64.v hd + U64.v mword == U64.v fb);
    assert (rw == run_words);
    assert (run_words == (run_words - 1) + 1);
    FStar.Math.Lemmas.distributivity_add_left
      (run_words - 1) 1 (U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v hd) (U64.v mword) ((run_words - 1) * U64.v mword);
    assert (U64.v hd + run_words * U64.v mword ==
            U64.v fb + (run_words - 1) * U64.v mword);
    assert (U64.v hd + run_words * U64.v mword == U64.v start)
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let nonblack_extended_run_flush_pre
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires
        Pending.pending_run_before_start
          work idx base start first_blue run_words /\
        idx < Seq.length work /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v start + (U64.v wz + 1) * U64.v mword <=
          MH.chunk_end (Seq.index work idx))
      (ensures
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + U64.v wz + 1 in
         (new_run <> 0 /\
          ~(U64.v new_first < U64.v mword) /\
          ~(U64.v new_first >= heap_size) /\
          ~(U64.v new_first % U64.v mword <> 0) /\
          new_run - 1 < pow2 54 ==>
           (let fb : obj_addr = new_first in
            let hd = hd_address fb in
            idx < Seq.length work /\
            MH.word_in_chunk (Seq.index work idx) hd /\
            U64.v hd + new_run * U64.v mword <=
              MH.chunk_end (Seq.index work idx)))))
  =
  let new_first : U64.t = if run_words = 0 then first else first_blue in
  let new_run = run_words + U64.v wz + 1 in
  if run_words = 0 then begin
    assert (new_first == first);
    assert (new_run == U64.v wz + 1);
    assert (hd_address new_first == start);
    assert (MH.word_in_chunk (Seq.index work idx) (hd_address new_first));
    assert (U64.v (hd_address new_first) + new_run * U64.v mword ==
            U64.v start + (U64.v wz + 1) * U64.v mword)
  end else begin
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    Pending.pending_run_before_start_nonempty_elim
      work idx base start first_blue rw;
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    hd_address_spec fb;
    assert (U64.v hd + U64.v mword == U64.v fb);
    assert (new_first == first_blue);
    assert (new_run == run_words + U64.v wz + 1);
    assert (run_words + U64.v wz + 1 == (run_words - 1) + (U64.v wz + 2));
    FStar.Math.Lemmas.distributivity_add_left
      (run_words - 1) (U64.v wz + 2) (U64.v mword);
    FStar.Math.Lemmas.distributivity_add_left
      (U64.v wz + 1) 1 (U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v hd) (U64.v mword)
      (((run_words - 1) + (U64.v wz + 1)) * U64.v mword);
    FStar.Math.Lemmas.distributivity_add_left
      (run_words - 1) (U64.v wz + 1) (U64.v mword);
    FStar.Math.Lemmas.paren_add_right
      (U64.v fb) ((run_words - 1) * U64.v mword)
      ((U64.v wz + 1) * U64.v mword);
    assert (U64.v fb + (run_words - 1) * U64.v mword == U64.v start);
    assert (U64.v hd + new_run * U64.v mword ==
            U64.v start + (U64.v wz + 1) * U64.v mword)
  end
#pop-options

let seq_tail_mem (#a:eqtype) (s: Seq.seq a) (x: a)
  : Lemma
      (requires Seq.length s > 0 /\ Seq.mem x (Seq.tail s))
      (ensures Seq.mem x s)
  =
  let hd = Seq.head s in
  let tl = Seq.tail s in
  assert (s == Seq.cons hd tl);
  SeqProps.lemma_mem_append (Seq.create 1 hd) tl

let seq_mem_eq (#a:eqtype) (s t: Seq.seq a) (x: a)
  : Lemma
      (requires s == t /\ Seq.mem x s)
      (ensures Seq.mem x t)
  =
  assert (Seq.equal s t);
  Seq.lemma_eq_elim s t

let other_chunk_post
    (work final: MH.major_heap)
    (target_idx: nat)
    (target_start: hp_addr)
    (protected: obj_addr)
  =
  target_idx < Seq.length work /\
  MH.well_formed_major_heap final /\
  target_idx < Seq.length final /\
  MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
    MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
  Seq.mem protected
    (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
  MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
    MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
  MH.chunk_start (Seq.index final target_idx) ==
    MH.chunk_start (Seq.index work target_idx) /\
  MH.chunk_end (Seq.index final target_idx) ==
    MH.chunk_end (Seq.index work target_idx)

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let other_chunk_post_intro
    (work final: MH.major_heap)
    (target_idx: nat)
    (target_start: hp_addr)
    (protected: obj_addr)
  : Lemma
      (requires
        target_idx < Seq.length work /\
        MH.well_formed_major_heap final /\
        target_idx < Seq.length final /\
        MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
          MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
        MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
        MH.chunk_start (Seq.index final target_idx) ==
          MH.chunk_start (Seq.index work target_idx) /\
        MH.chunk_end (Seq.index final target_idx) ==
          MH.chunk_end (Seq.index work target_idx))
      (ensures other_chunk_post work final target_idx target_start protected)
  = ()
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let other_chunk_post_elim
    (work final: MH.major_heap)
    (target_idx: nat)
    (target_start: hp_addr)
    (protected: obj_addr)
  : Lemma
      (requires other_chunk_post work final target_idx target_start protected)
      (ensures
        target_idx < Seq.length work /\
        MH.well_formed_major_heap final /\
        target_idx < Seq.length final /\
        MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
          MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
        MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
        MH.chunk_start (Seq.index final target_idx) ==
          MH.chunk_start (Seq.index work target_idx) /\
        MH.chunk_end (Seq.index final target_idx) ==
          MH.chunk_end (Seq.index work target_idx))
  = ()
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let other_chunk_post_compose
    (work mid final: MH.major_heap)
    (target_idx: nat)
    (target_start: hp_addr)
    (protected: obj_addr)
  : Lemma
      (requires
        other_chunk_post work mid target_idx target_start protected /\
        other_chunk_post mid final target_idx target_start protected)
      (ensures
        other_chunk_post work final target_idx target_start protected)
  =
  same_wosize_as_original
    (Seq.index work target_idx)
    (Seq.index mid target_idx)
    (Seq.index final target_idx)
    protected
#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 0 --split_queries always"
let other_chunk_black_head_finish
    (source work: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (target_idx: nat)
    (target_start: hp_addr)
    (protected: obj_addr)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        Defs.chunked_is_black source (Seq.head objs) /\
        (let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
         let work' = fst flushed in
         let fp' = snd flushed in
         let work'' = Defs.chunked_make_white work' (Seq.head objs) in
         let tail_final =
           fst (Defs.chunked_fused_aux
             source work'' (Seq.tail objs) 0UL 0 fp') in
         other_chunk_post work work'' target_idx target_start protected /\
         other_chunk_post work'' tail_final target_idx target_start protected))
      (ensures
        other_chunk_post work
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          target_idx target_start protected)
  =
  let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
  let work' = fst flushed in
  let fp' = snd flushed in
  let work'' = Defs.chunked_make_white work' (Seq.head objs) in
  let tail_final =
    fst (Defs.chunked_fused_aux
      source work'' (Seq.tail objs) 0UL 0 fp') in
  other_chunk_post_compose
    work work'' tail_final target_idx target_start protected;
  Defs.chunked_fused_aux_black_step
    source work objs first_blue run_words fp;
  assert (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp) == tail_final)

let other_chunk_nonblack_head_finish
    (source work: MH.major_heap)
    (objs: Seq.seq obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
    (target_idx: nat)
    (target_start: hp_addr)
    (protected: obj_addr)
  : Lemma
      (requires
        Seq.length objs > 0 /\
        ~(Defs.chunked_is_black source (Seq.head objs)) /\
        (let obj = Seq.head objs in
         let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
         let new_first : U64.t = if run_words = 0 then obj else first_blue in
         let tail_final =
           fst (Defs.chunked_fused_aux
             source work (Seq.tail objs) new_first (run_words + ws + 1) fp) in
         other_chunk_post work tail_final target_idx target_start protected))
      (ensures
        other_chunk_post work
          (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp))
          target_idx target_start protected)
  =
  let obj = Seq.head objs in
  let ws = U64.v (Defs.chunked_wosize_of_object source obj) in
  let new_first : U64.t = if run_words = 0 then obj else first_blue in
  let new_run = run_words + ws + 1 in
  let tail_final =
    fst (Defs.chunked_fused_aux
      source work (Seq.tail objs) new_first new_run fp) in
  Defs.chunked_fused_aux_nonblack_step
    source work objs first_blue run_words fp;
  assert (fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp) == tail_final)
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let next_object_start_nat_gt
    (start: hp_addr)
    (wz: Obj.wosize)
  : Lemma
      (ensures
        U64.v start <
        U64.v start + (U64.v wz + 1) * U64.v mword)
  =
  assert (U64.v mword == 8);
  assert (U64.v wz + 1 > 0);
  assert ((U64.v wz + 1) * U64.v mword > 0)

let next_object_start_after_header
    (start: hp_addr)
    (wz: Obj.wosize)
  : Lemma
      (ensures
        U64.v start + U64.v mword <=
        U64.v start + (U64.v wz + 1) * U64.v mword)
  =
  assert (U64.v mword == 8);
  assert (U64.v wz + 1 >= 1);
  assert ((U64.v wz + 1) * U64.v mword >= U64.v mword)

let terminal_next_start_at_chunk_end
    (c: MH.heap_chunk)
    (start: hp_addr)
    (wz: Obj.wosize)
    (next_start_nat: nat)
  : Lemma
      (requires
        next_start_nat ==
          U64.v start + (U64.v wz + 1) * U64.v mword /\
        next_start_nat <= MH.chunk_end c /\
        next_start_nat >= MH.chunk_end c)
      (ensures
        next_start_nat == MH.chunk_end c /\
        U64.v start + (U64.v wz + 1) * U64.v mword <= MH.chunk_end c)
  = ()

let chunk_tail_measure_decreases
    (c: MH.heap_chunk)
    (start next_start: hp_addr)
  : Lemma
      (requires
        U64.v start < U64.v next_start /\
        U64.v next_start <= MH.chunk_end c)
      (ensures
        MH.chunk_end c - U64.v next_start <
        MH.chunk_end c - U64.v start)
  = ()

let objects_in_chunk_from_cons_facts
    (c: MH.heap_chunk)
    (start: hp_addr)
    (objs: Seq.seq obj_addr)
  : Lemma
      (requires
        objs == MH.objects_in_chunk_from c start /\
        U64.v start >= MH.chunk_start c /\
        U64.v start + U64.v mword < MH.chunk_end c /\
        (let header = MH.read_word_in_chunk c start in
         let wz = Obj.getWosize header in
         let obj_size_words = U64.v wz + 1 in
         let next_start_nat =
           U64.v start + obj_size_words * U64.v mword in
         next_start_nat <= MH.chunk_end c /\
         next_start_nat < pow2 64 /\
         (next_start_nat < MH.chunk_end c ==>
          next_start_nat % U64.v mword == 0)))
      (ensures
        (let header = MH.read_word_in_chunk c start in
         let wz = Obj.getWosize header in
         let obj_size_words = U64.v wz + 1 in
         let next_start_nat =
           U64.v start + obj_size_words * U64.v mword in
         let tail =
           if next_start_nat >= MH.chunk_end c then Seq.empty
           else MH.objects_in_chunk_from c (U64.uint_to_t next_start_nat) in
         Seq.length objs > 0 /\
         Seq.head objs == f_address start /\
         Seq.tail objs == tail))
  =
  MH.objects_in_chunk_from_cons_step c start;
  let header = MH.read_word_in_chunk c start in
  let wz = Obj.getWosize header in
  let obj_size_words = U64.v wz + 1 in
  let next_start_nat =
    U64.v start + obj_size_words * U64.v mword in
  let tail =
    if next_start_nat >= MH.chunk_end c then Seq.empty
    else MH.objects_in_chunk_from c (U64.uint_to_t next_start_nat) in
  assert (Seq.tail (MH.objects_in_chunk_from c start) == tail);
  assert (Seq.equal objs (MH.objects_in_chunk_from c start));
  Seq.lemma_eq_elim objs (MH.objects_in_chunk_from c start)
#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1 --split_queries always"
let objects_in_chunk_from_nonempty_bounds
    (c: MH.heap_chunk)
    (start: hp_addr)
  : Lemma
      (requires Seq.length (MH.objects_in_chunk_from c start) > 0)
      (ensures
        U64.v start >= MH.chunk_start c /\
        U64.v start + U64.v mword < MH.chunk_end c /\
        (let header = MH.read_word_in_chunk c start in
         let wz = Obj.getWosize header in
         let obj_size_words = U64.v wz + 1 in
         let next_start_nat =
           U64.v start + obj_size_words * U64.v mword in
         next_start_nat <= MH.chunk_end c /\
         next_start_nat < pow2 64 /\
         (next_start_nat < MH.chunk_end c ==>
          next_start_nat % U64.v mword == 0)))
  =
  if U64.v start < MH.chunk_start c then begin
    assert (MH.objects_in_chunk_from c start == Seq.empty);
    assert False
  end else if U64.v start + U64.v mword >= MH.chunk_end c then begin
    assert (MH.objects_in_chunk_from c start == Seq.empty);
    assert False
  end else begin
    let header = MH.read_word_in_chunk c start in
    let wz = Obj.getWosize header in
    let obj_size_words = U64.v wz + 1 in
    let next_start_nat =
      U64.v start + obj_size_words * U64.v mword in
    if next_start_nat > MH.chunk_end c || next_start_nat >= pow2 64 then begin
      assert (MH.objects_in_chunk_from c start == Seq.empty);
      assert False
    end else if next_start_nat < MH.chunk_end c then begin
      MH.next_object_start_aligned start obj_size_words;
      assert (next_start_nat % U64.v mword == 0)
    end
  end
#pop-options

let pending_run_light
    (work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  =
  idx < Seq.length work /\
  (run_words <> 0 /\
   ~(U64.v first_blue < U64.v mword) /\
   ~(U64.v first_blue >= heap_size) /\
   ~(U64.v first_blue % U64.v mword <> 0) /\
   run_words - 1 < pow2 54 ==>
    (let fb : obj_addr = first_blue in
     let hd = hd_address fb in
     MH.word_in_chunk (Seq.index work idx) hd /\
     U64.v hd + run_words * U64.v mword <=
       MH.chunk_end (Seq.index work idx) /\
     U64.v hd + run_words * U64.v mword <= U64.v start))

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let pending_run_light_intro
    (work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires
        idx < Seq.length work /\
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           MH.word_in_chunk (Seq.index work idx) hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index work idx) /\
           U64.v hd + run_words * U64.v mword <= U64.v start)))
      (ensures pending_run_light work idx start first_blue run_words)
  = ()

let pending_run_light_from_pending
    (work: MH.major_heap)
    (idx: nat)
    (base start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires
        Pending.pending_run_before_start
          work idx base start first_blue run_words)
      (ensures pending_run_light work idx start first_blue run_words)
  =
  Pending.pending_run_before_start_index
    work idx base start first_blue run_words;
  pending_run_flush_pre work idx base start first_blue run_words

let pending_run_light_empty
    (work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
  : Lemma
      (requires idx < Seq.length work)
      (ensures pending_run_light work idx start 0UL 0)
  = ()

let pending_run_light_flush_pre
    (work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires pending_run_light work idx start first_blue run_words)
      (ensures
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           idx < Seq.length work /\
           MH.word_in_chunk (Seq.index work idx) hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index work idx) /\
           U64.v hd + run_words * U64.v mword <= U64.v start)))
  = ()

let pending_run_light_flush_in_chunk_pre
    (work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires pending_run_light work idx start first_blue run_words)
      (ensures
        (run_words <> 0 /\
         ~(U64.v first_blue < U64.v mword) /\
         ~(U64.v first_blue >= heap_size) /\
         ~(U64.v first_blue % U64.v mword <> 0) /\
         run_words - 1 < pow2 54 ==>
          (let fb : obj_addr = first_blue in
           let hd = hd_address fb in
           idx < Seq.length work /\
           MH.word_in_chunk (Seq.index work idx) hd /\
           U64.v hd + run_words * U64.v mword <=
             MH.chunk_end (Seq.index work idx))))
  = ()
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let flush_pending_light_other_chunk_post
    (work: MH.major_heap)
    (proc_idx target_idx: nat)
    (proc_start target_start: hp_addr)
    (protected: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        proc_idx < Seq.length work /\
        target_idx < Seq.length work /\
        proc_idx <> target_idx /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        pending_run_light work proc_idx proc_start first_blue run_words)
      (ensures
        (let work' = fst (Defs.chunked_flush_blue work first_blue run_words fp) in
         other_chunk_post work work' target_idx target_start protected))
  =
  pending_run_light_flush_in_chunk_pre
    work proc_idx proc_start first_blue run_words;
  if run_words <> 0 /\
     ~(U64.v first_blue < U64.v mword) /\
     ~(U64.v first_blue >= heap_size) /\
     ~(U64.v first_blue % U64.v mword <> 0) /\
     run_words - 1 < pow2 54
  then begin
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    assert (proc_idx < Seq.length work);
    assert (MH.word_in_chunk (Seq.index work proc_idx) hd);
    assert (U64.v hd + run_words * U64.v mword <=
            MH.chunk_end (Seq.index work proc_idx))
  end;
  Vertex.chunked_flush_blue_other_chunk_preserves_objects_from
    work proc_idx target_idx target_start protected
    first_blue run_words fp;
  other_chunk_post_intro
    work (fst (Defs.chunked_flush_blue work first_blue run_words fp))
    target_idx target_start protected
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let chunked_flush_blue_before_preserves_objects_from_light
    (mh: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap mh /\
        idx < Seq.length mh /\
        U64.v start <= MH.chunk_end (Seq.index mh idx) /\
        pending_run_light mh idx start first_blue run_words)
      (ensures
        (let final = fst (Defs.chunked_flush_blue mh first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final idx) start ==
           MH.objects_in_chunk_from (Seq.index mh idx) start /\
         MH.chunk_start (Seq.index final idx) ==
           MH.chunk_start (Seq.index mh idx) /\
         MH.chunk_end (Seq.index final idx) ==
           MH.chunk_end (Seq.index mh idx)))
  =
  if run_words = 0 then begin
    Defs.chunked_flush_blue_empty mh first_blue fp;
    assert (fst (Defs.chunked_flush_blue mh first_blue run_words fp) == mh)
  end else begin
    nat_nonzero_pos run_words;
    let rw : pos = run_words in
    if U64.v first_blue < U64.v mword \/
       U64.v first_blue >= heap_size \/
       U64.v first_blue % U64.v mword <> 0
    then begin
      Defs.chunked_flush_blue_invalid mh first_blue rw fp;
      assert (fst (Defs.chunked_flush_blue mh first_blue run_words fp) == mh)
    end else if run_words - 1 >= pow2 54 then begin
      Defs.chunked_flush_blue_too_large mh first_blue rw fp;
      assert (fst (Defs.chunked_flush_blue mh first_blue run_words fp) == mh)
    end else begin
      assert (run_words - 1 < pow2 54);
      FStar.Math.Lemmas.pow2_lt_compat 64 54;
      assert (run_words - 1 < pow2 64);
      pending_run_light_flush_pre mh idx start first_blue run_words;
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      assert (MH.word_in_chunk (Seq.index mh idx) hd);
      assert (U64.v hd + run_words * U64.v mword <= U64.v start);
      ReachPrefix.chunked_flush_blue_before_preserves_objects_from
        mh idx start first_blue run_words fp
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let pending_run_light_extend_nonblack_empty
    (work: MH.major_heap)
    (idx: nat)
    (start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
  : Lemma
      (requires
        idx < Seq.length work /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v next_start ==
          U64.v start + (U64.v wz + 1) * U64.v mword /\
        U64.v next_start <= MH.chunk_end (Seq.index work idx))
      (ensures
        pending_run_light work idx next_start first (U64.v wz + 1))
  =
  let new_run = U64.v wz + 1 in
  assert (new_run <> 0);
  assert (hd_address first == start);
  assert (MH.word_in_chunk (Seq.index work idx) (hd_address first));
  assert (U64.v (hd_address first) + new_run * U64.v mword ==
          U64.v next_start);
  if ~(U64.v first < U64.v mword) /\
     ~(U64.v first >= heap_size) /\
     ~(U64.v first % U64.v mword <> 0) /\
     new_run - 1 < pow2 54
  then begin
    assert (U64.v (hd_address first) + new_run * U64.v mword <=
            MH.chunk_end (Seq.index work idx));
    assert (U64.v (hd_address first) + new_run * U64.v mword <=
            U64.v next_start)
  end;
  pending_run_light_intro work idx next_start first new_run

let pending_run_light_extend_nonblack_nonempty
    (work: MH.major_heap)
    (idx: nat)
    (start next_start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
    (first_blue: U64.t)
    (run_words: pos)
  : Lemma
      (requires
        pending_run_light work idx start first_blue run_words /\
        idx < Seq.length work /\
        U64.v next_start ==
          U64.v start + (U64.v wz + 1) * U64.v mword /\
        U64.v next_start <= MH.chunk_end (Seq.index work idx))
      (ensures
        pending_run_light
          work idx next_start first_blue
          (run_words + U64.v wz + 1))
  =
  let new_run = run_words + U64.v wz + 1 in
  assert (new_run <> 0);
  if ~(U64.v first_blue < U64.v mword) /\
     ~(U64.v first_blue >= heap_size) /\
     ~(U64.v first_blue % U64.v mword <> 0) /\
     new_run - 1 < pow2 54
  then begin
    let fb : obj_addr = first_blue in
    let hd = hd_address fb in
    assert (run_words - 1 <= new_run - 1);
    assert (run_words - 1 < pow2 54);
    pending_run_light_flush_pre work idx start first_blue run_words;
    assert (MH.word_in_chunk (Seq.index work idx) hd);
    assert (U64.v hd + run_words * U64.v mword <= U64.v start);
    assert (U64.v hd + run_words * U64.v mword <=
            MH.chunk_end (Seq.index work idx));
    assert (new_run == run_words + (U64.v wz + 1));
    FStar.Math.Lemmas.distributivity_add_left
      run_words (U64.v wz + 1) (U64.v mword);
    assert (U64.v hd + new_run * U64.v mword ==
            U64.v hd + run_words * U64.v mword +
            (U64.v wz + 1) * U64.v mword);
    assert (U64.v hd + new_run * U64.v mword <=
            U64.v start + (U64.v wz + 1) * U64.v mword);
    assert (U64.v hd + new_run * U64.v mword <= U64.v next_start);
    assert (U64.v hd + new_run * U64.v mword <=
            MH.chunk_end (Seq.index work idx))
  end;
  pending_run_light_intro work idx next_start first_blue new_run
#pop-options

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --split_queries always"
let nonblack_extended_run_light_flush_pre
    (work: MH.major_heap)
    (idx: nat)
    (start: hp_addr)
    (first: obj_addr)
    (wz: Obj.wosize)
    (first_blue: U64.t)
    (run_words: nat)
  : Lemma
      (requires
        pending_run_light work idx start first_blue run_words /\
        idx < Seq.length work /\
        hd_address first == start /\
        U64.v first == U64.v start + U64.v mword /\
        MH.word_in_chunk (Seq.index work idx) start /\
        U64.v start + (U64.v wz + 1) * U64.v mword <=
          MH.chunk_end (Seq.index work idx))
      (ensures
        (let new_first : U64.t = if run_words = 0 then first else first_blue in
         let new_run = run_words + U64.v wz + 1 in
         (new_run <> 0 /\
          ~(U64.v new_first < U64.v mword) /\
          ~(U64.v new_first >= heap_size) /\
          ~(U64.v new_first % U64.v mword <> 0) /\
          new_run - 1 < pow2 54 ==>
           (let fb : obj_addr = new_first in
            let hd = hd_address fb in
            idx < Seq.length work /\
            MH.word_in_chunk (Seq.index work idx) hd /\
            U64.v hd + new_run * U64.v mword <=
              MH.chunk_end (Seq.index work idx)))))
  =
  let new_first : U64.t = if run_words = 0 then first else first_blue in
  let new_run = run_words + U64.v wz + 1 in
  if new_run <> 0 /\
     ~(U64.v new_first < U64.v mword) /\
     ~(U64.v new_first >= heap_size) /\
     ~(U64.v new_first % U64.v mword <> 0) /\
     new_run - 1 < pow2 54
  then begin
    if run_words = 0 then begin
      assert (new_first == first);
      assert (new_run == U64.v wz + 1);
      assert (hd_address new_first == start);
      assert (MH.word_in_chunk (Seq.index work idx) (hd_address new_first));
      assert (U64.v (hd_address new_first) + new_run * U64.v mword ==
              U64.v start + (U64.v wz + 1) * U64.v mword)
    end else begin
      nat_nonzero_pos run_words;
      let rw : pos = run_words in
      assert (new_first == first_blue);
      assert (run_words - 1 <= new_run - 1);
      assert (run_words - 1 < pow2 54);
      pending_run_light_flush_pre work idx start first_blue run_words;
      let fb : obj_addr = first_blue in
      let hd = hd_address fb in
      assert (MH.word_in_chunk (Seq.index work idx) hd);
      assert (U64.v hd + run_words * U64.v mword <= U64.v start);
      assert (new_run == run_words + U64.v wz + 1);
      assert (new_run == run_words + (U64.v wz + 1));
      FStar.Math.Lemmas.distributivity_add_left
        run_words (U64.v wz + 1) (U64.v mword);
      assert (U64.v hd + new_run * U64.v mword ==
              U64.v hd + run_words * U64.v mword +
              (U64.v wz + 1) * U64.v mword);
      assert (U64.v hd + new_run * U64.v mword <=
              U64.v start + (U64.v wz + 1) * U64.v mword);
      assert (U64.v hd + new_run * U64.v mword <=
              MH.chunk_end (Seq.index work idx))
    end
  end
#pop-options

#push-options "--z3rlimit 10 --fuel 1 --ifuel 1 --split_queries always"
let rec chunked_fused_aux_other_chunk_preserves_objects_from_from_light
    (source work: MH.major_heap)
    (proc_idx: nat{proc_idx < Seq.length source})
    (target_idx: nat)
    (proc_start target_start: hp_addr)
    (protected: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        proc_idx < Seq.length work /\
        target_idx < Seq.length work /\
        proc_idx <> target_idx /\
        MH.chunk_start (Seq.index work proc_idx) ==
          MH.chunk_start (Seq.index source proc_idx) /\
        MH.chunk_end (Seq.index work proc_idx) ==
          MH.chunk_end (Seq.index source proc_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        pending_run_light
          work proc_idx proc_start first_blue run_words /\
        (forall (o: obj_addr).
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source proc_idx) proc_start) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source work
            (MH.objects_in_chunk_from (Seq.index source proc_idx) proc_start)
            first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
      (decreases MH.chunk_end (Seq.index source proc_idx) - U64.v proc_start)
  =
  let c = Seq.index source proc_idx in
  let objs = MH.objects_in_chunk_from c proc_start in
  if Seq.length objs = 0 then begin
    Defs.chunked_fused_aux_empty_length
      source work objs first_blue run_words fp;
    pending_run_light_flush_pre
      work proc_idx proc_start first_blue run_words;
    Vertex.chunked_flush_blue_other_chunk_preserves_objects_from
      work proc_idx target_idx target_start protected first_blue run_words fp;
    let final = fst (Defs.chunked_flush_blue work first_blue run_words fp) in
    assert (fst (Defs.chunked_fused_aux
             source work objs first_blue run_words fp) == final)
  end else begin
    assert (Seq.length objs > 0);
    objects_in_chunk_from_nonempty_bounds c proc_start;
      let obj = Seq.head objs in
      let header = MH.read_word_in_chunk c proc_start in
      let wz = Obj.getWosize header in
      let obj_size_words = U64.v wz + 1 in
      let next_start_nat : nat =
        U64.v proc_start + obj_size_words * U64.v mword in
      assert (next_start_nat <= MH.chunk_end c);
      assert (next_start_nat < pow2 64);
      objects_in_chunk_from_cons_facts c proc_start objs;
      f_address_spec proc_start;
      assert (obj == f_address proc_start);
      hd_f_roundtrip proc_start;
      assert (hd_address obj == proc_start);
      assert (U64.v obj == U64.v proc_start + U64.v mword);
      assert (MH.word_in_chunk c proc_start);
      word_in_chunk_same_range c (Seq.index work proc_idx) proc_start;
      assert (U64.v (Defs.chunked_wosize_of_object source obj) ==
              MH.object_wosize_in_chunk c obj);
      assert (MH.object_wosize_in_chunk c obj == U64.v wz);
      assert (U64.v (Defs.chunked_wosize_of_object source obj) == U64.v wz);
      let tail =
        if next_start_nat >= MH.chunk_end c then Seq.empty
        else begin
          assert (next_start_nat < MH.chunk_end c);
          assert (MH.chunk_end c <= heap_size);
          assert (next_start_nat < heap_size);
          assert (next_start_nat < pow2 64);
          assert (U64.v proc_start % U64.v mword == 0);
          MH.next_object_start_aligned proc_start obj_size_words;
          assert (next_start_nat ==
            U64.v proc_start + obj_size_words * U64.v mword);
          assert ((U64.v proc_start + obj_size_words * U64.v mword) %
            U64.v mword == 0);
          assert (next_start_nat % U64.v mword == 0);
          let next_start : hp_addr = hp_addr_of_aligned_nat next_start_nat in
          MH.objects_in_chunk_from c next_start
        end
      in
      if Defs.chunked_is_black source obj then begin
        flush_pending_light_other_chunk_post
          work proc_idx target_idx proc_start target_start protected
          first_blue run_words fp;
        assert (U64.v proc_start <= MH.chunk_end (Seq.index work proc_idx));
        chunked_flush_blue_before_preserves_objects_from_light
          work proc_idx proc_start first_blue run_words fp;
        let flushed = Defs.chunked_flush_blue work first_blue run_words fp in
        let work' = fst flushed in
        let fp' = snd flushed in
        other_chunk_post_elim
          work work' target_idx target_start protected;
        assert (MH.well_formed_major_heap work');
        assert (proc_idx < Seq.length work');
        assert (target_idx < Seq.length work');
        assert (MH.chunk_start (Seq.index work' proc_idx) ==
                MH.chunk_start (Seq.index work proc_idx));
        assert (MH.chunk_end (Seq.index work' proc_idx) ==
                MH.chunk_end (Seq.index work proc_idx));
        assert (MH.chunk_start (Seq.index work' proc_idx) ==
                MH.chunk_start c);
        assert (MH.chunk_end (Seq.index work' proc_idx) ==
                MH.chunk_end c);
        assert (Seq.mem protected
          (MH.objects_in_chunk_from
            (Seq.index work' target_idx) target_start));
        assert (MH.object_wosize_in_chunk
          (Seq.index work' target_idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work target_idx) protected);
        assert (MH.chunk_start (Seq.index work' target_idx) ==
                MH.chunk_start (Seq.index work target_idx));
        assert (MH.chunk_end (Seq.index work' target_idx) ==
                MH.chunk_end (Seq.index work target_idx));
        other_chunk_post_intro
          work work' target_idx target_start protected;
        word_in_chunk_same_range
          (Seq.index work proc_idx) (Seq.index work' proc_idx) proc_start;
        Vertex.chunked_make_white_other_chunk_preserves_objects_from
          work' proc_idx target_idx target_start protected obj;
        let work'' = Defs.chunked_make_white work' obj in
        assert (MH.well_formed_major_heap work'');
        assert (target_idx < Seq.length work'');
        assert (Seq.mem protected
          (MH.objects_in_chunk_from
            (Seq.index work'' target_idx) target_start));
        assert (MH.object_wosize_in_chunk
          (Seq.index work'' target_idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work target_idx) protected);
        assert (MH.object_wosize_in_chunk
          (Seq.index work'' target_idx) protected ==
          MH.object_wosize_in_chunk (Seq.index work' target_idx) protected);
        assert (MH.chunk_start (Seq.index work'' target_idx) ==
                MH.chunk_start (Seq.index work target_idx));
        assert (MH.chunk_start (Seq.index work'' target_idx) ==
                MH.chunk_start (Seq.index work' target_idx));
        assert (MH.chunk_end (Seq.index work'' target_idx) ==
                MH.chunk_end (Seq.index work target_idx));
        assert (MH.chunk_end (Seq.index work'' target_idx) ==
                MH.chunk_end (Seq.index work' target_idx));
        other_chunk_post_intro
          work' work'' target_idx target_start protected;
        other_chunk_post_compose
          work work' work'' target_idx target_start protected;
        if next_start_nat >= MH.chunk_end c then begin
          assert (tail == Seq.empty);
          Defs.chunked_fused_aux_empty_length
            source work'' tail 0UL 0 fp';
          Defs.chunked_flush_blue_empty work'' 0UL fp';
          assert (fst (Defs.chunked_fused_aux
                   source work'' tail 0UL 0 fp') == work'')
        end else begin
          let next_start : hp_addr = hp_addr_of_aligned_nat next_start_nat in
          next_object_start_nat_gt proc_start wz;
          assert (U64.v proc_start < next_start_nat);
          assert (U64.v next_start == next_start_nat);
          assert (U64.v proc_start < U64.v next_start);
          assert (U64.v next_start <= MH.chunk_end c);
          chunk_tail_measure_decreases c proc_start next_start;
          assert (hd_address obj == proc_start);
          assert (MH.word_in_chunk (Seq.index work' proc_idx) (hd_address obj));
          next_object_start_after_header proc_start wz;
          assert (U64.v next_start ==
                  U64.v proc_start + (U64.v wz + 1) * U64.v mword);
          assert (U64.v (hd_address obj) + U64.v mword <= U64.v next_start);
          Reach.chunked_make_white_before_preserves_objects_from_at_index
            work' proc_idx next_start obj;
          assert (tail == MH.objects_in_chunk_from c next_start);
          assert (Seq.tail objs == tail);
          assert (Seq.tail objs == MH.objects_in_chunk_from c next_start);
          VS.wosize_match_tail_from_objects_from
            source c proc_start next_start objs;
          assert (proc_idx < Seq.length work'');
          pending_run_light_empty work'' proc_idx next_start;
          assert (MH.chunk_start (Seq.index work'' proc_idx) ==
                  MH.chunk_start c);
          assert (MH.chunk_end (Seq.index work'' proc_idx) ==
                  MH.chunk_end c);
          chunked_fused_aux_other_chunk_preserves_objects_from_from_light
            source work'' proc_idx target_idx next_start target_start
            protected 0UL 0 fp'
        end;
        assert (Seq.tail objs == tail);
        let tail_final =
          fst (Defs.chunked_fused_aux source work'' tail 0UL 0 fp') in
        assert (tail_final ==
          fst (Defs.chunked_fused_aux source work'' (Seq.tail objs) 0UL 0 fp'));
        other_chunk_post_intro
          work'' tail_final target_idx target_start protected;
        other_chunk_black_head_finish
          source work objs first_blue run_words fp
          target_idx target_start protected
        ;
        let final =
          fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp) in
        other_chunk_post_elim
          work final target_idx target_start protected
      end else begin
        Defs.chunked_fused_aux_nonblack_step
          source work objs first_blue run_words fp;
        let new_first : U64.t = if run_words = 0 then obj else first_blue in
        let new_run = run_words + U64.v (Defs.chunked_wosize_of_object source obj) + 1 in
        if next_start_nat >= MH.chunk_end c then begin
          assert (tail == Seq.empty);
          Defs.chunked_fused_aux_empty_length
            source work tail new_first new_run fp;
          assert (next_start_nat <= MH.chunk_end c);
          terminal_next_start_at_chunk_end c proc_start wz next_start_nat;
          assert (next_start_nat == MH.chunk_end c);
          assert (U64.v proc_start + (U64.v wz + 1) * U64.v mword <=
                  MH.chunk_end c);
          assert (MH.chunk_end (Seq.index work proc_idx) == MH.chunk_end c);
          nonblack_extended_run_light_flush_pre
            work proc_idx proc_start obj wz first_blue run_words;
          Vertex.chunked_flush_blue_other_chunk_preserves_objects_from
            work proc_idx target_idx target_start protected new_first new_run fp
        end else begin
          let next_start : hp_addr = hp_addr_of_aligned_nat next_start_nat in
          next_object_start_nat_gt proc_start wz;
          assert (U64.v proc_start < next_start_nat);
          assert (U64.v next_start == next_start_nat);
          assert (U64.v proc_start < U64.v next_start);
          assert (U64.v next_start <= MH.chunk_end c);
          chunk_tail_measure_decreases c proc_start next_start;
          assert (tail == MH.objects_in_chunk_from c next_start);
          assert (Seq.tail objs == tail);
          assert (Seq.tail objs == MH.objects_in_chunk_from c next_start);
          if run_words = 0 then
            pending_run_light_extend_nonblack_empty
              work proc_idx proc_start next_start obj wz
          else begin
            nat_nonzero_pos run_words;
            let rw : pos = run_words in
            pending_run_light_extend_nonblack_nonempty
              work proc_idx proc_start next_start obj wz first_blue rw
          end;
          VS.wosize_match_tail_from_objects_from
            source c proc_start next_start objs;
          chunked_fused_aux_other_chunk_preserves_objects_from_from_light
            source work proc_idx target_idx next_start target_start
            protected new_first new_run fp
        end;
        assert (Seq.tail objs == tail);
        let tail_final =
          fst (Defs.chunked_fused_aux source work tail new_first new_run fp) in
        assert (tail_final ==
          fst (Defs.chunked_fused_aux source work (Seq.tail objs) new_first new_run fp));
        other_chunk_post_intro
          work tail_final target_idx target_start protected;
        other_chunk_nonblack_head_finish
          source work objs first_blue run_words fp
          target_idx target_start protected
        ;
        let final =
          fst (Defs.chunked_fused_aux
            source work objs first_blue run_words fp) in
        other_chunk_post_elim
          work final target_idx target_start protected
      end
  end
#pop-options

let chunked_fused_aux_other_chunk_preserves_objects_from_from
    (source work: MH.major_heap)
    (proc_idx: nat{proc_idx < Seq.length source})
    (target_idx: nat)
    (proc_start target_start: hp_addr)
    (protected: obj_addr)
    (first_blue: U64.t)
    (run_words: nat)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        proc_idx < Seq.length work /\
        target_idx < Seq.length work /\
        proc_idx <> target_idx /\
        MH.chunk_start (Seq.index work proc_idx) ==
          MH.chunk_start (Seq.index source proc_idx) /\
        MH.chunk_end (Seq.index work proc_idx) ==
          MH.chunk_end (Seq.index source proc_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        Pending.pending_run_before_start
          work proc_idx (Seq.index source proc_idx).base proc_start
          first_blue run_words /\
        (forall (o: obj_addr).
          Seq.mem o
            (MH.objects_in_chunk_from (Seq.index source proc_idx) proc_start) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source work
            (MH.objects_in_chunk_from (Seq.index source proc_idx) proc_start)
            first_blue run_words fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
  =
  pending_run_light_from_pending
    work proc_idx (Seq.index source proc_idx).base proc_start
    first_blue run_words;
  chunked_fused_aux_other_chunk_preserves_objects_from_from_light
    source work proc_idx target_idx proc_start target_start
    protected first_blue run_words fp

let chunked_fused_aux_other_chunk_preserves_objects_from
    (source work: MH.major_heap)
    (proc_idx: nat{proc_idx < Seq.length source})
    (target_idx: nat)
    (target_start: hp_addr)
    (protected: obj_addr)
    (fp: U64.t)
  : Lemma
      (requires
        MH.well_formed_major_heap work /\
        proc_idx < Seq.length work /\
        target_idx < Seq.length work /\
        proc_idx <> target_idx /\
        MH.chunk_start (Seq.index work proc_idx) ==
          MH.chunk_start (Seq.index source proc_idx) /\
        MH.chunk_end (Seq.index work proc_idx) ==
          MH.chunk_end (Seq.index source proc_idx) /\
        Seq.mem protected
          (MH.objects_in_chunk_from (Seq.index work target_idx) target_start) /\
        (forall (o: obj_addr).
          Seq.mem o (MH.objects_in_chunk (Seq.index source proc_idx)) ==>
          U64.v (Defs.chunked_wosize_of_object source o) ==
          MH.object_wosize_in_chunk (Seq.index source proc_idx) o))
      (ensures
        (let final =
          fst (Defs.chunked_fused_aux
            source work (MH.objects_in_chunk (Seq.index source proc_idx))
            0UL 0 fp) in
         MH.well_formed_major_heap final /\
         target_idx < Seq.length final /\
         MH.objects_in_chunk_from (Seq.index final target_idx) target_start ==
           MH.objects_in_chunk_from (Seq.index work target_idx) target_start /\
         Seq.mem protected
           (MH.objects_in_chunk_from (Seq.index final target_idx) target_start) /\
         MH.object_wosize_in_chunk (Seq.index final target_idx) protected ==
           MH.object_wosize_in_chunk (Seq.index work target_idx) protected /\
         MH.chunk_start (Seq.index final target_idx) ==
           MH.chunk_start (Seq.index work target_idx) /\
         MH.chunk_end (Seq.index final target_idx) ==
           MH.chunk_end (Seq.index work target_idx)))
  =
  let c = Seq.index source proc_idx in
  assert (MH.objects_in_chunk c == MH.objects_in_chunk_from c c.base);
  Pending.pending_run_before_start_empty work proc_idx c.base c.base;
  chunked_fused_aux_other_chunk_preserves_objects_from_from
    source work proc_idx target_idx c.base target_start protected 0UL 0 fp
