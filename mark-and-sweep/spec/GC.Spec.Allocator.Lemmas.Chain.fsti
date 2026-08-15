module GC.Spec.Allocator.Lemmas.Chain

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

val fl_valid_transfer (g g': heap) (fp: U64.t) (fuel: nat)
  : Lemma
    (requires GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g)) ==>
                 (Seq.mem a (objects zero_addr g') /\
                  (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 ==>
                    U64.v (wosize_of_object (a <: obj_addr) g') >= 1) /\
                  (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                   U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr)))))
    (ensures GC.Spec.Allocator.Lemmas.Common.fl_valid g' fp fuel)

val fl_chain_terminates (g: heap) (fp: U64.t) (steps: nat) : Tot bool

val fl_chain_terminates_terminal (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fp = 0UL \/ U64.v fp < U64.v mword \/ U64.v fp >= heap_size \/ U64.v fp % U64.v mword <> 0)
          (ensures fl_chain_terminates g fp steps = true)

val fl_valid_any_fuel (g: heap) (fp: U64.t) (fuel fuel': nat)
  : Lemma (requires GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\ fl_chain_terminates g fp fuel)
          (ensures GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel')

val fl_chain_terminates_transfer (g g': heap) (fp: U64.t) (steps: nat)
  : Lemma
    (requires fl_chain_terminates g fp steps /\
              GC.Spec.Allocator.Lemmas.Common.fl_valid g fp steps /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g)) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures fl_chain_terminates g' fp steps)

val fl_chain_terminates_weaken (g: heap) (fp: U64.t) (s1 s2: nat)
  : Lemma (requires fl_chain_terminates g fp s1 /\ s2 >= s1)
          (ensures fl_chain_terminates g fp s2)

val fl_chain_terminates_step (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    (let hd = hd_address (fp <: obj_addr) in
                     U64.v hd + 16 <= heap_size ==>
                     fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1)))
          (ensures fl_chain_terminates g fp steps)

val fl_chain_terminates_elim (g: heap) (fp: U64.t) (steps: nat)
  : Lemma (requires fl_chain_terminates g fp steps /\
                    steps > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures fl_chain_terminates g (read_word g (fp <: obj_addr)) (steps - 1) = true)

val fl_chain_terminates_valid_zero (g: heap) (fp: U64.t)
  : Lemma (requires U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0)
          (ensures fl_chain_terminates g fp 0 = false)

val walk_chain (g: heap) (fp: U64.t) (n: nat) : Tot U64.t
val walk_chain_zero (g: heap) (fp: U64.t)
  : Lemma (ensures walk_chain g fp 0 = fp)
val walk_chain_valid (g: heap) (fp: U64.t) (n: nat) : Tot prop
val walk_chain_valid_zero (g: heap) (fp: U64.t)
  : Lemma (ensures walk_chain_valid g fp 0)

val walk_chain_valid_prefix (g: heap) (fp: U64.t) (k j: nat)
  : Lemma (requires walk_chain_valid g fp k /\ j <= k)
          (ensures walk_chain_valid g fp j)

val walk_chain_valid_at (g: heap) (fp: U64.t) (k j: nat)
  : Lemma (requires walk_chain_valid g fp k /\ j < k)
          (ensures (let node = walk_chain g fp j in
                    U64.v node >= U64.v mword /\ U64.v node < heap_size /\
                    U64.v node % U64.v mword = 0 /\
                    U64.v (hd_address (node <: obj_addr)) + 16 <= heap_size))

val walk_chain_valid_snoc (g: heap) (fp: U64.t) (k: nat)
  : Lemma (requires walk_chain_valid g fp k /\
                    (let node = walk_chain g fp k in
                     U64.v node >= U64.v mword /\ U64.v node < heap_size /\
                     U64.v node % U64.v mword = 0 /\
                     U64.v (hd_address (node <: obj_addr)) + 16 <= heap_size))
          (ensures walk_chain_valid g fp (k + 1))

val walk_chain_append (g: heap) (fp: U64.t) (m n: nat)
  : Lemma (requires walk_chain_valid g fp m)
          (ensures walk_chain g fp (m + n) = walk_chain g (walk_chain g fp m) n)

val fl_chain_terminates_unfold_steps (g: heap) (fp: U64.t) (n fuel: nat)
  : Lemma (requires n <= fuel /\ walk_chain_valid g fp n)
          (ensures fl_chain_terminates g fp fuel = fl_chain_terminates g (walk_chain g fp n) (fuel - n))

val fl_chain_kcycle_not_terminates (g: heap) (fp: U64.t) (k fuel: nat)
  : Lemma (requires k > 0 /\ walk_chain g fp k = fp /\ walk_chain_valid g fp k)
          (ensures fl_chain_terminates g fp fuel = false)

val fl_chain_2cycle_not_terminates (g: heap) (a b: U64.t) (n: nat)
  : Lemma (requires U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                    U64.v b >= U64.v mword /\ U64.v b < heap_size /\ U64.v b % U64.v mword = 0 /\
                    a <> b /\
                    U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size /\
                    U64.v (hd_address (b <: obj_addr)) + 16 <= heap_size /\
                    read_word g (a <: obj_addr) = b /\
                    read_word g (b <: obj_addr) = a)
          (ensures fl_chain_terminates g a n = false)

val fl_chain_terminates_splice (g g_new: heap) (fp splice_point: U64.t) (steps tail_steps: nat)
  : Lemma
    (requires fl_chain_terminates g fp steps /\
              GC.Spec.Allocator.Lemmas.Common.fl_valid g fp steps /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g)) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size /\
                  a <> splice_point ==>
                   read_word g_new (a <: obj_addr) == read_word g (a <: obj_addr))) /\
              (U64.v splice_point >= U64.v mword /\ U64.v splice_point < heap_size /\
               U64.v splice_point % U64.v mword = 0 /\
               U64.v (hd_address (splice_point <: obj_addr)) + 16 <= heap_size ==>
                fl_chain_terminates g_new (read_word g_new (splice_point <: obj_addr)) tail_steps))
    (ensures fl_chain_terminates g_new fp (steps + tail_steps))


val fl_valid_field_write (g: heap) (p: obj_addr) (v: U64.t) (fp: U64.t) (fuel tail_fuel: nat)
  : Lemma
    (requires GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\
              well_formed_heap g /\
              Seq.mem p (objects zero_addr g) /\
              U64.v (wosize_of_object p g) >= 1 /\
              v <> p /\
              GC.Spec.Allocator.Lemmas.Common.fl_valid (write_word g (p <: hp_addr) v) v tail_fuel /\
              tail_fuel >= fuel)
    (ensures GC.Spec.Allocator.Lemmas.Common.fl_valid (write_word g (p <: hp_addr) v) fp fuel)

val fl_valid_field_write_tail (g: heap) (p: obj_addr) (v: U64.t) (fuel: nat)
  : Lemma
    (requires well_formed_heap g /\
              Seq.mem p (objects zero_addr g) /\
              U64.v (wosize_of_object p g) >= 1 /\
              v <> p /\
              GC.Spec.Allocator.Lemmas.Common.fl_valid g v fuel)
    (ensures GC.Spec.Allocator.Lemmas.Common.fl_valid (write_word g (p <: hp_addr) v) v fuel)
val chain_avoids (g: heap) (fp excl: U64.t) (steps: nat) : Tot bool

val chain_avoids_null (g: heap) (excl: U64.t) (steps: nat)
  : Lemma (ensures chain_avoids g 0UL excl steps = true)

val chain_avoids_unfold_step (g: heap) (fp excl: U64.t) (steps: nat)
  : Lemma (requires U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size /\
                    fp <> excl /\ steps > 0)
          (ensures chain_avoids g fp excl steps =
                   chain_avoids g (read_word g (fp <: obj_addr)) excl (steps - 1))

val chain_avoids_head_ne (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ fuel > 0)
          (ensures fp <> excl)

val chain_avoids_tail (g: heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\ fuel > 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures chain_avoids g (read_word g (fp <: obj_addr)) excl (fuel - 1) = true)

val chain_avoids_transfer (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                      U64.v (wosize_of_object a g) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      a <> excl ==>
                        read_word g' a == read_word g a))
          (ensures chain_avoids g' fp excl fuel = true)

val chain_avoids_transfer_on_chain (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\
                    GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\
                    (forall (a: obj_addr). Seq.mem a (objects zero_addr g) /\
                      U64.v (wosize_of_object a g) >= 1 /\
                      U64.v (hd_address a) + 16 <= heap_size /\
                      a <> excl /\
                      chain_avoids g fp a fuel = false ==>
                        read_word g' a == read_word g a))
          (ensures chain_avoids g' fp excl fuel = true)

val chain_avoids_weaken (g: heap) (fp excl: U64.t) (fuel fuel': nat)
  : Lemma (requires chain_avoids g fp excl fuel = true /\ fuel' <= fuel)
          (ensures chain_avoids g fp excl fuel' = true)

val chain_avoids_strengthen (g: heap) (fp excl: U64.t) (s1 s2: nat)
  : Lemma (requires chain_avoids g fp excl s1 = true /\
                    fl_chain_terminates g fp s1 /\
                    s2 >= s1)
          (ensures chain_avoids g fp excl s2 = true)

val chain_avoids_transfer_excl (g g': heap) (fp excl: U64.t) (fuel: nat)
  : Lemma
    (requires chain_avoids g fp excl fuel = true /\
              GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g) /\ a <> excl) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures chain_avoids g' fp excl fuel = true)

val chain_avoids_transfer_excl2 (g g': heap) (fp excl excl2: U64.t) (fuel: nat)
  : Lemma
    (requires chain_avoids g fp excl fuel = true /\
              chain_avoids g fp excl2 fuel = true /\
              GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g) /\ a <> excl /\ a <> excl2) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures chain_avoids g' fp excl fuel = true)

val chain_avoids_unfold_steps (g: heap) (fp excl: U64.t) (n fuel: nat)
  : Lemma (requires n <= fuel /\ walk_chain_valid g fp n /\
                    chain_avoids g fp excl n = true)
          (ensures chain_avoids g fp excl fuel =
                   chain_avoids g (walk_chain g fp n) excl (fuel - n))

val first_hit (g: heap) (fp dst_obj: U64.t) (fuel: nat) : Tot nat

val first_hit_spec (g: heap) (fp dst_obj: U64.t) (fuel: nat)
  : Lemma (requires chain_avoids g fp dst_obj fuel = false)
          (ensures walk_chain g fp (first_hit g fp dst_obj fuel) = dst_obj /\
                   first_hit g fp dst_obj fuel <= fuel /\
                   walk_chain_valid g fp (first_hit g fp dst_obj fuel))

val walk_chain_one_step (g: heap) (fp: U64.t)
  : Lemma (requires U64.v fp >= U64.v mword /\ U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size)
          (ensures walk_chain g fp 1 = read_word g (fp <: obj_addr))

val chain_avoids_prev (g: heap) (prev_fp cur_fp next_fp: U64.t) (steps: nat)
  : Lemma
    (requires fl_chain_terminates g next_fp steps /\
              GC.Spec.Allocator.Lemmas.Common.fl_valid g next_fp steps /\
              U64.v prev_fp >= U64.v mword /\
              U64.v prev_fp < heap_size /\
              U64.v prev_fp % U64.v mword = 0 /\
              Seq.mem prev_fp (objects zero_addr g) /\
              U64.v (wosize_of_object (prev_fp <: obj_addr) g) >= 1 /\
              U64.v (hd_address (prev_fp <: obj_addr)) + 16 <= heap_size /\
              read_word g (prev_fp <: obj_addr) == cur_fp /\
              U64.v cur_fp >= U64.v mword /\
              U64.v cur_fp < heap_size /\
              U64.v cur_fp % U64.v mword = 0 /\
              Seq.mem cur_fp (objects zero_addr g) /\
              U64.v (wosize_of_object (cur_fp <: obj_addr) g) >= 1 /\
              U64.v (hd_address (cur_fp <: obj_addr)) + 16 <= heap_size /\
              read_word g (cur_fp <: obj_addr) == next_fp /\
              prev_fp <> cur_fp)
    (ensures chain_avoids g next_fp prev_fp steps = true)

val not_in_fl_chain_b (g: heap) (fp: U64.t) (dst_obj: U64.t) (fuel: nat) : Tot bool

val not_in_fl_chain_b_is_chain_avoids (g: heap) (fp dst_obj: U64.t) (fuel: nat)
  : Lemma (ensures not_in_fl_chain_b g fp dst_obj fuel = chain_avoids g fp dst_obj fuel)

val fl_chain_predecessor_not_in_suffix_b (g: heap) (obj: U64.t) (fuel: nat)
  : Lemma (requires fl_chain_terminates g obj fuel /\
                    GC.Spec.Allocator.Lemmas.Common.fl_valid g obj fuel /\
                    U64.v obj >= U64.v mword /\ U64.v obj < heap_size /\ U64.v obj % U64.v mword = 0 /\
                    U64.v (hd_address (obj <: obj_addr)) + 16 <= heap_size /\
                    fuel > 0)
          (ensures not_in_fl_chain_b g (read_word g (obj <: obj_addr)) obj (fuel - 1) = true)

val fl_chain_terminates_transfer_excl (g g': heap) (fp excl: U64.t) (steps: nat)
  : Lemma
    (requires fl_chain_terminates g fp steps /\
              GC.Spec.Allocator.Lemmas.Common.fl_valid g fp steps /\
              chain_avoids g fp excl steps /\
              (forall (a: U64.t).
                 (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                  Seq.mem a (objects zero_addr g) /\ a <> excl) ==>
                 (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                  U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                    read_word g' (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures fl_chain_terminates g' fp steps)

val fl_chain_no_early_repeat (g: heap) (fp: U64.t) (d fuel: nat)
  : Lemma (requires walk_chain_valid g fp d /\ d > 0 /\
                    fl_chain_terminates g fp fuel /\ GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\ fuel >= d)
          (ensures chain_avoids g fp (walk_chain g fp d) d = true)

val walk_chain_valid_preserved (g g2: heap) (fp excl: U64.t) (d fuel: nat)
  : Lemma
    (requires walk_chain_valid g fp d /\
             GC.Spec.Allocator.Lemmas.Common.fl_valid g fp fuel /\ fuel >= d /\
             chain_avoids g fp excl d = true /\
             (forall (a: U64.t).
                (U64.v a >= U64.v mword /\ U64.v a < heap_size /\ U64.v a % U64.v mword = 0 /\
                 Seq.mem a (objects zero_addr g) /\ a <> excl) ==>
                (U64.v (wosize_of_object (a <: obj_addr) g) >= 1 /\
                 U64.v (hd_address (a <: obj_addr)) + 16 <= heap_size ==>
                   read_word g2 (a <: obj_addr) == read_word g (a <: obj_addr))))
    (ensures walk_chain_valid g2 fp d /\ walk_chain g2 fp d = walk_chain g fp d)

/// The free-list search never bottoms out on its fuel budget: if the chain from
/// `cur_fp` reaches a terminal within `fuel` steps, then handing `alloc_search`
/// any larger budget yields exactly the same result.  Hence `alloc_search` never
/// takes its `fuel = 0` branch, and an OOM answer is always the genuine
/// "nothing on the free list fits" answer rather than an artefact of the bound.
val alloc_search_fuel_irrelevant
      (g: heap) (head_fp prev_fp cur_fp: U64.t) (requested_wz: nat) (fuel fuel': nat)
  : Lemma
    (requires fl_chain_terminates g cur_fp fuel /\ fuel' >= fuel)
    (ensures alloc_search g head_fp prev_fp cur_fp requested_wz fuel' ==
             alloc_search g head_fp prev_fp cur_fp requested_wz fuel)

/// Corollary: the `heap_words` budget baked into `alloc_spec` never binds.
val alloc_spec_fuel_irrelevant (g: heap) (fp: U64.t) (requested_wz: nat) (extra: nat)
  : Lemma
    (requires fl_chain_terminates g fp heap_words)
    (ensures (let wz = if requested_wz = 0 then 1 else requested_wz in
              alloc_spec g fp requested_wz ==
              alloc_search g fp 0UL fp wz (heap_words + extra)))
