/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PromoteCopy - a promoted copy, read as the model
/// ---------------------------------------------------------------------------
///
/// The promotion copies the fields of a nursery object into the block the
/// allocator returned (`GC.Gen.WriteBodyLemmas.copy_fields`).  Read as the
/// model, this is the Fill of the block with the young block's fields
/// (`copy_cabs`): each word copied is the young field the nursery's reading
/// gives.  Nothing here depends on an allocator.

module GC.Spec.Top.PromoteCopy

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.WriteBodyLemmas
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.Young
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module L = FStar.List.Tot
module U64 = FStar.UInt64
module BB = GC.Spec.Top.ByteBarrier

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The nursery object of the young block at `y`.
let yobj (y: nat{8 * y + 8 < pow2 64}) : U64.t = U64.uint_to_t (8 * y + 8)

let yobj_v (y: nat) (f: nat) : Lemma (requires 8 * y + 8 < pow2 64) (ensures U64.v (yobj y) + f * 8 == 8 * (y + 1 + f))
  = ()

let ypos (o f wz b: nat)
  : Lemma (requires f < wz /\ 8 * (o + wz + 1) <= b /\ b <= minor_heap_size)
          (ensures ok_pos (8 * (o + 1 + f)) /\ 8 * o + 8 < pow2 64 /\ 8 * o + 8 + f * 8 == 8 * (o + 1 + f))
  = msz ();
    FStar.Math.Lemmas.multiple_modulo_lemma (o + 1 + f) 8

/// The young block's place in the nursery.
let yplace (y: M.mheap) (ms: minor_state) (o f: nat)
  : Lemma (requires yrepr y ms /\ M.is_block y o /\ f < M.wz_of y o)
          (ensures ok_pos (8 * (o + 1 + f)) /\ 8 * o + 8 < pow2 64 /\ 8 * o + 8 + f * 8 == 8 * (o + 1 + f) /\
                   R.agree y (yabs ms))
  = let b : nat = U64.v ms.bump in
    let wz : nat = M.wz_of y o in
    yrepr_elim y ms;
    yok_elim ms;
    R.agree_blocks y (yabs ms) o;
    yblock ms o;
    ypos o f wz b

/// A field of a young block, read by GC.Gen.MinorHeap, is the model's.
#push-options "--z3rlimit 40"
let young_field (y: M.mheap) (ms: minor_state) (o f: nat)
  : Lemma (requires yrepr y ms /\ M.is_block y o /\ f < M.wz_of y o)
          (ensures 8 * o + 8 < pow2 64 /\ absv (minor_read_field ms (yobj o) f) == M.field y o f /\
                   storable_w (M.field y o f))
  = let p : nat = 8 * (o + 1 + f) in
    yplace y ms o f;
    yobj_v o f;
    yw_read ms.data p;
    yrepr_field y ms o f;
    absv_storable (yw ms.data p)
#pop-options

/// The address of field `i` of the block at `c`.
let copy_addr (g: heap) (c i: nat)
  : Lemma (requires M.is_block (cabs g) c /\ i < M.wz_of (cabs g) c)
          (ensures pos c + 8 < heap_size /\ pos (c + 1 + i) < heap_size /\
                   U64.v (obj_of c) + i * 8 + 8 <= heap_size /\ (U64.v (obj_of c) + i * 8) % 8 == 0 /\
                   U64.uint_to_t (U64.v (obj_of c) + i * 8) == hp (c + 1 + i))
  = abs_block_walk g c;
    msize_pos (c + 1 + i);
    msize_pos (c + M.wz_of (cabs g) c);
    pos_aligned (c + 1 + i);
    let a = U64.uint_to_t (U64.v (obj_of c) + i * 8) in
    assert (U64.v a == pos (c + 1 + i));
    U64.v_inj a (hp (c + 1 + i))

/// The fields `i .. n` of `c` written with the young fields `i .. n` of `o`.
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec copy_from (y: M.mheap) (ms: minor_state) (o: nat) (g: heap) (c i n: nat)
  : Lemma (requires yrepr y ms /\ M.is_block y o /\ n <= M.wz_of y o /\
                    M.is_block (cabs g) c /\ n <= M.wz_of (cabs g) c /\ pos c + 8 < heap_size /\
                    8 * o + 8 < pow2 64 /\ i <= n)
          (ensures R.heq (cabs (copy_fields ms g (yobj o) (obj_of c) i n))
                         (BB.fill_at (cabs g) c i (M.fields_from y o i (n - i))))
          (decreases (if i >= n then 0 else n - i))
  = if i >= n then begin
      copy_fields_base ms g (yobj o) (obj_of c) i n;
      assert (M.fields_from y o i (n - i) == [])
    end
    else begin
      young_field y ms o i;
      copy_addr g c i;
      let k = c + 1 + i in
      cabs_write_field g c i (minor_read_field ms (yobj o) i);
      copy_fields_step ms g (yobj o) (obj_of c) i n;
      let g1 = write_word g (hp k) (minor_read_field ms (yobj o) i) in
      assert (R.heq (cabs g1) (M.set_field (cabs g) c i (M.field y o i)));
      copy_from y ms o g1 c (i + 1) n;
      assert (M.fields_from y o i (n - i) == M.field y o i :: M.fields_from y o (i + 1) (n - (i + 1)));
      BB.fill_at_cons (cabs g) c i (M.field y o i) (M.fields_from y o (i + 1) (n - (i + 1))) (cabs g1)
    end
#pop-options

/// **The copy is the Fill of the block with the young block's fields.**
let copy_cabs (y: M.mheap) (ms: minor_state) (o: nat) (g: heap) (c: nat)
  : Lemma (requires yrepr y ms /\ M.is_block y o /\ M.is_block (cabs g) c /\
                    M.wz_of (cabs g) c == M.wz_of y o /\ pos c + 8 < heap_size /\ 8 * o + 8 < pow2 64)
          (ensures R.heq (cabs (copy_fields ms g (yobj o) (obj_of c) 0 (M.wz_of y o)))
                         (M.fill (cabs g) c (M.fields_of y o)))
  = copy_from y ms o g c 0 (M.wz_of y o);
    BB.fill_at_zero (cabs g) c (M.fields_of y o)

/// A young block is a nursery object, of its size and tag.
#push-options "--z3rlimit 40"
let young_obj (y: M.mheap) (ms: minor_state) (o: nat)
  : Lemma (requires yrepr y ms /\ M.is_block y o)
          (ensures 8 * o + 8 < pow2 64 /\ Seq.mem (yobj o) (minor_objects ms) /\
                   minor_wosize ms (yobj o) == M.wz_of y o /\ minor_tag ms (yobj o) == M.tag_of y o /\
                   M.wz_of y o > 0 /\ M.tag_of y o <> M.infix_tag)
  = let b : nat = U64.v ms.bump in
    let p8 : nat = 8 * o in
    let wz : nat = M.wz_of y o in
    yrepr_elim y ms;
    yok_elim ms;
    R.agree_blocks y (yabs ms) o;
    yblock ms o;
    ypos o 0 wz b;
    let hdr = yw ms.data p8 in
    minor_reads ms o;
    hdr_bits hdr;
    young_objects ms (yobj o);
    assert (U64.v (yobj o) - 8 == 8 * o)
#pop-options
