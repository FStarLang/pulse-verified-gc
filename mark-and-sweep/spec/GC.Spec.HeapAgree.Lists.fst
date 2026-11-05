/// ---------------------------------------------------------------------------
/// GC.Spec.HeapAgree.Lists - agreement facts for several free lists
/// ---------------------------------------------------------------------------
///
/// Two facts about `GC.Spec.HeapAgree` that the size-class collector needs:
/// a heap that differs from another only in the link words of its free blocks
/// agrees with it modulo free links, and strict agreement keeps every sound
/// free list the same.

module GC.Spec.HeapAgree.Lists

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
module HA = GC.Spec.HeapAgree
module FL = GC.Spec.FreeList

/// `a` is the link word of a free block of `h` that has a field.
let blue_link_word (h: heap) (a: hp_addr) : prop =
  exists (b: obj_addr).
    Seq.mem b (objects zero_addr h) /\ is_blue b h /\
    U64.v (wosize_of_object b h) >= 1 /\ (b <: U64.t) == (a <: U64.t)

/// ---------------------------------------------------------------------------
/// Differing only in free links
/// ---------------------------------------------------------------------------

/// The header of an object is no other object's link word.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let header_not_link (h2: heap) (f: obj_addr)
  : Lemma (requires Seq.mem f (objects zero_addr h2))
          (ensures ~(blue_link_word h2 (hd_address f)))
  = hd_address_spec f;
    let aux (b: obj_addr)
      : Lemma (requires Seq.mem b (objects zero_addr h2) /\
                        U64.v (wosize_of_object b h2) >= 1 /\
                        (b <: U64.t) == (hd_address f <: U64.t))
              (ensures False)
      = objects_separated zero_addr h2 b f
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// A word of a live block's body is no free block's link word.
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
private let body_not_link (h2: heap) (f: obj_addr) (a: hp_addr)
  : Lemma (requires Seq.mem f (objects zero_addr h2) /\ ~(is_blue f h2) /\
                    U64.v a >= U64.v f /\
                    U64.v a + 8 <= U64.v f + U64.v (wosize_of_object f h2) * 8)
          (ensures ~(blue_link_word h2 a))
  = let aux (b: obj_addr)
      : Lemma (requires Seq.mem b (objects zero_addr h2) /\ is_blue b h2 /\
                        U64.v (wosize_of_object b h2) >= 1 /\
                        (b <: U64.t) == (a <: U64.t))
              (ensures False)
      = objects_separated zero_addr h2 b f;
        objects_separated zero_addr h2 f b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

let differ_in_links (h1 h2: heap) : prop =
  forall (a: hp_addr). ~(blue_link_word h2 a) ==> read_word h1 a == read_word h2 a

/// Along the walk of `h2` from a position whose objects are objects of `h2`.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let rec walk_links (start: hp_addr) (h1 h2: heap)
  : Lemma (requires differ_in_links h1 h2 /\
                    (forall (x: obj_addr). Seq.mem x (objects start h2) ==>
                       Seq.mem x (objects zero_addr h2)) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr h2) ==>
                       Seq.mem x (objects start h2) \/
                       U64.v x + U64.v (wosize_of_object x h2) * 8 <= U64.v start))
          (ensures HA.walk_agree_gen false start h1 h2)
          (decreases (heap_size - U64.v start))
  = if U64.v start + 8 >= heap_size then ()
    else begin
      let wz = getWosize (read_word h2 start) in
      let next = U64.v start + (U64.v wz + 1) * 8 in
      if next > heap_size then begin
        // Nothing is left on the walk, so every object ends before `start`
        // and `start` is no link word.
        (if Seq.length (objects start h2) > 0 then objects_nonempty_head_fits start h2);
        assert (~(blue_link_word h2 start))
      end
      else begin
        HA.walk_next_aligned start (U64.v wz);
        f_address_spec start;
        hd_f_roundtrip start;
        let f = f_address start in
        if next < heap_size then begin
          let nx : hp_addr = U64.uint_to_t next in
          objects_cons_step_to start h2 nx;
          mem_cons_lemma f f (objects nx h2);
          let sub (x: obj_addr)
            : Lemma (Seq.mem x (objects nx h2) ==> Seq.mem x (objects start h2))
            = mem_cons_lemma x f (objects nx h2)
          in
          FStar.Classical.forall_intro sub;
          wosize_of_object_spec f h2;
          let before (x: obj_addr)
            : Lemma (Seq.mem x (objects zero_addr h2) ==>
                     Seq.mem x (objects nx h2) \/
                     U64.v x + U64.v (wosize_of_object x h2) * 8 <= U64.v nx)
            = mem_cons_lemma x f (objects nx h2)
          in
          FStar.Classical.forall_intro before;
          walk_links nx h1 h2
        end else begin
          objects_cons_end start h2;
          mem_cons_lemma f f Seq.empty
        end;
        assert (Seq.mem f (objects zero_addr h2));
        header_not_link h2 f;
        FStar.Classical.forall_intro
          (FStar.Classical.move_requires (body_not_link h2 f));
        assert (HA.block_agree_gen false h1 h2 f);
        HA.walk_agree_links_step start h1 h2
      end
    end
#pop-options

val agree_links_except_blue_links (h1 h2: heap)
  : Lemma (requires forall (a: hp_addr). ~(blue_link_word h2 a) ==> read_word h1 a == read_word h2 a)
          (ensures HA.heaps_agree_mod_free_links h1 h2)

let agree_links_except_blue_links h1 h2 = walk_links zero_addr h1 h2

/// ---------------------------------------------------------------------------
/// Strict agreement keeps a sound free list
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let rec agree_on_fl (h1 h2: heap) (fp obj: U64.t) (n: nat)
  : Lemma (requires HA.heaps_agree_mod_free h1 h2 /\ FL.fl_sound h2 fp)
          (ensures FL.on_fl h1 fp obj n == FL.on_fl h2 fp obj n)
          (decreases n)
  = if n = 0 || not (FL.fl_node fp) || fp = obj then ()
    else begin
      FL.on_fl_head h2 fp;
      assert (FL.reachable_on_fl h2 fp fp);
      HA.agree_field0 h1 h2 (fp <: obj_addr);
      FL.fl_sound_tail h2 fp;
      agree_on_fl h1 h2 (FL.fl_next h2 fp) obj (n - 1)
    end
#pop-options

val agree_reachable (h1 h2: heap) (fp y: U64.t)
  : Lemma (requires HA.heaps_agree_mod_free h1 h2 /\ FL.fl_sound h2 fp)
          (ensures FL.reachable_on_fl h1 fp y <==> FL.reachable_on_fl h2 fp y)

let agree_reachable h1 h2 fp y =
  let n_eq (n: nat) : Lemma (FL.on_fl h1 fp y n == FL.on_fl h2 fp y n)
    = agree_on_fl h1 h2 fp y n
  in
  FStar.Classical.forall_intro n_eq
