/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FollowWitness - what the minor collection's contract accepts
/// ---------------------------------------------------------------------------
///
/// Design doc §12.  A world whose nursery holds one live block (a root
/// points at it) with two fields:
///
///   * `Major 2`, an infix pointer into the major closure at 0 (wosize 3),
///     whose field 1 is an infix header of offset 2 (a `let rec`'s second
///     function), and
///   * `VInt 249`, the word 249 (the OCaml int 124), which reads as an
///     infix header of offset 0, in a block that is not a closure.
///
/// The minor collection's precondition (`minor_pre`, with the toy
/// allocator) holds of it.  Before §12 it did not: `young_sound` asked
/// `Major 2` to be a block (G39), and `young_infix_ok` asked the field
/// reading as an infix header to be one of a closure (G38(b)).  The byte
/// side of the same two fields is `GC.Spec.Pages.Promote.FollowWitness`.

module GC.Spec.Top.FollowWitness

open GC.Spec.Top.Heap
open GC.Spec.Top.Iface
open GC.Spec.Top.Toy
module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// The major heap: the closure at 0, whose word 2 is an infix header of
/// offset 2; the free tail at 4.
let maj_a : mheap =
  { size = 6;
    hd = (fun (x: nat) -> if x = 0 then Some ({ wz = 3; tag = closure_tag; col = White })
                          else if x = 4 then Some ({ wz = 1; tag = 0; col = White }) else None);
    body = (fun (x: nat) -> if x = 2 then infix_word 2 else VInt 0) }

/// The nursery: one block at 0 (wosize 2, tag 0): the infix pointer, then
/// the word 249.
let yng_a : mheap =
  { size = 4;
    hd = (fun (x: nat) -> if x = 0 then Some ({ wz = 2; tag = 0; col = White }) else None);
    body = (fun (x: nat) -> if x = 1 then VPtr (Major 2) else if x = 2 then VInt 249 else VInt 0) }

let w_acc : world = { maj = maj_a; yng = yng_a; roots = [VPtr (Young 0)]; rem = [] }

/// The allocator's state: the tail at 4, nothing dead.
let st4 : tstate = { cur = 4; dead = (fun _ -> false) }

/// ---------------------------------------------------------------------------
/// The heaps
/// ---------------------------------------------------------------------------

let maj_blocks (o: nat) : Lemma (is_block maj_a o <==> o == 0 \/ o == 4) = ()

let maj_wf (_: unit) : Lemma (well_formed maj_a)
  = let cov (w: nat) : Lemma (w < maj_a.size ==> (exists (o: nat). covers maj_a o w))
      = if w <= 3 then assert (covers maj_a 0 w) else if w < 6 then assert (covers maj_a 4 w) in
    FStar.Classical.forall_intro cov;
    FStar.Classical.forall_intro maj_blocks;
    tiled_intro maj_a

/// The infix pointer resolves to the closure; it is not a block.
let infix_ptr (_: unit) : Lemma (resolve maj_a 2 == Some 0 /\ ~(is_block maj_a 2))
  = assert (infix_hdr (infix_word 2) == Some 2)

let yng_blocks (o: nat) : Lemma (is_block yng_a o <==> o == 0) = ()

let yng_ok (_: unit) : Lemma (young_ok yng_a)
  = FStar.Classical.forall_intro yng_blocks

/// The nursery block's fields.
let yng_fields (i: nat)
  : Lemma (requires ptr_field yng_a 0 i)
          (ensures (i == 0 /\ field yng_a 0 i == VPtr (Major 2)) \/ (i == 1 /\ field yng_a 0 i == VInt 249))
  = ()

/// ---------------------------------------------------------------------------
/// The precondition
/// ---------------------------------------------------------------------------

let inv_ok (_: unit) : Lemma (tinv Idle maj_a st4)
  = maj_wf ();
    FStar.Classical.forall_intro maj_blocks;
    tinv_intro Idle maj_a st4

let rem_ok (_: unit) : Lemma (rem_covers toy Idle st4 maj_a w_acc)
  = let c (o i b: nat)
      : Lemma (~(live_target toy Idle st4 maj_a w_acc.maj o /\ ptr_field w_acc.maj o i /\ field w_acc.maj o i == VPtr (Young b)))
      = maj_blocks o in
    FStar.Classical.forall_intro_3 c

let sound_ok (_: unit) : Lemma (young_sound toy Idle st4 maj_a w_acc)
  = infix_ptr ();
    assert (live_target toy Idle st4 maj_a maj_a 0);
    let one (y i b: nat)
      : Lemma (ptr_field w_acc.yng y i /\ field w_acc.yng y i == VPtr (Major b) ==>
               sound_value toy Idle st4 maj_a w_acc.maj (VPtr (Major b)))
      = if ptr_field w_acc.yng y i then begin
          yng_blocks y;
          yng_fields i
        end in
    FStar.Classical.forall_intro_3 one

let follow_ok (_: unit) : Lemma (young_follow_ok yng_a)
  = let one (o i a: nat) : Lemma (~(ptr_field yng_a o i /\ field yng_a o i == VPtr (Young a)))
      = if ptr_field yng_a o i then begin
          yng_blocks o;
          yng_fields i
        end in
    FStar.Classical.forall_intro_3 one

/// The block's fields, as values.
let fields_val (_: unit)
  : Lemma (field w_acc.yng 0 0 == VPtr (Major 2) /\ field w_acc.yng 0 1 == VInt 249 /\
           infix_hdr (field w_acc.yng 0 1) == Some 0 /\ tag_of w_acc.yng 0 <> closure_tag)
  = assert (field yng_a 0 1 == VInt 249);
    assert (249 % 256 = 249 /\ 249 / 1024 = 0)

/// The precondition, assembled.
let pre_ok (_: unit) : Lemma (minor_pre toy Idle st4 w_acc.maj w_acc)
  = inv_ok ();
    maj_wf ();
    yng_ok ();
    rem_ok ();
    sound_ok ();
    follow_ok ()

/// **The minor collection's precondition accepts a young field holding an
/// infix pointer into an old closure, and one holding an int that looks
/// like an infix header**, in a live block; neither is what the earlier
/// conditions allowed (`Major 2` is not a block; the word 249 reads as an
/// infix header outside a closure).
let accepted (_: unit)
  : Lemma (minor_pre toy Idle st4 w_acc.maj w_acc /\ minor_live w_acc 0 /\
           field w_acc.yng 0 0 == VPtr (Major 2) /\ resolve w_acc.maj 2 == Some 0 /\ ~(is_block w_acc.maj 2) /\
           field w_acc.yng 0 1 == VInt 249 /\ infix_hdr (field w_acc.yng 0 1) == Some 0 /\
           tag_of w_acc.yng 0 <> closure_tag)
  = pre_ok ();
    fields_val ();
    infix_ptr ();
    let l : mlive w_acc 0 = LRoot 0 0 () in
    ()
