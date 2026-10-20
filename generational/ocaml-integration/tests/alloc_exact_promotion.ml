(* End-to-end detection of the allocator's one-word-leftover bug (issue #19),
 * through the promotion path.
 *
 *   usage: ocamlrun ./alloc_exact_promotion.byte <major-heap-words> [fill]
 *   with MIN_EXPANSION_WORDSIZE set to the same word count.
 *   Exit 0: exact. Exit 1: a promoted object's header is wrong. Exit 2:
 *   the harness did not get the heap into the shape it needs.
 *
 * Differential, like the other correctness tests: it must pass under stock
 * OCaml too, which allocates exactly.
 *
 * THE BUG. When a free block is exactly one word longer than the request, the
 * pre-fix allocator hands the whole block over and writes the header with the
 * BLOCK's wosize instead of the requested one (GC_Gen_Impl.c, the
 * `leftover >= 2` else-branch: `makeHeader(block_wz, white, 0)`).
 *
 * WHY THIS GOES THROUGH PROMOTION. On the direct major path the lie never
 * reaches the object: caml_alloc_shr_aux overwrites the header with the
 * requested wosize as soon as verified_allocate returns. Promotion does not.
 * The minor->major copy reads the header the allocator wrote and rebuilds it
 * verbatim -- `wz_read = getWosize(major_hdr); makeHeader(wz_read, White, tag)`
 * -- so the promoted object declares one field more than was copied into it.
 *
 * WHY THE CHECK IS AN ASSERTION, NOT A CRASH. Because that inflated header is
 * the object's own header, Array.length reads it directly. We do not have to
 * wait for something to follow the phantom field and fault, which is what
 * makes tests/ast-invariants an unreliable detector: whether it segfaults
 * depends on the platform (it fails 100% on Fedora 44 / gcc 16 and passes 15/15
 * on ubuntu-latest, with the allocator provably broken in both). An inflated
 * length is the defect itself rather than one of its possible symptoms.
 *
 * GETTING THE ALLOCATOR TO TAKE THAT BRANCH is the whole difficulty, and two
 * things have to be arranged:
 *
 *   - The free list must be out of tail. Coalesce walks upward making each
 *     flushed block the new head, so the head is the highest-address free
 *     block -- the unallocated tail -- and first fit serves every request from
 *     it with a large leftover, never touching a fragment. So the heap is
 *     filled to `fill` first.
 *   - The collection has to actually happen. `Gc.full_major ()` does NOT drive
 *     this collector: caml_gc_full_major calls stock caml_finish_major_cycle.
 *     The verified mark/sweep/coalesce is reachable from the promotion
 *     threshold or from a failed major allocation. This uses the threshold
 *     (see force_full_collection below), so it needs no runtime-specific
 *     primitive and runs under stock OCaml as well. Without it the victims
 *     below are never swept and no fragments ever exist.
 *
 * Then: build alternating [victim wosize V][keeper] pairs in ONE array so
 * Cheney copies them in index order and they interleave; drop every victim and
 * sweep, leaving wosize-V blocks each pinned between two survivors so coalesce
 * cannot merge them; then promote objects of wosize V-1. Once the tail is
 * gone, every request lands on a wosize-V fragment, leftover is 1, and the
 * header is inflated.
 *
 * Deterministic: no randomness, no timing dependence. Identical counts run to
 * run on a given (heap, fill).
 *)

(* Force a full collection of whichever collector is running. Gc.full_major
   drives stock's collector, not the verified one, so instead churn garbage
   through the nursery: the verified runtime runs its full GC once the words
   moved through minor collections exceed half the major heap, and stock
   finishes a major cycle on the same pressure. *)
let force_full_collection () =
  let before = (Gc.quick_stat ()).Gc.major_collections in
  let sink = ref [||] in
  let rounds = ref 0 in
  while (Gc.quick_stat ()).Gc.major_collections = before do
    for _ = 1 to 1000 do sink := Array.make 64 0 done;
    Gc.minor ();
    incr rounds;
    if !rounds > 1_000_000 then (print_endline "harness error: no full collection"; exit 2)
  done;
  ignore (Sys.opaque_identity !sink)

let heap_words = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 4194304
let fill_frac  = if Array.length Sys.argv > 2 then float_of_string Sys.argv.(2) else 0.60

let victim_wz = 101             (* wosize of the blocks we free      *)
let obj_wz    = victim_wz - 1   (* wosize we then ask promotion for  *)
let keeper_wz = 8               (* survivor pinning each victim      *)

(* Both are under Max_young_wosize (256), so these are minor allocations and
   reach the major heap by promotion rather than directly. *)
let () = assert (victim_wz <= 256 && obj_wz >= 1)

let per_pair = (victim_wz + 1) + (keeper_wz + 1)
let n = int_of_float (float_of_int heap_words *. fill_frac) / per_pair

let () =
  Printf.printf
    "major heap %d words; filling %.0f%% with %d [victim wosize %d][keeper wosize %d] pairs\n%!"
    heap_words (fill_frac *. 100.) n victim_wz keeper_wz

let slots : string array array = Array.make (2 * n) [||]

let () =
  for i = 0 to n - 1 do
    slots.(2 * i)     <- Array.make victim_wz "v";
    slots.(2 * i + 1) <- Array.make keeper_wz "k"
  done;
  Gc.minor ();                                       (* promote, interleaved *)
  for i = 0 to n - 1 do slots.(2 * i) <- [||] done;  (* drop the victims *)
  let stuck = ref 0 in
  for i = 0 to n - 1 do
    if Array.length slots.(2 * i) <> 0 then incr stuck
  done;
  if !stuck > 0 then begin
    Printf.printf
      "harness error: %d/%d victim slots did not clear, so no fragments exist\n" !stuck n;
    exit 2
  end;
  force_full_collection ();                          (* the real sweep + coalesce *)
  Printf.printf "%d isolated wosize-%d free blocks; tail is what remains\n%!" n victim_wz

let m = n
let promoted : string array array = Array.make m [||]

let () =
  let i = ref 0 and batch = 2000 in
  while !i < m do
    let hi = min (!i + batch - 1) (m - 1) in
    for j = !i to hi do promoted.(j) <- Array.make obj_wz "p" done;
    Gc.minor ();                                     (* the allocations under test *)
    i := hi + 1
  done

let () =
  (* Both directions. The bug inflates, but the contract is exact size, and a
     promoted object that under-declares is just as wrong -- it would hide
     fields the program wrote. Testing only `>` would report that as a pass. *)
  let wrong = ref 0 and first = ref (-1) and first_got = ref 0 in
  for j = 0 to m - 1 do
    let got = Array.length promoted.(j) in
    if got <> obj_wz then begin
      incr wrong;
      if !first < 0 then begin first := j; first_got := got end
    end
  done;
  if !wrong = 0 then begin
    Printf.printf
      "ok: %d promoted objects, every one declares exactly %d fields\n" m obj_wz;
    exit 0
  end else if !first_got > obj_wz then begin
    Printf.printf
      "FAIL: %d of %d promoted objects declare MORE fields than they own\n\
      \  first at index %d: asked for %d fields, header says %d\n\
      \n\
      \  The allocator handed over a free block %d word(s) longer than the\n\
      \  request and kept the BLOCK's size in the header; promotion copied that\n\
      \  header verbatim, so field %d of this object is not a value -- reading\n\
      \  it, or letting a collector follow it, is undefined.\n"
      !wrong m !first obj_wz !first_got (!first_got - obj_wz) obj_wz;
    exit 1
  end else begin
    Printf.printf
      "FAIL: %d of %d promoted objects declare FEWER fields than they own\n\
      \  first at index %d: asked for %d fields, header says %d\n\
      \n\
      \  Not the inflation of issue #19 but the opposite: the promoted header\n\
      \  under-declares, so fields the program wrote are outside the object and\n\
      \  a collector will not trace them.\n"
      !wrong m !first obj_wz !first_got;
    exit 1
  end
