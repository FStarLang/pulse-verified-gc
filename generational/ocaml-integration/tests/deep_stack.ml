(* Issue #41: more live roots than the old fixed root buffer held.

   alloc_gen.c used to copy every root into a fixed array of MAX_ROOTS = 2^18
   slots and abort with "verified gen GC: root overflow" when one more arrived.
   A deep, non-tail recursion that keeps a few blocks live in each frame has
   more pointer slots than that on its stack, while stock OCaml runs it within
   its default stack limit (Sandmark's stacks and lazylist did exactly this).

   Each frame below keeps three blocks live across the recursive call: [a],
   [b] and [c].  At depth 100_000 that is over 300K block-valued stack slots
   (plus the closure in each bytecode frame).  The descent allocates, so minor
   collections run with the stack ever deeper, and the deepest frame forces a
   minor collection and a full collection.  Run with a heap of 2M words, the
   full collection's gray stack would be 2M / 8 = 262,144 entries, fewer than
   the roots, so the bridge has to size it from the root count to keep
   gen_gc_stack_budget (nroots <= capacity).

   On the way back up, every frame checks that its values survived. *)

let depth = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 100_000

let minor_at_bottom = ref 0
let major_at_bottom = ref 0

let rec go n =
  if n = 0 then begin
    let s0 = Gc.quick_stat () in
    (* Fill the nursery a few times over (about 1M words of small blocks,
       each below Max_young_wosize) so minor collections run here. *)
    for _ = 1 to 10_000 do
      ignore (Sys.opaque_identity (Array.make 100 n))
    done;
    Gc.full_major ();
    let s1 = Gc.quick_stat () in
    minor_at_bottom := s1.Gc.minor_collections - s0.Gc.minor_collections;
    major_at_bottom := s1.Gc.major_collections - s0.Gc.major_collections;
    0
  end else begin
    let a = ref n in
    let b = Some a in
    let c = [n; n + 1] in
    let below = go (n - 1) in
    (match b with
     | Some a' when a' == a && !a = n -> ()
     | _ -> failwith (Printf.sprintf "frame %d: a or b corrupted" n));
    (match c with
     | [x; y] when x = n && y = n + 1 -> ()
     | _ -> failwith (Printf.sprintf "frame %d: c corrupted" n));
    below + 1
  end

let () =
  let frames = go depth in
  if frames <> depth then failwith "wrong frame count";
  (* The full collection counts as one minor collection; ask for more. *)
  if !minor_at_bottom < 2 then failwith "no minor collection at the deepest frame";
  if !major_at_bottom < 1 then failwith "no full collection at the deepest frame";
  Printf.printf "deep_stack: %d frames, %d minor and %d major collections at the bottom: OK\n"
    frames !minor_at_bottom !major_at_bottom
