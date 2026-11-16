(* Obj.truncate under the verified collector.
   ===========================================

   Stock OCaml shrinks a block in place and turns the leftover words into a
   black block, so that it is not reused before the ref table is emptied.
   The verified collector's invariants have no account of such a block (an
   idle verified heap admits no black object, and a block behind the sweep
   cursor is never whitened), so the verified runtime does not support
   Obj.truncate: it raises Invalid_argument, whatever the block, and leaves
   the block unchanged.  OCaml 5 removed Obj.truncate altogether.

   With OBJ_TRUNCATE_RUNTIME=verified: truncating a young block and a major
   block each raises Invalid_argument "Obj.truncate: not supported by the
   verified GC", the blocks keep their size and contents, and they survive a
   full collection.  Otherwise (stock OCaml, the differential check): the
   truncations succeed and shrink the blocks.

   Exits 1 if any check fails. *)

[@@@ocaml.warning "-3"]   (* Obj.truncate is deprecated *)

let verified =
  match Sys.getenv_opt "OBJ_TRUNCATE_RUNTIME" with
  | Some "verified" -> true
  | _ -> false

let failures = ref 0

let check name ok =
  if not ok then begin
    Printf.printf "FAIL: %s\n%!" name;
    incr failures
  end

let message = "Obj.truncate: not supported by the verified GC"

(* Truncate [a] to [n] fields; under the verified runtime this must raise. *)
let try_truncate name (a : int array) n =
  let len = Array.length a in
  match Obj.truncate (Obj.repr a) n with
  | () ->
      check (name ^ ": truncation should raise under the verified GC") (not verified);
      check (name ^ ": truncated length") (Array.length a = n)
  | exception Invalid_argument m ->
      check (name ^ ": stock should truncate") verified;
      check (name ^ ": message") (m = message);
      check (name ^ ": length unchanged") (Array.length a = len)

let () =
  (* A young block, and a block too large for the nursery (allocated in the
     major heap). *)
  let young = Array.init 8 (fun i -> i) in
  let major = Array.init 100_000 (fun i -> i) in
  try_truncate "young" young 4;
  try_truncate "major" major 10;
  Gc.full_major ();
  let ok_contents a = Array.for_all (fun x -> x >= 0) a
                      && (Array.length a = 0 || a.(0) = 0) in
  check "young contents" (ok_contents young);
  check "major contents" (ok_contents major);
  if verified then begin
    check "young size kept" (Array.length young = 8 && young.(7) = 7);
    check "major size kept" (Array.length major = 100_000 && major.(99_999) = 99_999)
  end;
  if !failures > 0 then exit 1;
  print_endline "obj_truncate: ok"
