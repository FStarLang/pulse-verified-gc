(* The parallel sweep across fork (docs/parallel-sweep-phase1.md, §9, Stage 3,
   step 5).  Major collections happen in the parent before fork, in the child,
   and in the parent after the child has exited.  The child has no worker
   threads; it must fall back to the sequential driver, not wait for workers.

   Exit 0 when the child and the parent each did at least one major collection
   after the fork and every retained value is intact. *)

let majors () = (Gc.quick_stat ()).Gc.major_collections

(* Survives every collection; checked after each phase. *)
let live = Array.init 2000 (fun i -> Array.make 20 i)

let check where =
  Array.iteri (fun i a ->
      Array.iter (fun x -> if x <> i then begin
          Printf.printf "%s: retained value corrupted\n%!" where; exit 2 end) a)
    live

(* Objects that survive long enough to be promoted, then die: major garbage. *)
let ring = Array.make 2000 [||]
let churn n =
  for i = 1 to n do ring.(i mod 2000) <- Array.make 30 i done;
  Array.iteri (fun j a -> if Array.length a > 0 && a.(0) mod 2000 <> j then begin
      print_string "ring corrupted\n"; exit 2 end) ring

let () =
  churn 300_000; check "parent, before fork";
  let before = majors () in
  match Unix.fork () with
  | 0 ->
      churn 300_000; check "child";
      let m = majors () - before in
      Printf.printf "child: %d major collections after fork\n%!" m;
      exit (if m > 0 then 0 else 3)
  | pid ->
      let _, st = Unix.waitpid [] pid in
      let at = majors () in
      churn 300_000; check "parent, after fork";
      let m = majors () - at in
      Printf.printf "parent: %d major collections before fork, %d after the child\n%!" before m;
      (match st with
       | Unix.WEXITED 0 when m > 0 -> print_string "ok: fork\n"; exit 0
       | Unix.WEXITED c -> Printf.printf "FAIL: child exit %d\n" c; exit 1
       | _ -> print_string "FAIL: child killed\n"; exit 1)
