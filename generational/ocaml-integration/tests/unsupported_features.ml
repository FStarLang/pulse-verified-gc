(* Issues #42 and #43: features the verified collector does not implement
   stop the program at once, with a clear message.

   Usage: unsupported_features.byte (weak | ephemeron | finalise | finalise_last)

   Each mode first checks that an invalid argument still raises
   Invalid_argument (only a real creation or registration stops the program),
   then prints "before", uses the feature, and prints "after".  Under stock
   OCaml it prints both and exits 0.  Under the verified runtime it must stop
   between the two with

     Fatal error: <feature> not supported by the verified GC (<function>)

   and a non-zero exit code; tests/check_unsupported.sh checks that. *)

let expect_invalid_arg name f =
  match f () with
  | _ -> failwith (name ^ ": expected Invalid_argument")
  | exception Invalid_argument _ -> ()

let () =
  let mode = if Array.length Sys.argv > 1 then Sys.argv.(1) else "" in
  let use =
    match mode with
    | "weak" ->
        expect_invalid_arg "Weak.create (-1)" (fun () -> ignore (Weak.create (-1)));
        fun () ->
          let w = Weak.create 4 in
          Weak.set w 0 (Some (ref 1));
          ignore (Sys.opaque_identity w)
    | "ephemeron" ->
        fun () ->
          let module T = Ephemeron.K1.Make (struct
            type t = int ref
            let equal = ( == )
            let hash = Hashtbl.hash
          end) in
          let t = T.create 16 in
          T.add t (ref 1) "one";
          ignore (Sys.opaque_identity t)
    | "finalise" ->
        expect_invalid_arg "Gc.finalise on an int"
          (fun () -> Gc.finalise (fun _ -> ()) (Sys.opaque_identity 42));
        fun () -> Gc.finalise (fun _ -> ()) (ref 1)
    | "finalise_last" ->
        fun () -> Gc.finalise_last (fun () -> ()) (ref 1)
    | _ -> prerr_endline "usage: weak | ephemeron | finalise | finalise_last"; exit 64
  in
  print_endline "before";
  use ();
  print_endline "after"
