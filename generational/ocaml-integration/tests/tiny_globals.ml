(* Bytecode startup with globals that start in the minor heap.
   ===========================================================

   At startup the bytecode runtime unmarshals the DATA section -- the global
   data array and every constant it reaches -- in one allocation
   (intern_alloc), and then must "ensure that the globals are in the major
   heap".  Stock OCaml does that with caml_oldify_one / caml_oldify_mopup,
   the stock minor collector, which must not run under the verified
   collector.  The verified runtime instead runs

       if (Is_block (caml_global_data) && Is_young (caml_global_data))
         caml_minor_collection ();

   i.e. the verified minor collection, which treats caml_global_data as a
   root (caml_do_roots) and rewrites it after promotion.

   An ordinary program never takes that branch: Stdlib alone makes the DATA
   section larger than Max_young_wosize (256 words), so it is allocated
   straight into the major heap.  This program is therefore linked WITHOUT
   the stdlib (-nostdlib -nopervasives, and an empty std_exit.ml) so that its
   DATA section is small and lands in the minor heap.  Everything it needs is
   declared as an external below.

   With TINY_GLOBALS_RUNTIME=verified it first checks, before
   allocating anything, that exactly one minor collection has already run
   and that it promoted something: that collection can only be the startup
   one.  Stock OCaml promotes the globals with caml_oldify_one, which counts
   neither, so the differential run under stock does not set it.  (The
   mode is not passed on the command line: caml_sys_argv crashes stock
   OCaml too in a program linked without the stdlib.)

   Then, under both runtimes, it uses the promoted globals: it reads the
   structured constants from DATA, stores young lists into a global array
   and a global mutable record (major -> minor pointers, through
   caml_modify), forces many minor collections, and checks every value.

   Exit status: 0 = all good; otherwise the number of the failed check. *)

external exit : int -> 'a = "caml_sys_exit"
external getenv : string -> string = "caml_sys_getenv"
external quick_stat : unit -> 'a = "caml_gc_quick_stat"
external field : 'a -> int -> 'b = "%obj_field"
external aget : 'a array -> int -> 'a = "%array_safe_get"
external aset : 'a array -> int -> 'a -> unit = "%array_safe_set"
external string_length : string -> int = "%string_length"
external ( + ) : int -> int -> int = "%addint"
external ( - ) : int -> int -> int = "%subint"
external ( mod ) : int -> int -> int = "%modint"
external ( = ) : 'a -> 'a -> bool = "%equal"
external ( < ) : 'a -> 'a -> bool = "%lessthan"
external ( > ) : 'a -> 'a -> bool = "%greaterthan"
external not : bool -> bool = "%boolnot"
external open_out_fd : int -> 'chan = "caml_ml_open_descriptor_out"
external output : 'chan -> string -> int -> int -> unit = "caml_ml_output"
external flush : 'chan -> unit = "caml_ml_flush"

(* Gc.stat field numbers: { minor_words; promoted_words; major_words;
   minor_collections; ... }.  promoted_words is a boxed float. *)
let minor_collections () = field (quick_stat ()) 3
let promoted_words () : float = field (quick_stat ()) 1

let check n ok = if not ok then exit n

(* Structured constants: emitted into the DATA section, so they are part of
   the block that started young and was promoted at startup. *)
let constant_list = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
let constant_pair = ("tiny_globals", constant_list)

type counter = { mutable count : int; mutable last : int list }
let counter = { count = 0; last = [] }
let slots = [| []; []; []; [] |]

let rec build n acc = if n = 0 then acc else build (n - 1) (n :: acc)
let rec sum l acc = match l with [] -> acc | x :: r -> sum r (acc + x)

let rec rounds i =
  if i > 0 then begin
    let young = build 100 [] in
    aset slots (i mod 4) young;          (* major -> minor, caml_modify *)
    counter.count <- counter.count + 1;
    counter.last <- young;
    let _garbage = build 1000 [] in      (* fills the minor heap *)
    rounds (i - 1)
  end

let () =
  (* Nothing before these two checks can trigger a collection. *)
  if (try getenv "TINY_GLOBALS_RUNTIME" with _ -> "") = "verified" then begin
    check 2 (minor_collections () = 1);
    check 3 (promoted_words () > 0.0)
  end;
  let (name, l) = constant_pair in
  check 4 (string_length name = 12);
  check 5 (sum l 0 = 55);
  check 6 (sum constant_list 0 = 55);
  let before = minor_collections () in
  rounds 2000;
  check 7 (minor_collections () > before + 4);
  check 8 (counter.count = 2000);
  check 9 (sum counter.last 0 = 5050);
  let rec all_slots i =
    if i < 4 then begin
      check (10 + i) (sum (aget slots i) 0 = 5050);
      all_slots (i + 1)
    end
  in
  all_slots 0;
  check 20 (sum constant_list 0 = 55);
  let out = open_out_fd 1 in
  let msg = "tiny_globals: all checks passed\n" in
  output out msg 0 (string_length msg);
  flush out
