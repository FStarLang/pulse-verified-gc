(* The write barrier (caml_modify, caml_initialize, caml_array_fill), from
   the program's side.
   ========================================================================

   Under the verified runtime every store into a field of a major block goes
   through the verified barrier (GC.Gen.Impl.Barrier.modify_field /
   initialize_field, via verified_gc/alloc_gen.c), which writes the field and
   says whether the slot must go into the remembered set (the ref table).  A
   slot left out of the table while it holds a nursery pointer is not
   rewritten by the next minor collection: the field then dangles into the
   reset nursery, and the checks below see garbage (or the program crashes).
   A slot put into the table that is not a field is rewritten when it should
   not be.

   Each section stores into old (major) blocks in the patterns the barrier
   distinguishes -- a young value over an old one, over an immediate, over a
   young one; an old value over a young one; the same field young ->
   immediate -> young (the slot is recorded twice); a whole range at once
   (Array.fill); blits and copies -- runs minor and major collections in
   between, and checks every field against a model.  This file runs
   unchanged on stock OCaml and the Makefile compares the outputs byte for
   byte.  Deterministic: a fixed PRNG seed. *)

let failures = ref 0

let check name ok =
  if not ok then begin
    incr failures;
    Printf.printf "  FAIL  %s\n%!" name
  end

let rng = Random.State.make [| 7 |]
let rand n = Random.State.int rng n

(* An old block: an array longer than Max_young_wosize is born major. *)
let old_len = 1000

(* A young value that knows its key. *)
let young k = (k, string_of_int k)
let young_ok k (k', s) = k = k' && s = string_of_int k

(* Nursery garbage, to force minor collections. *)
let churn n =
  let r = ref [] in
  for i = 1 to n do r := (i, i) :: (if i mod 64 = 0 then [] else !r) done;
  ignore (Sys.opaque_identity !r)

(* 1. Young values over every kind of old field content, many minor
   collections in between.  The model is the key stored in each field, or -1
   for an immediate. *)
let section_kinds () =
  let a : (int * string) option array = Array.make old_len None in
  let model = Array.make old_len (-1) in
  let olds = Array.init 20 (fun i -> Some (young (1_000_000 + i))) in
  Gc.minor ();
  for round = 1 to 400 do
    for _ = 1 to 50 do
      let i = rand old_len in
      let k = round * old_len + i in
      (match rand 4 with
       | 0 -> a.(i) <- Some (young k); model.(i) <- k              (* young *)
       | 1 -> a.(i) <- None; model.(i) <- -1                        (* immediate *)
       | 2 -> let j = rand 20 in a.(i) <- olds.(j); model.(i) <- 1_000_000 + j  (* old *)
       | _ -> a.(i) <- Some (young k); a.(i) <- None;              (* young -> imm -> young *)
              a.(i) <- Some (young k); model.(i) <- k)
    done;
    churn 20_000;
    if round mod 100 = 0 then Gc.full_major ();
    Array.iteri (fun i v ->
        match v with
        | None -> if model.(i) <> -1 then check (Printf.sprintf "kinds: %d None" i) false
        | Some p -> if not (young_ok model.(i) p) then
                      check (Printf.sprintf "kinds: field %d" i) false)
      a
  done;
  Printf.printf "kinds: ok\n%!"

(* 2. Array.fill (caml_array_fill's own copy of the barrier) of an old array
   with a young value, an old one and an immediate. *)
let section_fill () =
  let a : (int * string) option array = Array.make old_len None in
  let model = Array.make old_len (-1) in
  let keep = Some (young 77) in
  Gc.minor ();
  for round = 1 to 300 do
    let ofs = rand (old_len - 1) in
    let len = 1 + rand (old_len - ofs) in
    let k = round in
    (match rand 3 with
     | 0 -> Array.fill a ofs len (Some (young k)); Array.fill model ofs len k
     | 1 -> Array.fill a ofs len keep; Array.fill model ofs len 77
     | _ -> Array.fill a ofs len None; Array.fill model ofs len (-1));
    churn 15_000;
    Array.iteri (fun i v ->
        match v with
        | None -> if model.(i) <> -1 then check (Printf.sprintf "fill: %d None" i) false
        | Some p -> if not (young_ok model.(i) p) then
                      check (Printf.sprintf "fill: field %d" i) false)
      a
  done;
  Printf.printf "fill: ok\n%!"

(* 3. Blits and copies into an old array from young and old arrays
   (caml_array_blit uses caml_modify for a major destination), and
   Array.append / Array.sub of old arrays (caml_initialize into a new major
   block). *)
let section_blit () =
  let a : (int * string) array = Array.init old_len young in
  let model = Array.init old_len (fun i -> i) in
  Gc.minor ();
  for round = 1 to 200 do
    let n = 1 + rand 200 in
    let src = Array.init n (fun j -> young (round * 10_000 + j)) in
    let dst = rand (old_len - n) in
    Array.blit src 0 a dst n;
    for j = 0 to n - 1 do model.(dst + j) <- round * 10_000 + j done;
    if round mod 10 = 0 then begin
      (* an old-to-old blit within the array *)
      let s = rand (old_len - 100) and d = rand (old_len - 100) in
      Array.blit a s a d 100;
      Array.blit model s model d 100
    end;
    churn 15_000;
    let b = Array.append a (Array.sub a 0 10) in
    if Array.length b <> old_len + 10 then check "blit: append length" false;
    Array.iteri (fun i p ->
        let k = if i < old_len then model.(i) else model.(i - old_len) in
        if not (young_ok k p) then check (Printf.sprintf "blit: field %d" i) false)
      b
  done;
  Printf.printf "blit: ok\n%!"

(* 4. Records and refs promoted to the major heap and then mutated: a mutable
   field of an old record, Obj.set_field, a lazy value forced (it becomes a
   forward to its value), and a Hashtbl that resizes. *)
type cell = { mutable v : (int * string); mutable next : cell option }

let section_records () =
  let cells = Array.init 500 (fun i -> { v = young i; next = None }) in
  Gc.full_major ();                  (* the cells are old now *)
  let model = Array.init 500 (fun i -> i) in
  let lz = Array.init 500 (fun i -> lazy (young (i * 3))) in
  let h = Hashtbl.create 16 in
  for round = 1 to 300 do
    for _ = 1 to 40 do
      let i = rand 500 in
      let k = round * 500 + i in
      if rand 2 = 0 then cells.(i).v <- young k
      else Obj.set_field (Obj.repr cells.(i)) 0 (Obj.repr (young k));
      model.(i) <- k;
      cells.(i).next <- Some cells.(rand 500);
      Hashtbl.replace h (rand 2000) (young k)
    done;
    ignore (Lazy.force lz.(rand 500));
    churn 20_000;
    Array.iteri (fun i c ->
        if not (young_ok model.(i) c.v) then check (Printf.sprintf "records: cell %d" i) false)
      cells
  done;
  Array.iteri (fun i l -> if not (young_ok (i * 3) (Lazy.force l)) then
                            check (Printf.sprintf "records: lazy %d" i) false) lz;
  Hashtbl.iter (fun _ p -> let (k, s) = p in if s <> string_of_int k then
                             check "records: hashtbl" false) h;
  Printf.printf "records: ok (%d bindings)\n%!" (Hashtbl.length h)

let () =
  section_kinds ();
  section_fill ();
  section_blit ();
  section_records ();
  if !failures = 0 then print_endline "write_barrier: all checks passed"
  else (Printf.printf "write_barrier: %d failures\n" !failures; exit 1)
