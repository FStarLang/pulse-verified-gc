(* Stage B: compare the extracted GC.Spec.SweepPar.sweep_par with the
   extracted GC.Spec.SweepPar.Exec.fused_sweep_coalesce_x (which F* proves
   equal to GC.Spec.SweepCoalesce.Defs.fused_sweep_coalesce).

     sweep_par_test hand              hand-built cases
     sweep_par_test random SEED N     N generated heaps

   The heap size is fixed per process (PS_WORDS, see GC_Spec_ZeroAddr.ml).
   The first mismatch stops the run with exit 1 and a full description. *)

module U64 = Stdint.Uint64
module Seq = FStar_Seq_Base
module H = GC_Lib_Header
module SP = GC_Spec_SweepPar

let zero = U64.to_int GC_Spec_Base.zero_addr
let hsize = Z.to_int GC_Spec_Base.heap_size
let words = (hsize - zero) / 8

(* ------------------------------------------------------------------ *)
(* Heap construction                                                   *)
(* ------------------------------------------------------------------ *)

type obj = { wz : int; color : H.color_sem; tag : int; mutable fields : U64.t array }

let color_name = function H.White -> "W" | H.Gray -> "G" | H.Blue -> "U" | H.Black -> "B"

(* Lay objects out from zero_addr; returns header addresses. *)
let layout (objs : obj list) =
  let rec go a = function [] -> [] | o :: r -> a :: go (a + 8 * (o.wz + 1)) r in
  go zero objs

let write_bytes (b : int array) a (v : U64.t) =
  for k = 0 to 7 do
    b.(a + k) <- U64.to_int (U64.logand (U64.shift_right v (8 * k)) (U64.of_int 255))
  done

let build (objs : obj list) : GC_Spec_Base.heap =
  let total = List.fold_left (fun s o -> s + o.wz + 1) 0 objs in
  if total <> words then failwith (Printf.sprintf "build: %d words, heap has %d" total words);
  let b = Array.make hsize 0 in
  let hs = layout objs in
  List.iter2 (fun a o ->
      let hdr = GC_Spec_Object.makeHeader (U64.of_int o.wz) o.color (U64.of_int o.tag) in
      write_bytes b a hdr;
      Array.iteri (fun i v -> write_bytes b (a + 8 * (i + 1)) v) o.fields)
    hs objs;
  let g = Seq.seq_of_list (Array.to_list b) in
  (* The extracted reader must see exactly the headers we meant. *)
  List.iter2 (fun a o ->
      let h = GC_Spec_Heap.read_word g (U64.of_int a) in
      if U64.to_int (GC_Spec_Object.getWosize h) <> o.wz
         || GC_Spec_Object.getColor h <> o.color then failwith "build: header mismatch")
    hs objs;
  g

(* ------------------------------------------------------------------ *)
(* The precondition, as far as it can be executed                      *)
(* ------------------------------------------------------------------ *)

let objects g = List.map U64.to_int (Seq.seq_to_list (GC_Spec_SweepPar_Exec.objects_x GC_Spec_Base.zero_addr g))

let hdr_of g o = GC_Spec_Heap.read_word g (U64.of_int (o - 8))

(* well_formed_heap parts 1-4, objects nonempty, density, no gray.
   Part 2/3 are checked in the form the generator guarantees: every field of
   a scannable object that is_pointer_field is the address of an object. *)
let pre_ok g =
  let objs = objects g in
  let set = Hashtbl.create 64 in
  List.iter (fun o -> Hashtbl.replace set o ()) objs;
  let ok = ref (objs <> []) in
  List.iter (fun o ->
      let h = hdr_of g o in
      let wz = U64.to_int (GC_Spec_Object.getWosize h) in
      let tag = U64.to_int (GC_Spec_Object.getTag h) in
      if o - 8 + 8 + 8 * wz > hsize then ok := false;              (* part 1 *)
      if tag = 249 then ok := false;                               (* part 4 *)
      if GC_Spec_Object.getColor h = H.Gray then ok := false;      (* no gray *)
      if tag < 251 then                                            (* part 2/3 *)
        for i = 0 to wz - 1 do
          let v = GC_Spec_Heap.read_word g (U64.of_int (o + 8 * i)) in
          if GC_Spec_Fields.is_pointer_field v && not (Hashtbl.mem set (U64.to_int v)) then ok := false
        done;
      (* density: a successor with room for a header is an object *)
      let next = o - 8 + 8 * (wz + 1) in
      if next + 8 < hsize && not (Hashtbl.mem set (next + 8)) then ok := false)
    objs;
  !ok

(* Walk positions from zero_addr, including a final wosize-0 header that the
   object list does not enumerate. *)
let walk_positions g =
  let rec go s acc =
    if s + 8 >= hsize then List.rev (s :: acc)
    else
      let wz = U64.to_int (GC_Spec_Object.getWosize (GC_Spec_Heap.read_word g (U64.of_int s))) in
      let next = s + 8 * (wz + 1) in
      if next >= hsize then List.rev (s :: acc) else go next (s :: acc)
  in
  go zero []

(* ------------------------------------------------------------------ *)
(* Comparison                                                          *)
(* ------------------------------------------------------------------ *)

let zl = List.map Z.of_int
let bs_of interior = zl ((zero :: interior) @ [hsize])

type stats = {
  mutable heaps : int; mutable cases : int; mutable segs : int; mutable max_segs : int;
  mutable cross1 : int;      (* runs crossing exactly one boundary *)
  mutable crossn : int;      (* runs crossing two or more boundaries *)
  mutable all_free : int;    (* all-free segments *)
  mutable frag_bd : int;     (* wosize-0 fragment next to a boundary *)
  mutable patched : int;     (* segments whose first link was patched *)
  mutable patched_nz : int;  (*   ... with a nonzero head *)
  mutable first_bd : int; mutable last_bd : int; mutable end_bd : int;
  mutable rejected : int;    (* invalid bs correctly rejected *)
  mutable mut_seen : int array;
}

let st = { heaps = 0; cases = 0; segs = 0; max_segs = 0; cross1 = 0; crossn = 0;
           all_free = 0; frag_bd = 0; patched = 0; patched_nz = 0;
           first_bd = 0; last_bd = 0; end_bd = 0; rejected = 0;
           mut_seen = Array.make 5 0 }

let describe g interior =
  let objs = objects g in
  let b = Buffer.create 256 in
  Buffer.add_string b (Printf.sprintf "heap: zero_addr=%d heap_size=%d (%d words)\n" zero hsize words);
  List.iter (fun s ->
      let h = GC_Spec_Heap.read_word g (U64.of_int s) in
      Buffer.add_string b (Printf.sprintf "  hdr @%d (w%d): wz=%d %s tag=%d%s%s\n" s ((s - zero) / 8)
        (U64.to_int (GC_Spec_Object.getWosize h)) (color_name (GC_Spec_Object.getColor h))
        (U64.to_int (GC_Spec_Object.getTag h))
        (if List.mem s interior then "   <-- boundary" else "")
        (if List.mem (s + 8) objs then "" else "   (not enumerated)")))
    (walk_positions g);
  Buffer.add_string b (Printf.sprintf "bs: %s\n"
    (String.concat "; " (List.map string_of_int ((zero :: interior) @ [hsize]))));
  Buffer.contents b

let first_diff (a : int list) (b : int list) =
  let rec go i = function
    | x :: xs, y :: ys -> if x <> y then Some i else go (i + 1) (xs, ys)
    | _ -> None in
  go 0 (a, b)

let bytes h = Seq.seq_to_list h

let word_at l a =
  let r = ref 0 in
  for k = 7 downto 0 do r := (!r lsl 8) lor List.nth l (a + k) done; !r

let fail g interior (hs, fs) (hp, fpp) =
  print_string "MISMATCH: sweep_par bs g <> fused_sweep_coalesce g\n";
  print_string (describe g interior);
  Printf.printf "free-list head: sequential %s, parallel %s\n" (U64.to_string fs) (U64.to_string fpp);
  (match first_diff (bytes hs) (bytes hp) with
   | None -> print_string "heaps equal\n"
   | Some i ->
     let a = i land (lnot 7) in
     Printf.printf "heaps differ first at byte %d (word @%d): sequential %x, parallel %x\n"
       i a (word_at (bytes hs) a) (word_at (bytes hp) a));
  exit 1

(* Coverage of the interesting shapes, read off the segment outputs. *)
let note g interior =
  let rs = SP.sweep_all g (SP.segments (bs_of interior)) in
  let n = List.length rs in
  st.segs <- st.segs + n; st.max_segs <- max st.max_segs n;
  let out (r : SP.seg_raw) = r.SP.out in
  (* runs that cross boundaries: count boundaries spanned by each run *)
  let span = ref 0 in
  let close () = if !span = 1 then st.cross1 <- st.cross1 + 1
                 else if !span >= 2 then st.crossn <- st.crossn + 1; span := 0 in
  let carry = ref false in
  List.iter (fun r ->
      let o = out r in
      if o.SP.all_free then begin
        st.all_free <- st.all_free + 1;
        if !carry && Z.to_int o.SP.lead.SP.rw > 0 then incr span;
        if Z.to_int o.SP.lead.SP.rw > 0 then carry := true
      end else begin
        if !carry && Z.to_int o.SP.lead.SP.rw > 0 then incr span;
        close ();
        (match o.SP.first_link with Some _ -> st.patched <- st.patched + 1 | None -> ());
        carry := Z.to_int o.SP.trail.SP.rw > 0
      end;
      if Z.to_int o.SP.lead.SP.rw = 1 || Z.to_int o.SP.trail.SP.rw = 1 then st.frag_bd <- st.frag_bd + 1)
    rs;
  close ();
  (* a patch with a nonzero head: some earlier free block exists *)
  let head = ref false in
  List.iter (fun r ->
      let o = out r in
      if (match o.SP.first_link with Some _ -> true | None -> false) && !head then
        st.patched_nz <- st.patched_nz + 1;
      if Z.to_int o.SP.lead.SP.rw > 1 || (match o.SP.first_link with Some _ -> true | None -> false) then head := true)
    rs;
  let ps = walk_positions g in
  (match ps with _ :: p1 :: _ when List.mem p1 interior -> st.first_bd <- st.first_bd + 1 | _ -> ());
  let objs = objects g in
  let last = List.nth objs (List.length objs - 1) - 8 in
  if List.mem last interior then st.last_bd <- st.last_bd + 1;
  if List.mem (hsize - 8) interior && not (List.mem hsize objs) then st.end_bd <- st.end_bd + 1

let check g interior =
  let bs = bs_of interior in
  if not (SP.valid_bounds g bs) then begin
    print_string "harness error: generated bs rejected by valid_bounds\n";
    print_string (describe g interior); exit 2
  end;
  let s = GC_Spec_SweepPar_Exec.fused_sweep_coalesce_x g in
  let p = SP.sweep_par bs g in
  let eq (h1, f1) (h2, f2) = bytes h1 = bytes h2 && U64.compare f1 f2 = 0 in
  if not (eq s p) then fail g interior s p;
  if not (eq p (GC_Spec_SweepPar_Mutants.sweep_par_m Z.zero bs g)) then begin
    print_string "harness error: mutant 0 differs from sweep_par\n"; exit 2 end;
  for m = 1 to 4 do
    if not (eq s (GC_Spec_SweepPar_Mutants.sweep_par_m (Z.of_int m) bs g)) then
      st.mut_seen.(m) <- st.mut_seen.(m) + 1
  done;
  st.cases <- st.cases + 1;
  note g interior

(* Boundaries that are not walk positions, or are out of order, must be
   rejected: otherwise the theorem's hypothesis would admit them. *)
let check_rejects g =
  let ps = List.tl (walk_positions g) in
  let bad = ref [] in
  for w = 1 to words - 1 do
    let a = zero + 8 * w in
    if not (List.mem a ps) then bad := [a] :: !bad
  done;
  (match ps with
   | a :: b :: _ -> bad := [b; a] :: [a; a] :: !bad
   | _ -> ());
  bad := [zero] :: !bad;
  List.iter (fun interior ->
      if SP.valid_bounds g (bs_of interior) then begin
        print_string "harness error: invalid bs accepted by valid_bounds\n";
        print_string (describe g interior); exit 2
      end else st.rejected <- st.rejected + 1)
    !bad;
  (* missing endpoints *)
  if SP.valid_bounds g (zl [zero]) || SP.valid_bounds g (zl [zero; hsize - 8])
     || SP.valid_bounds g (zl [hsize]) then begin
    print_string "harness error: bs without both endpoints accepted\n"; exit 2 end

(* All boundary sets of size <= k over the interior walk positions; all
   subsets when there are few positions. *)
let rec subsets_upto k = function
  | [] -> [ [] ]
  | x :: r ->
    let without = subsets_upto k r in
    if k = 0 then without
    else List.map (fun s -> x :: s) (subsets_upto (k - 1) r) @ without

let boundary_sets ps =
  let n = List.length ps in
  if n <= 10 then subsets_upto n ps else subsets_upto 2 ps @ [ ps ]

let run_heap ?(sets = None) g =
  if not (pre_ok g) then begin
    print_string "harness error: heap does not meet the precondition\n";
    print_string (describe g []); exit 2
  end;
  st.heaps <- st.heaps + 1;
  check_rejects g;
  let ps = List.tl (walk_positions g) in
  let sets = match sets with Some s -> s | None -> boundary_sets ps in
  List.iter (check g) sets

(* ------------------------------------------------------------------ *)
(* Hand-built cases                                                    *)
(* ------------------------------------------------------------------ *)

let mk wz color = { wz; color; tag = 0; fields = Array.make wz (U64.of_int 1) }
let b n = mk n H.Black
let w n = mk n H.White
let u n = mk n H.Blue

(* A case is a list of items: objects, and `Bd` before an object to put a
   boundary at its header.  The heap is padded to PS_WORDS with one object
   of colour `pad` (wosize 0 if a single word remains). *)
type item = O of obj | Bd

let hand name ?(pad = H.Black) items =
  let objs = List.filter_map (function O o -> Some o | Bd -> None) items in
  let used = List.fold_left (fun s o -> s + o.wz + 1) 0 objs in
  if used > words then failwith ("hand case too big: " ^ name);
  let objs = if used = words then objs else objs @ [ mk (words - used - 1) pad ] in
  (* boundary addresses *)
  let rec bds a = function
    | [] -> []
    | Bd :: r -> a :: bds a r
    | O o :: r -> bds (a + 8 * (o.wz + 1)) r in
  let interior = bds zero items in
  let g = build objs in
  Printf.printf "  %-58s " name;
  let before = st.cases in
  (* the stated boundaries, plus every set of up to 2 walk positions *)
  let ps = List.tl (walk_positions g) in
  run_heap ~sets:(Some (interior :: subsets_upto 2 ps)) g;
  Printf.printf "%5d bs ok\n" (st.cases - before)

let hand_cases () =
  print_string "hand-built cases\n";
  hand "run crossing one boundary" [ O (b 1); O (w 1); O (w 2); Bd; O (w 1); O (u 2); O (b 1) ];
  hand "run crossing several boundaries"
    [ O (b 1); O (w 1); Bd; O (w 2); Bd; O (u 1); O (w 0); Bd; O (w 1); Bd; O (w 1); O (b 2) ];
  hand "wosize-0 fragment ending a segment" [ O (b 1); O (w 0); Bd; O (b 1); O (w 2); O (b 1) ];
  hand "wosize-0 fragment starting a segment" [ O (b 1); Bd; O (w 0); O (b 1); O (w 1); O (b 1) ];
  hand "wosize-0 fragments on both sides (merge to rw=2)" [ O (b 1); O (w 0); Bd; O (w 0); O (b 1) ];
  hand "wosize-0 fragment alone in a segment" [ O (b 1); Bd; O (w 0); Bd; O (b 1); O (w 3) ];
  hand "interior fragment only (no link in segment)" [ O (b 1); Bd; O (b 1); O (w 0); O (b 1); Bd; O (w 1) ];
  hand "segment entirely free" [ O (b 1); Bd; O (w 1); O (u 2); O (w 0); Bd; O (b 1) ];
  hand "several consecutive all-free segments"
    [ O (b 2); O (w 1); Bd; O (w 1); Bd; O (u 0); Bd; O (w 3); Bd; O (w 1); Bd; O (b 1) ];
  hand "boundary at the first object's successor" [ O (w 1); Bd; O (b 1); O (w 1); O (b 1) ];
  hand "boundary at the last object" ~pad:H.White [ O (b 1); O (w 1); O (b 1); O (w 2); Bd ];
  hand "boundary at the last object (black)" [ O (b 1); O (w 1); O (b 1); O (w 2); Bd ];
  hand "heap entirely free, many segments" ~pad:H.White
    [ O (w 1); Bd; O (w 0); Bd; O (u 2); Bd; O (w 1); Bd; O (w 0) ];
  hand "heap entirely live, many segments" [ O (b 1); Bd; O (b 0); Bd; O (b 2); Bd; O (b 1) ];
  hand "interior runs in every segment (patches chain)"
    [ O (b 1); O (w 1); O (b 1); O (w 2); Bd; O (b 1); O (w 1); O (b 1); O (u 1); Bd;
      O (w 1); O (b 1); O (w 1); O (b 1) ];
  hand "first segment has no links, later ones do"
    [ O (b 1); O (b 1); Bd; O (b 1); O (w 1); O (b 1); O (w 1); O (b 1) ];
  (* A heap whose last word is a wosize-0 header: a walk position that
     `objects` does not enumerate.  Pad by hand to leave exactly one word. *)
  let used = 2 + 2 + 3 + 2 in
  if words - used >= 2 then begin
    let fill = words - used - 1 in
    let tail = [ O (b 1); O (w 1); O (b 2); O (w 1); O (mk (fill - 1) H.Black); Bd; O (w 0) ] in
    hand "trailing unenumerated wosize-0 header as a boundary" tail
  end

(* ------------------------------------------------------------------ *)
(* Random heaps                                                        *)
(* ------------------------------------------------------------------ *)

let gen_heap rng =
  let p_black = [| 0.0; 0.1; 0.3; 0.5; 0.7; 0.9; 1.0 |].(Random.State.int rng 7) in
  let p_blue = Random.State.float rng 0.5 in
  let rec go rem acc =
    if rem = 0 then List.rev acc
    else
      let r = Random.State.int rng 100 in
      let wz = if r < 25 then 0 else if r < 50 then 1 else if r < 65 then 2
               else if r < 85 then 3 + Random.State.int rng 3 else 6 + Random.State.int rng 8 in
      let wz = min wz (rem - 1) in
      let color =
        if Random.State.float rng 1.0 < p_black then H.Black
        else if Random.State.float rng 1.0 < p_blue then H.Blue else H.White in
      let tag = [| 0; 0; 0; 1; 2; 252 |].(Random.State.int rng 6) in
      go (rem - wz - 1) ({ wz; color; tag; fields = [||] } :: acc)
  in
  let objs = go words [] in
  (* fields: non-pointers, or pointers to real objects *)
  let addrs = Array.of_list (List.map (fun a -> a + 8) (layout objs)) in
  let n_enum = Array.length addrs - (if hsize - 8 = (List.nth (layout objs) (List.length objs - 1)) then 1 else 0) in
  List.iter (fun o ->
      o.fields <- Array.init o.wz (fun _ ->
          if o.tag >= 251 then U64.of_int (Random.State.bits rng)
          else match Random.State.int rng 3 with
            | 0 -> U64.of_int (2 * Random.State.int rng 1000 + 1)
            | 1 when n_enum > 0 -> U64.of_int addrs.(Random.State.int rng n_enum)
            | _ -> U64.zero))
    objs;
  objs

let random_cases seed n =
  Printf.printf "random heaps: seed %d, %d heaps of %d words\n" seed n words;
  let rng = Random.State.make [| seed; words |] in
  for _ = 1 to n do
    let objs = gen_heap rng in
    let g = build objs in
    let ps = List.tl (walk_positions g) in
    let sets =
      if List.length ps <= 6 then subsets_upto 6 ps
      else
        (* singletons, all positions, all pairs on smaller heaps, and 24
           random subsets of varying density *)
        (List.map (fun p -> [ p ]) ps) @ [ ps ]
        @ (if List.length ps <= 10 then List.filter (fun s -> List.length s = 2) (subsets_upto 2 ps) else [])
        @ List.init 24 (fun _ ->
            let d = 0.05 +. Random.State.float rng 0.6 in
            List.filter (fun _ -> Random.State.float rng 1.0 < d) ps) in
    run_heap ~sets:(Some sets) g
  done

let report () =
  Printf.printf "ok: %d heaps, %d (heap, bs) pairs, %d segments (max %d per bs)\n"
    st.heaps st.cases st.segs st.max_segs;
  Printf.printf "  runs crossing 1 boundary: %d, crossing >= 2: %d\n" st.cross1 st.crossn;
  Printf.printf "  all-free segments: %d, wosize-0 fragment at a boundary: %d\n" st.all_free st.frag_bd;
  Printf.printf "  first-link patches: %d (nonzero head: %d)\n" st.patched st.patched_nz;
  Printf.printf "  boundary at 2nd object: %d, at last object: %d, at unenumerated end header: %d\n"
    st.first_bd st.last_bd st.end_bd;
  Printf.printf "  invalid bs rejected: %d\n" st.rejected;
  Printf.printf "  mutants detected (pairs where the mutant differs): %s\n"
    (String.concat ", " (List.map (fun m -> Printf.sprintf "m%d=%d" m st.mut_seen.(m)) [1; 2; 3; 4]))

let () =
  (match Array.to_list Sys.argv with
   | [ _; "hand" ] -> hand_cases ()
   | [ _; "random"; seed; n ] -> random_cases (int_of_string seed) (int_of_string n)
   | _ -> prerr_endline "usage: sweep_par_test hand | random SEED N"; exit 2);
  report ()
