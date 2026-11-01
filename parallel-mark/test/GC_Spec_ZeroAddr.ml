(* Test realisation of GC.Spec.ZeroAddr (an interface whose implementation is
   C in the real collector).  zero_addr = 2048, as zero_addr_above_minor_size
   requires; the heap holds PS_WORDS words after it.  The .fsti's
   requirements (heap_size % 8 = 0, >= 16, < 2^57; zero_addr % 8 = 0,
   zero_addr + 8 < heap_size) hold for PS_WORDS >= 2.  heap_size is the
   .fsti's own definition, U64.v heap_size_u64, which Custard leaves to the
   implementation because the .fsti marks it noextract. *)
let words =
  match Sys.getenv_opt "PS_WORDS" with
  | Some s -> int_of_string s
  | None -> 32
let () = if words < 2 then failwith "PS_WORDS must be >= 2"
let zero_addr = Stdint.Uint64.of_int 2048
let heap_size_u64 = Stdint.Uint64.of_int (2048 + 8 * words)
let heap_size = FStar_UInt64.v heap_size_u64
