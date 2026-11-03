# Sandmark on the verified OCaml 4.14 runtime

The sequential Sandmark benchmarks (github.com/ocaml-bench/sandmark, commit
`5605805954a00497ed197c930641cddd580e1507`, Aug 2024) that build with the stock
4.14 `ocamlc` and run correctly on the verified generational GC's bytecode
runtime, for docs/parallel-mark-prototype2.md.  `build.sh` clones Sandmark into
`../../_build/sandmark` (if absent) and compiles them into `bin/` (ignored by
git); `benchmarks.txt` lists them as `name|binary|heap_words|args|notes`, to be
run with `bin/` as the working directory (`../parmark2_bench.sh` does this for
`sm:<name>`).

## Selection rules

1. Sequential only: no `Domain`, no effects, no domainslib.
2. Standard library only, compiled with plain `ocamlc` (no dune, no opam).
   C-stub libraries shipped with the compiler load dynamically on the verified
   runtime (`unix.cma`, `str.cma` with `-dllpath` to the stock stublibs), so
   those are allowed; opam packages (zarith, lwt, yojson, ...) are not.
3. Exit 0 and the same stdout as the stock runtime (outputs that are timings
   or random are noted).
4. Sandmark's own parameters (`run_config_byte.json`, else `run_config.json`),
   reduced where a run on the verified runtime took over about a minute.
5. Heap: `MIN_EXPANSION_WORDSIZE = max(4M, 4 x stock top_heap_words)`, rounded
   up to a multiple of 1M words (the verified heap does not grow).

## Benchmarks timed for the parallel mark

Only programs whose sequential mark is at least 1% of the run and that do at
least 3 major collections: with a heap 4x the live peak, almost every Sandmark
program spends well under 1% of its time marking, and a parallel mark changes
nothing measurable there.  Of those that pass, timed: **markbench** (Sandmark's
own mark benchmark: a large live heap and `n` explicit `Gc.full_major`; run with
n = 5 instead of 20), **minilight**, **bdd**, **fft**.

## All benchmarks that build and run

Mark s is the sequential mark's total over the run (verified runtime,
VGC_MARK_STATS); walls are single runs on a loaded machine, for orientation
only.

| name | args used | heap words | majors | mark s | mark % | verified s | stock s | timed | notes |
|---|---|---|---|---|---|---|---|---|---|
| binarytrees5 | 21 | 88080384 | 20 | 0.34 | 0.8 | 40.547 | 40.510 |  |  |
| fasta3 | 25_000_000 | 4194304 | 1037 | 0.03 | 0.1 | 42.426 | 33.263 |  |  |
| fasta6 | 25_000_000 | 224395264 | 18 | 0.00 | 0.0 | 38.120 | 30.565 |  |  |
| knucleotide | (none) | 36700160 | - | - | - | 29.383 | 28.516 | | input fasta3 2_500_000 (Sandmark 25_000_000) |
| knucleotide3 | (none) | 168820736 | - | - | - | 29.242 | 29.883 | | input fasta3 2_500_000 (Sandmark 25_000_000) |
| mandelbrot6 | 3000 | 4194304 | 1505 | 0.04 | 0.1 | 24.933 | 18.614 |  | Sandmark 16_000 |
| nbody | 5_000_000 | 4194304 | 2246 | 0.05 | 0.2 | 29.338 | 19.474 |  | Sandmark 50_000_000 |
| revcomp2 | (none) | 11534336 | 1 | 0.00 | 0.1 | 1.166 | 1.143 |  | input fasta3 2_500_000 (Sandmark 25_000_000); <3 majors |
| spectralnorm2 | 2_500 | 4194304 | 1061 | 0.03 | 0.1 | 21.640 | 15.577 |  | Sandmark 5_500 |
| almabench | (none) | 4194304 | 598 | 0.02 | 0.1 | 13.467 | 9.692 |  |  |
| bdd | 26 | 9437184 | 320 | 1.19 | 2.3 | 51.806 | 44.057 | yes |  |
| kb | (none) | 4194304 | 310 | 0.16 | 0.9 | 17.358 | 15.287 |  |  |
| kb_no_exc | (none) | 4194304 | 79 | 0.03 | 0.2 | 14.816 | 14.118 |  |  |
| lexifi-g2pp | (none) | 4194304 | 6136 | 0.64 | 0.6 | 112.043 | 74.688 |  |  |
| sequence_cps | 10000 | 4194304 | 551 | 0.01 | 0.1 | 11.530 | 8.950 |  |  |
| hamming | 10_000 | 16777216 | 1 | 0.02 | 0.0 | 148.646 | .301 |  | <3 majors; verified runtime ~230x slower than stock (98.1 s against 0.42 s, rerun awake): first-fit promotion walks every 1-2 word hole, see docs/sandmark-failures.md |
| soli | 200 | 4194304 | - | - | - | 10.411 | 10.097 | |  |
| minilight | roomfront5.ml.txt | 4194304 | 987 | 1.20 | 4.5 | 26.699 | 17.774 | yes | Sandmark roomfront.ml.txt (100 passes); 5 passes |
| kronecker | 12 10 | 11534336 | 7146 | 0.20 | 0.6 | 33.195 | 35.842 |  |  |
| kernel1_run | edges.data | 171966464 | - | - | - | 2.898 | 2.214 | | stdout differs (timings or Random.self_init; masked); edges from gen -scale 17 (Sandmark scale 21) |
| LU_decomposition | 1024 | 19922944 | 282 | 0.01 | 0.0 | 42.355 | 34.646 |  |  |
| floyd_warshall | 512 | 9437184 | 1 | 0.01 | 0.0 | 10.060 | 12.053 |  | <3 majors |
| game_of_life | 64 | 9437184 | 1 | 0.00 | 0.0 | 24.511 | 20.149 |  | Sandmark 256; <3 majors |
| evolutionary_algorithm | 1000 1000 | 16777216 | 170 | 0.21 | 0.5 | 41.007 | 35.655 |  | stdout differs (timings or Random.self_init; masked); Sandmark 10000 10000 |
| nqueens | 13 | 4194304 | 6 | 0.00 | 0.0 | 10.396 | 10.338 |  | Sandmark byte 15 |
| mergesort | 16777216 | 148897792 | - | - | - | 27.672 | 27.863 | | Sandmark 67108864 |
| matrix_multiplication | 1024 | 14680064 | - | - | - | 47.104 | 40.586 | |  |
| quicksort | 4000000 | 36700160 | - | - | - | 7.643 | 7.354 | |  |
| grammatrix | 1 data/1k.csv | 14680064 | 1040 | 0.10 | 0.2 | 64.785 | 36.857 |  | Sandmark default input tox21 (>5 min) |
| durand-kerner-aberth | 75 | 4194304 | 1020 | 0.04 | 0.3 | 14.845 | 9.368 |  | Sandmark default (=100) |
| fft | (none) | 116391936 | 33 | 0.77 | 2.5 | 30.724 | 13.007 | yes |  |
| levinson-durbin | (none) | 4194304 | 2235 | 0.03 | 0.1 | 47.471 | 31.435 |  |  |
| crout-decomposition | (none) | 33554432 | 63 | 0.02 | 0.1 | 14.129 | 14.225 |  |  |
| naive-multilayer | (none) | 4194304 | 1665 | 0.12 | 0.3 | 48.352 | 36.880 |  |  |
| qr-decomposition | (none) | 4194304 | 973 | 0.06 | 0.3 | 23.152 | 17.522 |  |  |
| alloc | 200_000 | 4194304 | 339 | 0.00 | 0.0 | 7.403 | 6.305 |  |  |
| morestacks | 1_000 | 4194304 | - | - | - | 27.824 | 18.561 | |  |
| lazy_primes | 5000 | 202375168 | 1 | 1.29 | 22.4 | 5.770 | 3.182 |  | not in run_config; micro_multicore.json 1000..10000; <3 majors |
| markbench | 5 (timed), 20 here | 424673280 | 20 | 56.40 | 87.4 | 64.540 | 21.906 | yes | stdout differs (timings or Random.self_init; masked); Gc.full_major |
| lists.int-option-array_100000 | int-option-array 100000 | 16777216 | 9 | 0.03 | 0.8 | 3.014 | 2.993 |  |  |
| lists.string_100000 | string 100000 | 8388608 | 5 | 0.00 | 0.2 | 1.678 | 1.847 |  |  |
| lists.record_100000 | record 100000 | 13631488 | 7 | 0.01 | 0.5 | 2.262 | 2.448 |  |  |
| lists.float-array_100000 | float-array 100000 | 16777216 | 8 | 0.02 | 0.9 | 2.042 | 1.828 |  |  |
| lists.float-tuple_100000 | float-tuple 100000 | 12582912 | 7 | 0.01 | 0.8 | 1.412 | 1.201 |  |  |
| stress.10000_10 | 10000 10 | 4194304 | 53 | 0.01 | 0.2 | 4.065 | 3.915 |  |  |
| stress.100000_100 | 100000 100 | 4194304 | 53 | 0.07 | 1.5 | 4.444 | 4.148 |  |  |
| stress.1_100 | 1 100 | 4194304 | 53 | 0.00 | 0.0 | 4.235 | 3.957 |  |  |
| stress.100000_10 | 100000 10 | 4194304 | 53 | 0.07 | 1.7 | 4.120 | 3.762 |  |  |
| stress.10000_100 | 10000 100 | 4194304 | 53 | 0.01 | 0.2 | 4.284 | 4.156 |  |  |
| stress.1_10 | 1 10 | 4194304 | 53 | 0.00 | 0.0 | 4.017 | 3.934 |  |  |
| stacks.100000_ints-small | 100000 ints-small | 4194304 | - | - | - | 17.203 | 13.840 | |  |
| stacks.20000_ints-large | 20000 ints-large | 4194304 | - | - | - | 11.218 | 7.168 | |  |
| weakretain.25_1000 | 25 1000 | 4194304 | 35 | 0.00 | 0.0 | 2.107 | 2.069 |  | Weak |
| weakretain.25_100000 | 25 100000 | 4194304 | 35 | 0.00 | 0.0 | 2.212 | 2.079 |  | Weak |
| weakretain.25_10000000 | 25 10000000 | 89128960 | 2 | 0.00 | 0.0 | 2.215 | 2.037 |  | <3 majors; Weak |
| weakretain.50_1000 | 50 1000 | 4194304 | 31 | 0.00 | 0.0 | 2.423 | 2.040 |  | Weak |
| weakretain.50_100000 | 50 100000 | 4194304 | 31 | 0.00 | 0.0 | 2.915 | 2.477 |  | Weak |
| weakretain.50_10000000 | 50 10000000 | 89128960 | 1 | 0.00 | 0.0 | 3.299 | 3.247 |  | <3 majors; Weak |
| weakretain.75_1000 | 75 1000 | 4194304 | 28 | 0.00 | 0.0 | 3.271 | 2.971 |  | Weak |
| weakretain.75_100000 | 75 100000 | 4194304 | 28 | 0.00 | 0.0 | 3.471 | 3.174 |  | Weak |
| weakretain.75_10000000 | 75 10000000 | 89128960 | 1 | 0.00 | 0.0 | 4.083 | 3.313 |  | <3 majors; Weak |
| weakretain.100_1000 | 100 1000 | 4194304 | 25 | 0.00 | 0.0 | 3.495 | 3.682 |  | Weak |
| weakretain.100_100000 | 100 100000 | 4194304 | 25 | 0.00 | 0.0 | 3.406 | 3.656 |  | Weak |
| weakretain.100_10000000 | 100 10000000 | 89128960 | 1 | 0.00 | 0.0 | 3.734 | 3.704 |  | <3 majors; Weak |
| stack_bench.stack_push_pop_100000000 | stack_push_pop 100000000 | 4194304 | 127 | 0.00 | 0.0 | 9.928 | 9.577 |  |  |
| array_bench.array_forall_1000_100000 | array_forall 1000 100000 | 4194304 | - | - | - | 3.134 | 3.622 | |  |
| array_bench.array_fold_1000_100000 | array_fold 1000 100000 | 4194304 | - | - | - | 3.674 | 3.922 | |  |
| array_bench.array_iter_1000_100000 | array_iter 1000 100000 | 4194304 | - | - | - | 2.993 | 3.046 | |  |
| bytes_bench.bytes_map_1000000 | bytes_map 1000000 | 4194304 | 32 | 0.00 | 0.0 | 19.509 | 16.463 |  |  |
| bytes_bench.bytes_uppercase_ascii_1000000 | bytes_uppercase_ascii 1000000 | 4194304 | 31 | 0.00 | 0.0 | 22.805 | 24.741 |  |  |
| bytes_bench.bytes_contains_100000000 | bytes_contains 100000000 | 4194304 | - | - | - | 27.206 | 35.704 | |  |
| bytes_bench.bytes_iter_1000000 | bytes_iter 1000000 | 4194304 | 1 | 0.00 | 0.0 | 11.865 | 12.988 |  | <3 majors |
| bytes_bench.bytes_get_100000000 | bytes_get 100000000 | 4194304 | - | - | - | 1.815 | 1.666 | |  |
| bytes_bench.bytes_sub_100000000 | bytes_sub 100000000 | 4194304 | 84 | 0.00 | 0.0 | 7.997 | 7.070 |  |  |
| set_bench.set_fold_1000000 | set_fold 1000000 | 4194304 | 1 | 0.00 | 0.0 | 59.049 | 62.298 |  | <3 majors |
| set_bench.set_add_rem_20000000 | set_add_rem 20000000 | 4194304 | 890 | 0.03 | 0.0 | 58.350 | 55.366 |  |  |
| set_bench.set_mem_50000000 | set_mem 50000000 | 4194304 | - | - | - | 29.806 | 31.317 | |  |
| hashtbl_bench.int_replace1_10000 | int_replace1 10000 | 4194304 | - | - | - | 1.395 | 1.267 | |  |
| hashtbl_bench.hashtbl_remove_4000000 | hashtbl_remove 4000000 | 4194304 | 8 | 0.00 | 0.0 | 1.080 | 1.099 |  |  |
| hashtbl_bench.hashtbl_find_6000000 | hashtbl_find 6000000 | 4194304 | - | - | - | .636 | .643 | |  |
| hashtbl_bench.int_find1_20000 | int_find1 20000 | 4194304 | - | - | - | 1.297 | 1.295 | |  |
| hashtbl_bench.caml_hash_int_200000 | caml_hash_int 200000 | 4194304 | - | - | - | 7.341 | 6.966 | |  |
| hashtbl_bench.caml_hash_tuple_100000 | caml_hash_tuple 100000 | 4194304 | 127 | 0.00 | 0.1 | 6.009 | 5.314 |  |  |
| hashtbl_bench.int_replace2_100000 | int_replace2 100000 | 4194304 | - | - | - | 17.461 | 14.451 | |  |
| hashtbl_bench.int_find2_300000 | int_find2 300000 | 4194304 | - | - | - | 627.709 | 27.312 | |  |
| hashtbl_bench.hashtbl_iter_200000 | hashtbl_iter 200000 | 4194304 | - | - | - | 617.604 | 17.111 | |  |
| hashtbl_bench.hashtbl_fold_200000 | hashtbl_fold 200000 | 4194304 | - | - | - | 20.005 | 621.457 | |  |
| hashtbl_bench.hashtbl_add_resizing_4000000 | hashtbl_add_resizing 4000000 | 78643200 | - | - | - | 4.680 | 2.986 | |  |
| hashtbl_bench.hashtbl_add_sized_6000000 | hashtbl_add_sized 6000000 | 130023424 | - | - | - | 1.639 | 6.314 | |  |
| hashtbl_bench.hashtbl_add_duplicate_2000000 | hashtbl_add_duplicate 2000000 | 81788928 | - | - | - | 1.670 | 1.967 | |  |
| hashtbl_bench.hashtbl_filter_map_100000 | hashtbl_filter_map 100000 | 4194304 | 85 | 0.00 | 0.0 | 10.128 | 9.304 |  |  |
| string_bench.string_sub_50000000 | string_sub 50000000 | 4194304 | 42 | 0.00 | 0.0 | 3.778 | 3.560 |  |  |
| string_bench.string_concat_20000000 | string_concat 20000000 | 4194304 | 25 | 0.00 | 0.0 | 7.387 | 6.871 |  |  |
| string_bench.string_iter_1000000 | string_iter 1000000 | 4194304 | 1 | 0.00 | 0.0 | 9.327 | 8.308 |  | <3 majors |
| string_bench.string_uppercase_ascii_1000000 | string_uppercase_ascii 1000000 | 4194304 | 31 | 0.00 | 0.0 | 25.656 | 617.303 |  |  |
| string_bench.string_split_on_char_500000 | string_split_on_char 500000 | 4194304 | 96 | 0.00 | 0.0 | 621.391 | 7.805 |  |  |
| string_bench.string_compare_10000 | string_compare 10000 | 4194304 | 1 | 0.00 | 0.0 | 4.384 | 604.114 |  | <3 majors |
| string_bench.string_equal_25000 | string_equal 25000 | 4194304 | 3 | 0.00 | 0.0 | 7.473 | 19.078 |  |  |
| pervasives_bench.pervasives_compare_lists_100000000 | pervasives_compare_lists 100000000 | 4194304 | - | - | - | 1.577 | 1.780 | |  |
| pervasives_bench.pervasives_compare_ints_1000000000 | pervasives_compare_ints 1000000000 | 4194304 | - | - | - | 11.751 | 10.207 | |  |
| pervasives_bench.pervasives_equal_floats_1000000000 | pervasives_equal_floats 1000000000 | 4194304 | 847 | 0.02 | 0.0 | 636.515 | 13.166 |  |  |
| pervasives_bench.pervasives_equal_strings_20000000 | pervasives_equal_strings 20000000 | 4194304 | 21 | 0.00 | 0.0 | 2.409 | 2.242 |  |  |
| pervasives_bench.pervasives_compare_strings_20000000 | pervasives_compare_strings 20000000 | 4194304 | 21 | 0.00 | 0.0 | 2.448 | 2.314 |  |  |
| map_bench.map_map_10000 | map_map 10000 | 4194304 | 254 | 0.17 | 0.7 | 25.006 | 608.636 |  |  |
| big_array_bench.big_array_int_rev_1024_50000 | big_array_int_rev 1024 50000 | 4194304 | - | - | - | 1.652 | 603.028 | |  |
| big_array_bench.big_array_int32_rev_1024_50000 | big_array_int32_rev 1024 50000 | 4194304 | 65 | 0.00 | 0.0 | 2.371 | 1.904 |  |  |
| str_bench.str_search_forward_5000000 | str_search_forward 5000000 | 4194304 | 6 | 0.00 | 0.0 | 1.16 | 1.14 | | Str |
| str_bench.str_split_2000000 | str_split 2000000 | 4194304 | 73 | 0.00 | 0.1 | 1.48 | 1.11 | | Str |

## Excluded

Built but failing on the verified runtime (each also tried with the heap
doubled up to four times):

| benchmark | error |
|---|---|
| zdd | `Out_of_memory` at every heap up to 671M words (stock peak 21M words). Not memory growth (live set 0.25M words): `Weak.get_copy` reads a weak key left dangling by the minor GC, which ignores `ephe_ref_table`; see docs/sandmark-failures.md |
| stacks.100000_floats-small | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): 268K stack slots; see docs/sandmark-failures.md |
| stacks.20000_floats-large | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): 304K stack slots; see docs/sandmark-failures.md |
| lazylist.100000_100 | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): 279K stack slots (deep `add_lazy` recursion); see docs/sandmark-failures.md |
| finalise.50 | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): the finaliser table, which never empties because finalisers are not run; see docs/sandmark-failures.md |
| finalise.60 | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): the finaliser table, which never empties because finalisers are not run; see docs/sandmark-failures.md |
| finalise.70 | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): the finaliser table, which never empties because finalisers are not run; see docs/sandmark-failures.md |
| finalise.80 | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): the finaliser table, which never empties because finalisers are not run; see docs/sandmark-failures.md |
| finalise.90 | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): the finaliser table, which never empties because finalisers are not run; see docs/sandmark-failures.md |
| finalise.100 | `Fatal error: verified gen GC: root overflow`: more than MAX_ROOTS (2^18) roots at one collection (alloc_gen.c): the finaliser table, which never empties because finalisers are not run; see docs/sandmark-failures.md |

Not built:

| benchmark | reason |
|---|---|
| alt-ergo, coqc, cpdf, cubicle, frama-c, js_of_ocaml, menhir, setrip | whole applications installed from opam |
| irmin (irmin_mem_rw, replay) | opam packages (irmin, lwt) |
| decompress (test_decompress) | opam packages (decompress, checkseum, bigstringaf) |
| yojson (ydump) | opam package yojson |
| zarith (fact, fib, pi, tak), benchmarksgame pidigits5 | opam package zarith |
| benchmarksgame regexredux2 | dune libraries include zarith |
| chameneos_redux_lwt, thread_ring_lwt_mvar, thread_ring_lwt_stream, valet test_lwt | opam package lwt |
| owl_gc | opam package owl |
| simple-tests capi | its own C stubs (ocamlcapi.c), which would have to be linked into the runtime |
| minilight-ocaml (run_config.json) | external program; Sandmark's multicore-minilight/sequential sources are built as `minilight` instead |
| benchmarksgame fannkuchredux | raises `Invalid_argument "index out of bounds"` on the stock runtime too (at n = 10); compute-only, not investigated |
| multicore-*, graph500par, mpl, numerical-analysis parallel versions, `*_multicore`, `*_parallel` | Domain / domainslib / effects |

