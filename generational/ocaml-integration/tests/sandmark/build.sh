#!/usr/bin/env bash
# Build the curated sequential Sandmark benchmarks (see README.md) as OCaml
# 4.14 bytecode with the stock ocamlc, into tests/sandmark/bin/<name>.byte.
# Data files the benchmarks open are copied/generated next to them in bin/,
# so run them with bin/ as the working directory.
#
# Idempotent: clones Sandmark at the pinned commit into _build/sandmark if it
# is absent, rebuilds every binary (cheap), and regenerates the generated
# inputs (fasta / graph500 edges) only if missing.  Sources are copied to
# bin/.obj/<name>/ before compiling so the clone is never written to.
set -eu

HERE="$(cd "$(dirname "$0")" && pwd)"
INTEG="$(cd "$HERE/../.." && pwd)"
SANDMARK="${SANDMARK:-$INTEG/_build/sandmark}"
SANDMARK_COMMIT=5605805954a00497ed197c930641cddd580e1507
BINDIR="$HERE/bin"
OCAMLBIN="$INTEG/ocaml-4.14-unchanged/_install/bin"
OCAMLC="$OCAMLBIN/ocamlc"
OCAMLDEP="$OCAMLBIN/ocamldep"
STOCK_OCAMLRUN="$INTEG/ocaml-4.14-unchanged/runtime/ocamlrun"
STDLIB="$("$OCAMLC" -where)"

if [ ! -d "$SANDMARK/benchmarks" ]; then
  mkdir -p "$(dirname "$SANDMARK")"
  git init -q "$SANDMARK"
  git -C "$SANDMARK" fetch -q --depth 1 https://github.com/ocaml-bench/sandmark.git "$SANDMARK_COMMIT"
  git -C "$SANDMARK" checkout -q FETCH_HEAD
fi
B="$SANDMARK/benchmarks"
mkdir -p "$BINDIR/.obj"

# build NAME DIR LIBS MODULES...
#   DIR: directory under benchmarks/; LIBS: "", "unix" or "str";
#   MODULES: base names (.mli/.ml copied when present), ordered by ocamldep;
#   a name containing "/" is taken relative to benchmarks/ instead of DIR.
build() {
  local name="$1" dir="$2" libs="$3"; shift 3
  local obj="$BINDIR/.obj/$name"
  rm -rf "$obj"; mkdir -p "$obj"
  local m
  local p
  for m in "$@"; do
    case "$m" in */*) p="$B/$m" ;; *) p="$B/$dir/$m" ;; esac
    if [ -f "$p.mli" ]; then cp "$p.mli" "$obj/"; fi
    if [ -f "$p.ml" ]; then cp "$p.ml" "$obj/"; fi
  done
  local srcs
  srcs="$(cd "$obj" && "$OCAMLDEP" -sort *.ml* )"
  local libargs=""
  if [ "$libs" = unix ] || [ "$libs" = str ]; then
    # Record the stublibs dir so dllunix.so / dllcamlstr.so are found
    # without ld.conf lookups.
    libargs="$libs.cma -dllpath $STDLIB/stublibs"
  fi
  # shellcheck disable=SC2086
  (cd "$obj" && "$OCAMLC" -w -a $libargs -o "$BINDIR/$name.byte" $srcs)
  echo "built $name"
}

# --- benchmarksgame ---------------------------------------------------------
build binarytrees5   benchmarksgame "" binarytrees5
build fasta3         benchmarksgame "" fasta3
build fasta6         benchmarksgame "" fasta6
build knucleotide    benchmarksgame "" knucleotide
build knucleotide3   benchmarksgame "" knucleotide3
build mandelbrot6    benchmarksgame "" mandelbrot6
build nbody          benchmarksgame "" nbody
build revcomp2       benchmarksgame "" revcomp2
build spectralnorm2  benchmarksgame "" spectralnorm2
# --- OCamlPro-derived macro benchmarks --------------------------------------
build almabench      almabench "" almabench
build bdd            bdd "" bdd
build kb             kb "" kb
build kb_no_exc      kb "" kb_no_exc
build lexifi-g2pp    lexifi-g2pp "" date math optimization g2pp_calibration main
build sequence_cps   sequence "" sequence_cps
build hamming        hamming "" hamming
build soli           soli "" soli
build zdd            zdd "" zdd
build minilight      multicore-minilight/sequential "" \
      vector3f triangle spatialIndex surfacePoint scene rayTracer image camera minilight
# --- graph500seq ------------------------------------------------------------
build kronecker      graph500seq "" kronecker
build graph500_gen   graph500seq unix graph500par/graphTypes generateSeq gen
build kernel1_run    graph500seq unix graph500par/graphTypes generateSeq sparseGraphSeq kernel1Seq kernel1_run
# --- multicore-numerical (sequential versions) -------------------------------
build LU_decomposition       multicore-numerical "" LU_decomposition
build floyd_warshall         multicore-numerical "" floyd_warshall
build game_of_life           multicore-numerical "" game_of_life
build evolutionary_algorithm multicore-numerical "" evolutionary_algorithm
build nqueens                multicore-numerical "" nqueens
build mergesort              multicore-numerical "" mergesort
build matrix_multiplication  multicore-numerical "" matrix_multiplication
build quicksort              multicore-numerical "" quicksort
# --- numerical-analysis -----------------------------------------------------
build durand-kerner-aberth numerical-analysis "" durand_kerner_aberth
build fft                  numerical-analysis unix fft
build levinson-durbin      numerical-analysis "" levinson_durbin_dataset levinson_durbin
build crout-decomposition  numerical-analysis "" crout_decomposition
build naive-multilayer     numerical-analysis "" naive_multilayer_dataset naive_multilayer
build qr-decomposition     numerical-analysis "" qr_decomposition
# --- simple-tests -----------------------------------------------------------
build alloc       simple-tests "" alloc
build morestacks  simple-tests "" morestacks
build lists       simple-tests "" lists
build stress      simple-tests "" stress
build stacks      simple-tests "" stacks
build lazylist    simple-tests "" lazylist
build lazy_primes simple-tests "" lazy_primes
build weakretain  simple-tests "" weakretain
build finalise    simple-tests "" finalise
# --- stdlib -----------------------------------------------------------------
build stack_bench      stdlib "" stack_bench
build array_bench      stdlib "" array_bench
build bytes_bench      stdlib "" bytes_bench
build set_bench        stdlib "" set_bench
build hashtbl_bench    stdlib "" hashtbl_bench
build string_bench     stdlib "" string_bench
build pervasives_bench stdlib "" pervasives_bench
build map_bench        stdlib "" map_bench
build big_array_bench  stdlib "" big_array_bench
build str_bench        stdlib str str_bench
# --- markbench --------------------------------------------------------------
build markbench   markbench unix markbench

build grammatrix  multicore-grammatrix unix multicore-grammatrix/utls/utls grammatrix

# --- data files -------------------------------------------------------------
cd "$BINDIR"
mkdir -p data
for f in tox21_nrar_ligands_std_rand_01.csv 1k.csv 4k.csv; do
  ln -sf "$B/multicore-grammatrix/data/$f" "data/$f"
done
ln -sf "$B/zdd/words.txt" words.txt
# minilight: Sandmark's model (100 passes) takes >5 min in bytecode; make a
# copy that renders 5 passes (line 3 of the model is the iteration count).
awk 'NR==3{$0="5"}1' "$B/minilight/roomfront.ml.txt" > roomfront5.ml.txt
# knucleotide/knucleotide3/revcomp2 open "input25000000.txt", which Sandmark
# generates with `fasta3 25_000_000`.  We use 2_500_000 (FASTA_N overrides);
# the generated file is named by N and input25000000.txt symlinks to it.
FASTA_N="${FASTA_N:-2500000}"
if [ ! -s "fasta_$FASTA_N.txt" ]; then
  echo "generating fasta_$FASTA_N.txt"
  "$STOCK_OCAMLRUN" ./fasta3.byte "$FASTA_N" > "fasta_$FASTA_N.txt.tmp"
  mv "fasta_$FASTA_N.txt.tmp" "fasta_$FASTA_N.txt"
fi
ln -sf "fasta_$FASTA_N.txt" input25000000.txt
# kernel1_run reads edges.data, which Sandmark generates with
# `gen -scale 21 -edgefactor 16` (a 5.4 GB peak heap in kernel1_run); we use
# scale 17 (GRAPH_SCALE overrides).  gen uses Random.self_init, so the file
# differs between builds (kernel1_run prints only timings).
GRAPH_SCALE="${GRAPH_SCALE:-17}"
if [ ! -s "edges_$GRAPH_SCALE.data" ]; then
  echo "generating edges_$GRAPH_SCALE.data"
  "$STOCK_OCAMLRUN" ./graph500_gen.byte -scale "$GRAPH_SCALE" -edgefactor 16 "edges_$GRAPH_SCALE.data.tmp"
  mv "edges_$GRAPH_SCALE.data.tmp" "edges_$GRAPH_SCALE.data"
fi
ln -sf "edges_$GRAPH_SCALE.data" edges.data
echo "done: $BINDIR"
