# Benchmarks for verified generational GC vs stock OCaml vs verified M&S
#
# Three-way comparison using the Computer Language Benchmarks Game programs.

OCAMLC            ?= ../ocaml-4.14-unchanged/_install/bin/ocamlc
VERIFIED_GEN_OCAMLRUN ?= ../ocaml-4.14-verified-gen/runtime/ocamlrun
UNCHANGED_OCAMLRUN    ?= ../ocaml-4.14-unchanged/runtime/ocamlrun

# Optional: M&S runtime for 3-way comparison
VERIFIED_MS_OCAMLRUN  ?= ../../../mark-and-sweep/ocaml-integration/ocaml-4.14-verified-gc/runtime/ocamlrun

DEFAULT_MAJOR_WORDS       ?= 33554432
BINARYTREES_MAJOR_WORDS   ?= 134217728
FASTA_MAJOR_WORDS         ?= 134217728
QUICKSORT_MAJOR_WORDS     ?= 8000000
FANNKUCHREDUX_MAJOR_WORDS ?= $(DEFAULT_MAJOR_WORDS)
COUNT_CHANGE_MAJOR_WORDS  ?= 20000000
NBODIES_MAJOR_WORDS       ?= $(DEFAULT_MAJOR_WORDS)
SPECTRALNORM_MAJOR_WORDS  ?= $(DEFAULT_MAJOR_WORDS)
MANDELBROT_MAJOR_WORDS    ?= $(DEFAULT_MAJOR_WORDS)

%.byte: %.ml
	$(OCAMLC) -o $@ $<

bench_stats.cmo: bench_stats.ml
	$(OCAMLC) -c $<

%.stats.byte: %.ml bench_stats.cmo
	$(OCAMLC) -o $@ bench_stats.cmo $<

BENCHMARKS = binarytrees fasta quicksort fannkuchredux count_change nbodies spectralnorm mandelbrot

# Correctness tests (not benchmarks): run under both runtimes and compared.
CORRECTNESS_TESTS = infix_closures no_scan make_vect_barrier nursery_no_scan_interior

# infix_closures needs a small major heap so that real major collections
# (mark & sweep) happen; it checks Gc.quick_stat to confirm they did.
INFIX_MAJOR_WORDS ?= 300000

# no_scan allocates 300 x 2KB no-scan blocks and then promotes 400 nursery
# blocks, so it needs more room than infix_closures while still forcing real
# major collections.
NO_SCAN_MAJOR_WORDS ?= 4000000

# make_vect_barrier promotes a large young live set ten times over.
MAKE_VECT_MAJOR_WORDS ?= 4000000

# nursery_no_scan_interior forges interior pointers into no-scan nursery
# payloads.  It was a known-gap reproducer until the nursery scan window
# became `GC.Gen.MinorHeap.minor_scan_wosize`; it is now a regression test.
KNOWN_GAP_TESTS =
NURSERY_NO_SCAN_MAJOR_WORDS ?= 4000000

BYTE_FILES = $(addsuffix .byte, $(BENCHMARKS)) $(addsuffix .byte, $(CORRECTNESS_TESTS)) \
             $(addsuffix .byte, $(KNOWN_GAP_TESTS))
BENCH_TARGETS = $(addsuffix .bench, $(BENCHMARKS))
STATS_TARGETS = $(addsuffix .stats, $(BENCHMARKS))
MINHEAP_TARGETS = $(addsuffix .minheap, $(BENCHMARKS))
MINHEAP_CSVS = $(addprefix results/,$(addsuffix .minheap.csv,$(BENCHMARKS)))

all: $(BYTE_FILES)

# ---- Smoke tests (one run each, verified gen GC) ----

test: correctness $(BYTE_FILES)
	@echo "=== Smoke tests (verified generational GC) ==="
	@echo "--- binarytrees ---"
	MIN_EXPANSION_WORDSIZE=$(BINARYTREES_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) binarytrees.byte 10
	@echo "--- fasta ---"
	MIN_EXPANSION_WORDSIZE=$(FASTA_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) fasta.byte 1000
	@echo "--- quicksort ---"
	MIN_EXPANSION_WORDSIZE=$(QUICKSORT_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) quicksort.byte 10000
	@echo "--- fannkuchredux ---"
	MIN_EXPANSION_WORDSIZE=$(FANNKUCHREDUX_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) fannkuchredux.byte 7
	@echo "--- count_change ---"
	MIN_EXPANSION_WORDSIZE=$(COUNT_CHANGE_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) count_change.byte 50
	@echo "--- nbodies ---"
	MIN_EXPANSION_WORDSIZE=$(NBODIES_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) nbodies.byte 1000
	@echo "--- spectralnorm ---"
	MIN_EXPANSION_WORDSIZE=$(SPECTRALNORM_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) spectralnorm.byte 100
	@echo "--- mandelbrot ---"
	MIN_EXPANSION_WORDSIZE=$(MANDELBROT_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) mandelbrot.byte 100
	@echo "=== All smoke tests passed ==="

# ---- Correctness tests ----
#
# infix_closures.ml exercises interior (infix) pointers: mutually recursive
# OCaml closures share one heap block, and every function after the first is
# addressed by a pointer into the middle of that block.  The test confirms the
# heap really contains such pointers, that the parent-address formula in
# GC.Spec.Object.infix_addr_conds holds numerically, that a block reachable
# only through an interior pointer survives mark & sweep, and that the
# post-collection heap has exactly the shape it had before.
#
# Groups 8-10 do the same for the *nursery*: mutually recursive closures are
# allocated young, so an interior pointer to one points into the middle of a
# young block and Cheney copying must forward the enclosing block and re-apply
# the offset.  Both the major -> minor edge (remembered set) and the
# minor -> minor edge (Cheney scanning) are covered, and each is shown to have
# actually been promoted, so the nursery path is really the one exercised.
#
# Groups 11-12 move the interior pointer out of the heap and into a *root*: a
# local variable, scanned verbatim off the bytecode stack, is the only thing
# referring to the closure block.  A root cannot be replaced by its enclosing
# closure -- the mutator keeps calling through it -- so the offset has to
# survive the collection.  Group 12 keeps 24 such roots live simultaneously,
# one per frame of a recursion, with the collections forced at the bottom.
# Both collectors resolve roots (forward_if_minor_infix in the nursery,
# check_and_darken_bounded_spec in the major heap), and Phase H of
# docs/minor-infix-support-plan.md brought the specifications into line.
#
# Group 13 audits the heap the collector is *handed* rather than what it did
# with it: inside one collection-free window it establishes, on the live heap,
# that the closure blocks are in the nursery (positionally, between two young
# sentinels), that a root and a young field each hold an interior pointer into
# one, and that infix_addr_conds holds numerically -- exactly the shape
# GC.Gen.HeapInvariant.collection_heap_shape and
# GC.Gen.MinorCollectForwarding.Helpers.roots_valid_for_minor_collection now
# admit.  It then forces one minor collection and checks the result.
# spot/GC.SPOT.MinorInfixPre and spot/GC.SPOT.MinorInfixCall are the
# machine-checked counterparts: a concrete heap of exactly this shape, proved to
# satisfy gen_gc's precondition, and a Pulse call that runs the collector on it.
#
# It is run under the verified runtime and, as a differential check, under
# stock OCaml, where it must produce the same verdict.

correctness: $(addsuffix .byte, $(CORRECTNESS_TESTS))
	@echo "=== Correctness tests ==="
	@echo "--- infix_closures (verified generational GC) ---"
	MIN_EXPANSION_WORDSIZE=$(INFIX_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) infix_closures.byte
	@echo "--- infix_closures (stock OCaml, differential check) ---"
	$(UNCHANGED_OCAMLRUN) infix_closures.byte
	@echo "--- no_scan (verified generational GC) ---"
	MIN_EXPANSION_WORDSIZE=$(NO_SCAN_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) no_scan.byte
	@echo "--- no_scan (stock OCaml, differential check) ---"
	$(UNCHANGED_OCAMLRUN) no_scan.byte
	@echo "--- make_vect_barrier (verified generational GC) ---"
	MIN_EXPANSION_WORDSIZE=$(MAKE_VECT_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) make_vect_barrier.byte
	@echo "--- make_vect_barrier (stock OCaml, differential check) ---"
	$(UNCHANGED_OCAMLRUN) make_vect_barrier.byte
	@echo "--- nursery_no_scan_interior (verified generational GC) ---"
	MIN_EXPANSION_WORDSIZE=$(NURSERY_NO_SCAN_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) nursery_no_scan_interior.byte
	@echo "--- nursery_no_scan_interior (stock OCaml, differential check) ---"
	$(UNCHANGED_OCAMLRUN) nursery_no_scan_interior.byte
	@echo "=== Correctness tests passed ==="

# ---- Known-gap reproducers (expected to FAIL under the verified GC) ----
#
# Run these deliberately, e.g. `make known-gaps`.  Each one passes under
# stock OCaml and demonstrates a gap that is still open in the verified
# collector.  See docs/known-issues.md.
#
# There are currently none: nursery_no_scan_interior graduated to
# `correctness` when the nursery stopped scanning no-scan bodies.

known-gaps: $(addsuffix .byte, $(KNOWN_GAP_TESTS))
	@echo "=== No known-gap reproducers outstanding ==="

# ---- Benchmarks with hyperfine (3-way comparison) ----

benchmark: bench-all
	@echo "=== Benchmarks ==="

results:
	@mkdir -p results

binarytrees.bench: binarytrees.byte | results
	MIN_EXPANSION_WORDSIZE=$(BINARYTREES_MAJOR_WORDS) \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 16' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 16'

binarytrees.stats: binarytrees.stats.byte | results
	rm -f results/$@.csv
	MIN_EXPANSION_WORDSIZE=$(BINARYTREES_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv binarytrees verified-gen $(VERIFIED_GEN_OCAMLRUN) $< 16
	MIN_EXPANSION_WORDSIZE=$(BINARYTREES_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv binarytrees stock-ocaml $(UNCHANGED_OCAMLRUN) $< 16

binarytrees.minheap: binarytrees.stats.byte | results
	rm -f results/$@.csv
	./bench_min_heap.sh results/$@.csv binarytrees $(BINARYTREES_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) $(UNCHANGED_OCAMLRUN) $< 16

fasta.bench: fasta.byte | results
	MIN_EXPANSION_WORDSIZE=$(FASTA_MAJOR_WORDS) \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 2500000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 2500000'

fasta.stats: fasta.stats.byte | results
	rm -f results/$@.csv
	MIN_EXPANSION_WORDSIZE=$(FASTA_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv fasta verified-gen $(VERIFIED_GEN_OCAMLRUN) $< 2500000
	MIN_EXPANSION_WORDSIZE=$(FASTA_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv fasta stock-ocaml $(UNCHANGED_OCAMLRUN) $< 2500000

fasta.minheap: fasta.stats.byte | results
	rm -f results/$@.csv
	./bench_min_heap.sh results/$@.csv fasta $(FASTA_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) $(UNCHANGED_OCAMLRUN) $< 2500000

quicksort.bench: quicksort.byte | results
	MIN_EXPANSION_WORDSIZE=$(QUICKSORT_MAJOR_WORDS) \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 5000000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 5000000'

quicksort.stats: quicksort.stats.byte | results
	rm -f results/$@.csv
	MIN_EXPANSION_WORDSIZE=$(QUICKSORT_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv quicksort verified-gen $(VERIFIED_GEN_OCAMLRUN) $< 5000000
	MIN_EXPANSION_WORDSIZE=$(QUICKSORT_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv quicksort stock-ocaml $(UNCHANGED_OCAMLRUN) $< 5000000

quicksort.minheap: quicksort.stats.byte | results
	rm -f results/$@.csv
	./bench_min_heap.sh results/$@.csv quicksort $(QUICKSORT_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) $(UNCHANGED_OCAMLRUN) $< 5000000

fannkuchredux.bench: fannkuchredux.byte | results
	MIN_EXPANSION_WORDSIZE=$(FANNKUCHREDUX_MAJOR_WORDS) \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 11' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 11'

fannkuchredux.stats: fannkuchredux.stats.byte | results
	rm -f results/$@.csv
	MIN_EXPANSION_WORDSIZE=$(FANNKUCHREDUX_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv fannkuchredux verified-gen $(VERIFIED_GEN_OCAMLRUN) $< 11
	MIN_EXPANSION_WORDSIZE=$(FANNKUCHREDUX_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv fannkuchredux stock-ocaml $(UNCHANGED_OCAMLRUN) $< 11

fannkuchredux.minheap: fannkuchredux.stats.byte | results
	rm -f results/$@.csv
	./bench_min_heap.sh results/$@.csv fannkuchredux $(FANNKUCHREDUX_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) $(UNCHANGED_OCAMLRUN) $< 11

count_change.bench: count_change.byte | results
	MIN_EXPANSION_WORDSIZE=$(COUNT_CHANGE_MAJOR_WORDS) \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 150' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 150'

count_change.stats: count_change.stats.byte | results
	rm -f results/$@.csv
	MIN_EXPANSION_WORDSIZE=$(COUNT_CHANGE_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv count_change verified-gen $(VERIFIED_GEN_OCAMLRUN) $< 150
	MIN_EXPANSION_WORDSIZE=$(COUNT_CHANGE_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv count_change stock-ocaml $(UNCHANGED_OCAMLRUN) $< 150

count_change.minheap: count_change.stats.byte | results
	rm -f results/$@.csv
	./bench_min_heap.sh results/$@.csv count_change $(COUNT_CHANGE_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) $(UNCHANGED_OCAMLRUN) $< 150

nbodies.bench: nbodies.byte | results
	MIN_EXPANSION_WORDSIZE=$(NBODIES_MAJOR_WORDS) \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 100000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 100000'

nbodies.stats: nbodies.stats.byte | results
	rm -f results/$@.csv
	MIN_EXPANSION_WORDSIZE=$(NBODIES_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv nbodies verified-gen $(VERIFIED_GEN_OCAMLRUN) $< 100000
	MIN_EXPANSION_WORDSIZE=$(NBODIES_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv nbodies stock-ocaml $(UNCHANGED_OCAMLRUN) $< 100000

nbodies.minheap: nbodies.stats.byte | results
	rm -f results/$@.csv
	./bench_min_heap.sh results/$@.csv nbodies $(NBODIES_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) $(UNCHANGED_OCAMLRUN) $< 100000

spectralnorm.bench: spectralnorm.byte | results
	MIN_EXPANSION_WORDSIZE=$(SPECTRALNORM_MAJOR_WORDS) \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 1000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 1000'

spectralnorm.stats: spectralnorm.stats.byte | results
	rm -f results/$@.csv
	MIN_EXPANSION_WORDSIZE=$(SPECTRALNORM_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv spectralnorm verified-gen $(VERIFIED_GEN_OCAMLRUN) $< 1000
	MIN_EXPANSION_WORDSIZE=$(SPECTRALNORM_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv spectralnorm stock-ocaml $(UNCHANGED_OCAMLRUN) $< 1000

spectralnorm.minheap: spectralnorm.stats.byte | results
	rm -f results/$@.csv
	./bench_min_heap.sh results/$@.csv spectralnorm $(SPECTRALNORM_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) $(UNCHANGED_OCAMLRUN) $< 1000

mandelbrot.bench: mandelbrot.byte | results
	MIN_EXPANSION_WORDSIZE=$(MANDELBROT_MAJOR_WORDS) \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 1000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 1000'

mandelbrot.stats: mandelbrot.stats.byte | results
	rm -f results/$@.csv
	MIN_EXPANSION_WORDSIZE=$(MANDELBROT_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv mandelbrot verified-gen $(VERIFIED_GEN_OCAMLRUN) $< 1000
	MIN_EXPANSION_WORDSIZE=$(MANDELBROT_MAJOR_WORDS) \
	./bench_stats.sh results/$@.csv mandelbrot stock-ocaml $(UNCHANGED_OCAMLRUN) $< 1000

mandelbrot.minheap: mandelbrot.stats.byte | results
	rm -f results/$@.csv
	./bench_min_heap.sh results/$@.csv mandelbrot $(MANDELBROT_MAJOR_WORDS) $(VERIFIED_GEN_OCAMLRUN) $(UNCHANGED_OCAMLRUN) $< 1000

bench-all: $(BENCH_TARGETS)
	$(MAKE) bench-stats

bench-stats: $(STATS_TARGETS)

bench-min-heaps: $(MINHEAP_TARGETS)
	rm -f results/min_heaps.csv
	head -n 1 results/binarytrees.minheap.csv > results/min_heaps.csv
	tail -n +2 -q $(MINHEAP_CSVS) >> results/min_heaps.csv

.PHONY: all test correctness known-gaps benchmark bench-all bench-stats bench-min-heaps clean

clean:
	rm -f *.byte *.cmi *.cmo *.o
	rm -rf results
