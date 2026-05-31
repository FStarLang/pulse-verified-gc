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

BYTE_FILES = $(addsuffix .byte, $(BENCHMARKS))
BENCH_TARGETS = $(addsuffix .bench, $(BENCHMARKS))
STATS_TARGETS = $(addsuffix .stats, $(BENCHMARKS))
MINHEAP_TARGETS = $(addsuffix .minheap, $(BENCHMARKS))
MINHEAP_CSVS = $(addprefix results/,$(addsuffix .minheap.csv,$(BENCHMARKS)))

all: $(BYTE_FILES)

# ---- Smoke tests (one run each, verified gen GC) ----

test: $(BYTE_FILES)
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

.PHONY: all test benchmark bench-all bench-stats bench-min-heaps clean

clean:
	rm -f *.byte *.cmi *.cmo *.o
	rm -rf results
