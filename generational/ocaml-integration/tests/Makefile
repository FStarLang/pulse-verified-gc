# Benchmarks for verified generational GC vs stock OCaml vs verified M&S
#
# Three-way comparison using the Computer Language Benchmarks Game programs.

OCAMLC            ?= ../ocaml-4.14-unchanged/_install/bin/ocamlc
VERIFIED_GEN_OCAMLRUN ?= ../ocaml-4.14-verified-gen/runtime/ocamlrun
UNCHANGED_OCAMLRUN    ?= ../ocaml-4.14-unchanged/runtime/ocamlrun

# Optional: M&S runtime for 3-way comparison
VERIFIED_MS_OCAMLRUN  ?= ../../../mark-and-sweep/ocaml-integration/ocaml-4.14-verified-gc/runtime/ocamlrun

%.byte: %.ml
	$(OCAMLC) -o $@ $<

BENCHMARKS = binarytrees fasta quicksort fannkuchredux count_change nbodies spectralnorm mandelbrot

BYTE_FILES = $(addsuffix .byte, $(BENCHMARKS))

all: $(BYTE_FILES)

# ---- Smoke tests (one run each, verified gen GC) ----

test: $(BYTE_FILES)
	@echo "=== Smoke tests (verified generational GC) ==="
	@echo "--- binarytrees ---"
	MIN_EXPANSION_WORDSIZE=134217728 $(VERIFIED_GEN_OCAMLRUN) binarytrees.byte 10
	@echo "--- fasta ---"
	MIN_EXPANSION_WORDSIZE=134217728 $(VERIFIED_GEN_OCAMLRUN) fasta.byte 1000
	@echo "--- quicksort ---"
	MIN_EXPANSION_WORDSIZE=8000000 $(VERIFIED_GEN_OCAMLRUN) quicksort.byte 10000
	@echo "--- fannkuchredux ---"
	$(VERIFIED_GEN_OCAMLRUN) fannkuchredux.byte 7
	@echo "--- count_change ---"
	MIN_EXPANSION_WORDSIZE=20000000 $(VERIFIED_GEN_OCAMLRUN) count_change.byte 50
	@echo "--- nbodies ---"
	$(VERIFIED_GEN_OCAMLRUN) nbodies.byte 1000
	@echo "--- spectralnorm ---"
	$(VERIFIED_GEN_OCAMLRUN) spectralnorm.byte 100
	@echo "--- mandelbrot ---"
	$(VERIFIED_GEN_OCAMLRUN) mandelbrot.byte 100
	@echo "=== All smoke tests passed ==="

# ---- Benchmarks with hyperfine (3-way comparison) ----

benchmark: $(BYTE_FILES)
	@echo "=== Benchmarks ==="
	@mkdir -p results

binarytrees.bench: binarytrees.byte
	MIN_EXPANSION_WORDSIZE=134217728 \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 16' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 16'

fasta.bench: fasta.byte
	MIN_EXPANSION_WORDSIZE=134217728 \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 2500000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 2500000'

quicksort.bench: quicksort.byte
	MIN_EXPANSION_WORDSIZE=8000000 \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 5000000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 5000000'

fannkuchredux.bench: fannkuchredux.byte
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 11' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 11'

count_change.bench: count_change.byte
	MIN_EXPANSION_WORDSIZE=20000000 \
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 150' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 150'

nbodies.bench: nbodies.byte
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 100000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 100000'

spectralnorm.bench: spectralnorm.byte
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 1000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 1000'

mandelbrot.bench: mandelbrot.byte
	hyperfine --export-csv results/$@.csv \
		--command-name 'verified-gen' '$(VERIFIED_GEN_OCAMLRUN) $< 1000' \
		--command-name 'stock-ocaml'  '$(UNCHANGED_OCAMLRUN) $< 1000'

bench-all: binarytrees.bench fasta.bench quicksort.bench fannkuchredux.bench \
           count_change.bench nbodies.bench spectralnorm.bench mandelbrot.bench

.PHONY: all test benchmark bench-all clean

clean:
	rm -f *.byte *.cmi *.cmo *.o
	rm -rf results
