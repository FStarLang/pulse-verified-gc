# Benchmarks for verified GC vs stock OCaml
#
# These OCaml programs come from the Computer Language Benchmarks Game and
# were used in Sheera Shamsu et al. (JAR 2025) to evaluate the original
# verified OCaml GC.

OCAMLC          ?= ../ocaml-4.14-unchanged/_install/bin/ocamlc
VERIFIED_OCAMLRUN ?= ../ocaml-4.14-verified-gc/runtime/ocamlrun
UNCHANGED_OCAMLRUN ?= ../ocaml-4.14-unchanged/runtime/ocamlrun

# Compile bytecode using the unchanged compiler, linked with our runtime
%.byte: %.ml
	$(OCAMLC) -custom \
		-cclib -L../ocaml-4.14-verified-gc/runtime/verified_gc \
		-cclib -lvergc \
		-o $@ $<

BENCHMARKS = binarytrees fasta quicksort fannkuchredux count_change nbodies spectralnorm mandelbrot

BYTE_FILES = $(addsuffix .byte, $(BENCHMARKS))

all: $(BYTE_FILES)

# ---- Smoke tests (one run each) ----

test: $(BYTE_FILES)
	@echo "=== Smoke tests ==="
	@echo "--- binarytrees ---"
	MIN_EXPANSION_WORDSIZE=134217728 $(VERIFIED_OCAMLRUN) binarytrees.byte 10
	@echo "--- fasta ---"
	MIN_EXPANSION_WORDSIZE=134217728 $(VERIFIED_OCAMLRUN) fasta.byte 1000
	@echo "--- quicksort ---"
	MIN_EXPANSION_WORDSIZE=8000000 $(VERIFIED_OCAMLRUN) quicksort.byte 10000
	@echo "--- fannkuchredux ---"
	$(VERIFIED_OCAMLRUN) fannkuchredux.byte 7
	@echo "--- count_change ---"
	MIN_EXPANSION_WORDSIZE=20000000 $(VERIFIED_OCAMLRUN) count_change.byte 50
	@echo "--- nbodies ---"
	$(VERIFIED_OCAMLRUN) nbodies.byte 1000
	@echo "--- spectralnorm ---"
	$(VERIFIED_OCAMLRUN) spectralnorm.byte 100
	@echo "--- mandelbrot ---"
	$(VERIFIED_OCAMLRUN) mandelbrot.byte 100
	@echo "=== All smoke tests passed ==="

# ---- Benchmarks with hyperfine ----

benchmark: $(BYTE_FILES)
	@echo "=== Benchmarks ==="
	@mkdir -p results

binarytrees.bench: binarytrees.byte
	MIN_EXPANSION_WORDSIZE=134217728 \
	hyperfine --export-csv results/$@.csv \
		'$(VERIFIED_OCAMLRUN) $< 16' \
		'$(UNCHANGED_OCAMLRUN) $< 16'

fasta.bench: fasta.byte
	MIN_EXPANSION_WORDSIZE=134217728 \
	hyperfine --export-csv results/$@.csv \
		'$(VERIFIED_OCAMLRUN) $< 2500000' \
		'$(UNCHANGED_OCAMLRUN) $< 2500000'

quicksort.bench: quicksort.byte
	MIN_EXPANSION_WORDSIZE=8000000 \
	hyperfine --export-csv results/$@.csv \
		'$(VERIFIED_OCAMLRUN) $< 5000000' \
		'$(UNCHANGED_OCAMLRUN) $< 5000000'

fannkuchredux.bench: fannkuchredux.byte
	hyperfine --export-csv results/$@.csv \
		'$(VERIFIED_OCAMLRUN) $< 11' \
		'$(UNCHANGED_OCAMLRUN) $< 11'

count_change.bench: count_change.byte
	MIN_EXPANSION_WORDSIZE=20000000 \
	hyperfine --export-csv results/$@.csv \
		'$(VERIFIED_OCAMLRUN) $< 150' \
		'$(UNCHANGED_OCAMLRUN) $< 150'

nbodies.bench: nbodies.byte
	hyperfine --export-csv results/$@.csv \
		'$(VERIFIED_OCAMLRUN) $< 100000' \
		'$(UNCHANGED_OCAMLRUN) $< 100000'

spectralnorm.bench: spectralnorm.byte
	hyperfine --export-csv results/$@.csv \
		'$(VERIFIED_OCAMLRUN) $< 1000' \
		'$(UNCHANGED_OCAMLRUN) $< 1000'

mandelbrot.bench: mandelbrot.byte
	hyperfine --export-csv results/$@.csv \
		'$(VERIFIED_OCAMLRUN) $< 1000' \
		'$(UNCHANGED_OCAMLRUN) $< 1000'

bench-all: binarytrees.bench fasta.bench quicksort.bench fannkuchredux.bench \
           count_change.bench nbodies.bench spectralnorm.bench mandelbrot.bench

.PHONY: all test benchmark bench-all clean

clean:
	rm -f *.byte *.cmi *.cmo *.o
	rm -rf results
