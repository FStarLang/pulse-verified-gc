# Makefile for OCaml 4.14 integration with verified GC
#
# Usage:
#   make setup      — clone & build both OCaml runtimes
#   make test       — run smoke test on all benchmarks
#   make benchmark  — run hyperfine benchmarks
#   make clean      — clean build artifacts

.PHONY: setup test benchmark clean

UNCHANGED_OCAMLC = ocaml-4.14-unchanged/_install/bin/ocamlc
VERIFIED_OCAMLRUN = ocaml-4.14-verified-gc/runtime/ocamlrun
UNCHANGED_OCAMLRUN = ocaml-4.14-unchanged/runtime/ocamlrun

setup:
	./setup.sh

test: setup
	$(MAKE) -C tests test \
		OCAMLC="$(abspath $(UNCHANGED_OCAMLC))" \
		VERIFIED_OCAMLRUN="$(abspath $(VERIFIED_OCAMLRUN))" \
		UNCHANGED_OCAMLRUN="$(abspath $(UNCHANGED_OCAMLRUN))"

benchmark: setup
	$(MAKE) -C tests benchmark \
		OCAMLC="$(abspath $(UNCHANGED_OCAMLC))" \
		VERIFIED_OCAMLRUN="$(abspath $(VERIFIED_OCAMLRUN))" \
		UNCHANGED_OCAMLRUN="$(abspath $(UNCHANGED_OCAMLRUN))"

clean:
	$(MAKE) -C tests clean
	rm -rf ocaml-4.14-unchanged ocaml-4.14-verified-gc
