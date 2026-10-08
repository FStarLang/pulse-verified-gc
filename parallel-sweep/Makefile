# Parallel sweep, Phase 1 (see docs/parallel-sweep-phase1.md).
#
# Kept out of the root build on purpose: GC.Spec.SweepPar's correctness
# theorem is stated but closed with `admit` until it is proved.
#
#   make verify     Verify the parallel-sweep spec modules
#   make test       Extract to OCaml and compare sweep_par with the sequential pass
#   make clean

ROOT       := $(abspath ..)
FSTAR_HOME ?= $(ROOT)/fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
FSTAR_LIB  := $(shell $(FSTAR_EXE) --locate_lib 2>/dev/null)

CACHE_DIR ?= $(ROOT)/_cache
Z3_VERSION ?= 4.15.3
RETRY ?= --retry 3
Z3_TIMEOUT ?= --z3smtopt '(set-option :timeout 300000)'

INCLUDES = \
  --include $(ROOT)/common/spec --include $(ROOT)/common/lib --include $(ROOT)/common/impl \
  --include $(ROOT)/mark-and-sweep/spec --include $(ROOT)/mark-and-sweep/impl \
  --include spec

FSTAR_FLAGS = \
  $(RETRY) \
  $(Z3_TIMEOUT) \
  $(OTHERFLAGS) \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --z3version $(Z3_VERSION) \
  --warn_error -321 \
  --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore' \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

SPEC = spec/GC.Spec.SweepPar.Exec.fst spec/GC.Spec.SweepPar.fst spec/GC.Spec.SweepPar.Mutants.fst

.PHONY: verify test clean
verify:
	for f in $(SPEC); do $(FSTAR) $$f || exit 1; done

# Modules extracted to OCaml: the parallel-sweep model and the spec modules
# its executable twins call into.
EXTRACT = '* -FStar -Prims -Pulse -PulseCore'
OUT = _build/ml

test: verify
	mkdir -p $(OUT)
	# 342: GC.Spec.Base.heap_size refers to a noextract definition; build.sh
	# restores it (see there).
	$(FSTAR) --warn_error -342 --codegen OCaml --odir $(OUT) --extract $(EXTRACT) spec/GC.Spec.SweepPar.Mutants.fst
	./test/build.sh $(OUT) $(FSTAR_LIB)
	./test/run.sh

clean:
	rm -rf _build
