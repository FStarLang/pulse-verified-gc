# Parallel sweep, Phase 1 (see docs/parallel-sweep-phase1.md).
#
# Kept out of the root build: this is Phase 1 work, verified and tested
# here on its own.
#
#   make verify     Verify the parallel-sweep spec modules and the Pulse interface
#   make test       Extract to OCaml (Custard) and compare sweep_par with the sequential pass
#   make clean

ROOT       := $(abspath ..)
FSTAR_HOME ?= $(ROOT)/fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
FSTAR_LIB  := $(shell $(FSTAR_EXE) --locate_lib 2>/dev/null)

CACHE_DIR ?= $(ROOT)/_cache
Z3_VERSION ?= 5.3.0
RETRY ?= --retry 3
Z3_TIMEOUT ?= --z3smtopt '(set-option :timeout 300000)'

INCLUDES = \
  --include $(ROOT)/common/spec --include $(ROOT)/common/lib --include $(ROOT)/common/impl \
  --include $(ROOT)/mark-and-sweep/spec --include $(ROOT)/mark-and-sweep/impl \
  --include spec --include impl

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

SPEC = spec/GC.Spec.SweepPar.Exec.fst spec/GC.Spec.SweepPar.fst spec/GC.Spec.SweepPar.Mutants.fst spec/GC.Spec.SweepPar.Vacuity.fst spec/GC.Spec.SweepPar.Local.fst spec/GC.Spec.SweepPar.Join.fsti
IMPL = impl/GC.Impl.SweepSegment.fsti impl/GC.Impl.SweepPar.fsti

.PHONY: verify test clean
verify:
	for f in $(SPEC) $(IMPL); do $(FSTAR) $$f || exit 1; done

# Custard (--codegen OCaml) extracts a whole program from its entry points,
# and reads every module from its .checked file, so `verify` must have written
# them (see docs/parallel-sweep-phase1.md).  The roots are the three
# parallel-sweep modules, plus the spec functions the driver calls directly.
# --custard_split writes one .ml per F* module, as the driver expects;
# GC.Spec.Base.heap is kept by name because the driver's types use it.
CUSTARD = \
  --codegen OCaml --custard_split \
  --custard_no_unfold GC.Spec.Base.heap \
  --custard_entry_module GC.Spec.SweepPar \
  --custard_entry_module GC.Spec.SweepPar.Exec \
  --custard_entry_module GC.Spec.SweepPar.Mutants \
  --custard_entry GC.Spec.Base.heap_size \
  --custard_entry GC.Spec.Heap.read_word \
  --custard_entry GC.Spec.Object.makeHeader \
  --custard_entry GC.Spec.Object.getTag \
  --custard_entry GC.Spec.Fields.is_pointer_field \
  --custard_entry FStar.Seq.Base.seq_of_list \
  --custard_entry FStar.Seq.Base.seq_to_list
OUT = _build/ml

test: verify
	rm -rf $(OUT); mkdir -p $(OUT)
	$(FSTAR) $(CUSTARD) --odir $(OUT) spec/GC.Spec.SweepPar.Mutants.fst
	./test/build.sh $(OUT) $(FSTAR_LIB)
	./test/run.sh

clean:
	rm -rf _build
