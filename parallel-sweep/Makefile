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

SPEC = spec/GC.Spec.SweepPar.Exec.fst spec/GC.Spec.SweepPar.fst spec/GC.Spec.SweepPar.Mutants.fst spec/GC.Spec.SweepPar.Vacuity.fst spec/GC.Spec.SweepPar.Local.fst spec/GC.Spec.SweepPar.Join.fsti spec/GC.Spec.SweepPar.Join.fst spec/GC.Spec.SweepPar.SegLoop.fst
IMPL = impl/GC.Impl.HeapRange.fst impl/GC.Impl.SweepSegment.fsti impl/GC.Impl.SweepSegment.fst impl/GC.Impl.SweepPar.fsti impl/GC.Impl.SweepPar.Prepass.fst impl/GC.Impl.SweepPar.Merge.fst impl/GC.Impl.SweepPar.fst

.PHONY: verify test extract ctest clean
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

# --- C extraction (Custard, as generational/Makefile does) ------------------
#
# Custard (--codegen KrmlC) extracts everything reachable from its roots into
# one Custard.krml; --custard_split keeps one KaRaMeL module per F* module.
# The roots are the parallel pieces and the sequential fused_sweep_coalesce
# they are tested against.  They are named one by one, not with
# --custard_entry_module as generational/Makefile does: that would also root
# GC.Impl.SweepPar.fsti's spec-only bounds_list, which Custard compiles to list
# code that krml then half drops (docs/parallel-sweep-phase1.md, §9).
# `verify` must have written the .checked files.
KRML ?= $(FSTAR_HOME)/karamel/krml
KRML_OUT = _build/krml
EXTRACT  = _build/extract

CUSTARD_C = \
  --codegen KrmlC --custard_split \
  --custard_entry GC.Impl.SweepPar.prepass \
  --custard_entry GC.Impl.SweepPar.merge \
  --custard_entry GC.Impl.SweepPar.sweep_par_seq \
  --custard_entry GC.Impl.SweepSegment.sweep_segment \
  --custard_entry GC.Impl.FusedSweepCoalesce.fused_sweep_coalesce

KRML_MODS = \
  GC.Impl.SweepPar GC.Impl.SweepPar.Prepass GC.Impl.SweepPar.Merge \
  GC.Impl.SweepSegment GC.Impl.HeapRange \
  GC.Impl.FusedSweepCoalesce GC.Impl.Coalesce \
  GC.Impl.ArrayWord GC.Impl.Heap GC.Impl.Object \
  GC.Spec.ZeroAddr GC.Spec.Base GC.Spec.Heap GC.Spec.Object \
  GC.Lib.Header GC.Lib.Address

# One translation unit, GC_SweepPar.{c,h}, with the three entry modules as
# its API, as generational/Makefile bundles GC_Gen_Impl.
KRML_FLAGS = \
  -tmpdir $(EXTRACT) \
  -skip-compilation -skip-linking \
  -bundle 'GC.Impl.SweepPar+GC.Impl.SweepSegment+GC.Impl.FusedSweepCoalesce=GC.Impl.*,Pulse.Lib.Array[rename=GC_SweepPar]' \
  -bundle 'GC.Spec.ZeroAddr=GC.Spec.ZeroAddr' \
  -bundle 'GC.Spec.*,GC.Lib.Header,GC.Lib.Address' \
  $(foreach m,$(KRML_MODS),-no-prefix $(m)) \
  -warn-error -2-9-15

extract: verify
	rm -rf $(KRML_OUT) $(EXTRACT); mkdir -p $(KRML_OUT) $(EXTRACT)
	$(FSTAR) --odir $(KRML_OUT) $(CUSTARD_C) impl/GC.Impl.SweepPar.fst
	$(KRML) $(KRML_FLAGS) $(KRML_OUT)/Custard.krml

# --- The extracted C, tested on its own -------------------------------------
#
# c/sweep_par_ctest.c runs prepass, sweep_segment on each piece in order and
# merge, and sweep_par_seq, against fused_sweep_coalesce on copies of the same
# heaps.  The externs (zero_addr, heap_size_u64, read_u64_le, ...) come from
# the generational snapshot's compat.c, unchanged.
CC ?= cc
COMPAT = $(ROOT)/generational/snapshot
CFLAGS_C = -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable \
  -I$(EXTRACT) -I$(FSTAR_HOME)/karamel/include -I$(FSTAR_HOME)/karamel/krmllib/dist/minimal \
  -I$(COMPAT) -include compat.h
EXTRACTED_C = $(EXTRACT)/GC_SweepPar.c $(EXTRACT)/GC_Spec_GC_Lib_Header_GC_Lib_Address.c $(EXTRACT)/krmlinit.c

ctest: extract
	$(CC) $(CFLAGS_C) $(EXTRACTED_C) $(COMPAT)/compat.c c/sweep_par_ctest.c -o _build/sweep_par_ctest
	./_build/sweep_par_ctest

clean:
	rm -rf _build
