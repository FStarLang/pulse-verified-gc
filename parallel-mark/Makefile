# Parallel mark: Stages 1-2 (docs/parallel-mark-phase1.md) and Stage 3, the
# model of docs/parallel-mark-design.md (GC.Spec.MarkPar2).
#
# Kept out of the root build.  No module has an admit.
#
#   make verify     Verify the parallel-mark spec modules (Stage 1-2 and 3)
#   make test       Extract to OCaml (Custard) and run random interleavings
#                   against the sequential mark (Stage 1 model)
#   make test2      The same for the Stage 3 model, GC.Spec.MarkPar2
#                   (docs/parallel-mark-design.md)
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

SPEC = spec/GC.Spec.MarkPar.Exec.fst spec/GC.Spec.MarkPar.Model.fst spec/GC.Spec.MarkPar.Recolour.fst spec/GC.Spec.MarkPar.Field.fst spec/GC.Spec.MarkPar.Own.fst spec/GC.Spec.MarkPar.Roots.fst spec/GC.Spec.MarkPar.Inv.fst spec/GC.Spec.MarkPar.End.fst spec/GC.Spec.MarkPar.Seq.fst spec/GC.Spec.MarkPar.Term.fst spec/GC.Spec.MarkPar.fst spec/GC.Spec.MarkPar.Mutants.fst spec/GC.Spec.MarkPar.Witness.fst spec/GC.Spec.MarkPar.WitnessRun.fst spec/GC.Spec.MarkPar.Vacuity.fst spec/GC.Spec.MarkPar.VacuityMark.fst spec/GC.Spec.MarkPar.VacuityTerm.fst

# Stage 3, in dependency order.
SPEC2 = spec/GC.Spec.MarkPar2.Model.fst spec/GC.Spec.MarkPar2.Mutants.fst \
  spec/GC.Spec.MarkPar2.Lists.fst spec/GC.Spec.MarkPar2.Inv.fst spec/GC.Spec.MarkPar2.Upd.fst \
  spec/GC.Spec.MarkPar2.Act.fst spec/GC.Spec.MarkPar2.Step.fst spec/GC.Spec.MarkPar2.Fix.fst \
  spec/GC.Spec.MarkPar2.Main.fst spec/GC.Spec.MarkPar2.Init.fst spec/GC.Spec.MarkPar2.End.fst \
  spec/GC.Spec.MarkPar2.Count.fst spec/GC.Spec.MarkPar2.Foot.fst spec/GC.Spec.MarkPar2.Weight.fst \
  spec/GC.Spec.MarkPar2.Meas.fst spec/GC.Spec.MarkPar2.Term.fst spec/GC.Spec.MarkPar2.fst \
  spec/GC.Spec.MarkPar2.Witness.fst spec/GC.Spec.MarkPar2.Runs.fst spec/GC.Spec.MarkPar2.RunR1.fst \
  spec/GC.Spec.MarkPar2.RunR2.fst spec/GC.Spec.MarkPar2.RunR3.fst spec/GC.Spec.MarkPar2.RunR4.fst \
  spec/GC.Spec.MarkPar2.VacBase.fst spec/GC.Spec.MarkPar2.VacA.fst spec/GC.Spec.MarkPar2.VacB.fst \
  spec/GC.Spec.MarkPar2.VacC.fst spec/GC.Spec.MarkPar2.VacD.fst

.PHONY: verify test test2 check clean
verify:
	for f in $(SPEC) $(SPEC2); do $(FSTAR) $$f || exit 1; done

# One module: gmake check F=spec/GC.Spec.MarkPar.Recolour.fst
check:
	$(FSTAR) $(F)

# Custard (--codegen OCaml) extracts a whole program from its entry points,
# and reads every module from its .checked file, so `verify` must have
# written them.  The roots are the three parallel-mark modules, plus the spec
# functions the driver calls directly.  --custard_split writes one .ml per
# F* module, as the driver expects; GC.Spec.Base.heap is kept by name
# because the driver's types use it.
CUSTARD = \
  --codegen OCaml --custard_split \
  --custard_no_unfold GC.Spec.Base.heap \
  --custard_entry_module GC.Spec.MarkPar.Model \
  --custard_entry_module GC.Spec.MarkPar.Exec \
  --custard_entry_module GC.Spec.MarkPar.Mutants \
  --custard_entry GC.Spec.Base.heap_size \
  --custard_entry GC.Spec.Heap.read_word \
  --custard_entry GC.Spec.Object.makeHeader \
  --custard_entry GC.Spec.Object.getTag \
  --custard_entry GC.Spec.Object.getWosize \
  --custard_entry GC.Spec.Object.getColor \
  --custard_entry GC.Spec.Fields.is_pointer_field \
  --custard_entry FStar.Seq.Base.seq_of_list \
  --custard_entry FStar.Seq.Base.seq_to_list
OUT = _build/ml

test: verify
	rm -rf $(OUT); mkdir -p $(OUT)
	$(FSTAR) $(CUSTARD) --odir $(OUT) spec/GC.Spec.MarkPar.Mutants.fst
	./test/build.sh $(OUT) $(FSTAR_LIB)
	./test/run.sh

CUSTARD2 = \
  --codegen OCaml --custard_split \
  --custard_no_unfold GC.Spec.Base.heap \
  --custard_entry_module GC.Spec.MarkPar.Model \
  --custard_entry_module GC.Spec.MarkPar.Exec \
  --custard_entry_module GC.Spec.MarkPar2.Model \
  --custard_entry_module GC.Spec.MarkPar2.Mutants \
  --custard_entry GC.Spec.Base.heap_size \
  --custard_entry GC.Spec.Heap.read_word \
  --custard_entry GC.Spec.Object.makeHeader \
  --custard_entry GC.Spec.Object.getTag \
  --custard_entry GC.Spec.Object.getWosize \
  --custard_entry GC.Spec.Object.getColor \
  --custard_entry GC.Spec.Fields.is_pointer_field \
  --custard_entry FStar.Seq.Base.seq_of_list \
  --custard_entry FStar.Seq.Base.seq_to_list
OUT2 = _build/ml2

test2: verify
	rm -rf $(OUT2); mkdir -p $(OUT2)
	$(FSTAR) $(CUSTARD2) --odir $(OUT2) spec/GC.Spec.MarkPar2.Mutants.fst
	./test/build.sh $(OUT2) $(FSTAR_LIB) mark_par2_test
	./test/run2.sh

clean:
	rm -rf _build
