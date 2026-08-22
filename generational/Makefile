# Makefile for Generational GC
#
# Builds on top of mark-and-sweep (major heap) and common modules.
# Verification: make verify
# Extraction:   make extract  (requires M&S and common already verified)
# Snapshot:     make snapshot (copies extracted C + krmllib headers)

FSTAR_HOME ?= $(CURDIR)/../fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML       ?= $(KRML_HOME)/krml

FSTAR_LIB  := $(shell $(FSTAR_EXE) --locate_lib 2>/dev/null)

C = ../common
M = ../mark-and-sweep

OUTPUT_DIR  = _output
EXTRACT_DIR = _extract
SNAPSHOT_DIR = snapshot

# Shared checked-file cache (see the root Makefile).  F* writes
# `M.fst.checked` into --cache_dir, which defaults to the current working
# directory, so every build in this repo points at one explicit directory.
CACHE_DIR ?= ../_cache

# --- F* flags ---------------------------------------------------------------

# Z3 version used for all SMT queries (bundled with the F* installation).
Z3_VERSION ?= 4.15.3

# Z3 4.15.3 regression workaround -- see the root Makefile for details.
# Applied per module (EAGER_QI_CHECKED), never globally: at the raised
# eager-instantiation threshold other modules hang instead.
EAGER_QI ?= --z3smtopt '(set-option :smt.qi.eager_threshold 100)'

# Z3 4.15.3 flakiness workaround -- see the top-level Makefile.
RETRY ?= --retry 3

# Hard per-query wall-clock bound; see the root Makefile for the rationale.
# Some Z3 4.15.3 searches never terminate and never charge the rlimit, so
# `--z3rlimit` alone cannot bound them.
Z3_TIMEOUT ?= --z3smtopt '(set-option :timeout 300000)'

FSTAR_FLAGS = \
  $(RETRY) \
  $(Z3_TIMEOUT) \
  --z3version $(Z3_VERSION) \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --warn_error -321 \
  --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  --include spec --include impl \
  --include $(C)/spec --include $(C)/lib --include $(C)/impl \
  --include $(M)/spec --include $(M)/impl

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# --- Sources ----------------------------------------------------------------

SPEC_SRC = $(wildcard spec/*.fst spec/*.fsti)
IMPL_SRC = $(wildcard impl/*.fst impl/*.fsti)

# Exclude SPOT test files from orphan checking (they are tests, not production code)
SPOT_SRC = spec/GC.Gen.SPOT.fst spec/GC.Gen.SPOT.Lemmas.fst impl/GC.Gen.SPOT.Pulse.fst impl/GC.Gen.SPOT.Simple.fst impl/GC.Gen.SPOT.Full.fst
ALL_SRC  = $(filter-out $(SPOT_SRC),$(SPEC_SRC) $(IMPL_SRC))

# All checked files land in one shared cache, so targets are derived from the
# module file name alone.
checked = $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(notdir $(1))))

ROOT_SRC = impl/GC.Gen.Impl.fsti impl/GC.Gen.Impl.fst
ROOT_CHECKED = $(call checked,$(ROOT_SRC))
ALL_CHECKED  = $(call checked,$(ALL_SRC))

# --- Auto-generated dependency graph ----------------------------------------

.depend: Makefile $(ALL_SRC)
	$(FSTAR) --dep full $(ROOT_SRC) --output_deps_to $@.raw
	@awk -v cwd="$$(pwd)/" -v proj="$$(cd .. && pwd)/" ' \
	  { gsub(cwd, ""); gsub(proj, "../") } \
	  /^[^ \t].*:/ { flush(); split($$0, a, ":"); target = a[1]; \
	    keep = (target ~ /\.checked$$/); n = 0; next } \
	  keep { line = $$0; sub(/^[ \t]+/, "", line); sub(/[ \t]*\\?[ \t]*$$/, "", line); \
	    if (line ~ /\.checked$$/) deps[++n] = line } \
	  END { flush() } \
	  function flush() { if (!keep || target == "") return; \
	    print target ": \\"; \
	    for (i=1;i<=n;i++) print "\t" deps[i] (i < n ? " \\" : ""); \
	    print ""; delete deps; n=0 }' $@.raw > $@
	@printf '\nDEP_CHECKED := ' >> $@
	@awk '/^[^ \t].*\.checked:/ { target=$$1; sub(/:$$/, "", target); \
	    print target }' $@ \
	  | sort -u | tr '\n' ' ' >> $@
	@printf '\n' >> $@
	@rm -f $@.raw

# --- Default goal -----------------------------------------------------------

.PHONY: all verify check-orphans extract snapshot clean

all: verify

# Bind every cache target to its source file so `$<` is always the source.
define bind_source
$(CACHE_DIR)/$(notdir $(1)).checked: $(1)
endef
$(foreach s,$(SPEC_SRC) $(IMPL_SRC),$(eval $(call bind_source,$(s))))

-include .depend

# Restrict the dependency closure to this directory's own modules, then map
# each checked file back to the source it was built from.
VERIFY_CHECKED = $(filter $(ALL_CHECKED),$(DEP_CHECKED))
REACHABLE_SRC = $(foreach c,$(VERIFY_CHECKED), \
                  $(filter %/$(patsubst %.checked,%,$(notdir $(c))),$(ALL_SRC)))
ORPHAN_SRC = $(filter-out $(REACHABLE_SRC),$(ALL_SRC))

# --- Pattern rules (verification) -------------------------------------------
#
# One rule for every module; per-module SMT tuning goes through the
# target-specific variable EXTRA_FLAGS.  `private` stops GNU make from
# propagating it to the target's prerequisites.

# Modules that hang at Z3 4.15.3's default eager-instantiation threshold.
#
# Opt-in, not a default: at the raised threshold other modules diverge instead.
# See the top-level Makefile for the rationale.
EAGER_QI_CHECKED = \
  $(CACHE_DIR)/GC.Gen.Cheney.fst.checked \
  $(CACHE_DIR)/GC.Gen.Cheney.Dense.fst.checked \
  $(CACHE_DIR)/GC.Gen.CheneyPreservation.Forwarding.fst.checked \
  $(CACHE_DIR)/GC.Gen.CheneyPreservation.Frame.fst.checked \
  $(CACHE_DIR)/GC.Gen.CheneyPreservation.NonBlueOrigin.fsti.checked \
  $(CACHE_DIR)/GC.Gen.CombinedGraph.fst.checked \
  $(CACHE_DIR)/GC.Gen.MinorCollectForwarding.Edges.fst.checked \
  $(CACHE_DIR)/GC.Gen.MinorCollectForwarding.Reflection.fst.checked \
  $(CACHE_DIR)/GC.Gen.PromoteUpdate.BlueAlloc.fst.checked \
  $(CACHE_DIR)/GC.Gen.Promote.fst.checked \
  $(CACHE_DIR)/GC.Gen.TwoPassEquiv.fst.checked \
  $(CACHE_DIR)/GC.Gen.Impl.Cheney.fst.checked

$(EAGER_QI_CHECKED): private EXTRA_FLAGS = $(EAGER_QI)

# GC.Gen.Promote.fst needs a higher rlimit for abstract heap_size proofs
$(CACHE_DIR)/GC.Gen.Promote.fst.checked: private EXTRA_FLAGS = --z3rlimit_factor 3 $(EAGER_QI)

$(filter-out $(EAGER_QI_CHECKED),$(call checked,$(wildcard impl/*.fst impl/*.fsti))): \
  private EXTRA_FLAGS = --z3rlimit 160

$(filter $(EAGER_QI_CHECKED),$(call checked,$(wildcard impl/*.fst impl/*.fsti))): \
  private EXTRA_FLAGS = --z3rlimit 160 $(EAGER_QI)

$(CACHE_DIR)/%.checked:
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) $(EXTRA_FLAGS) $<

$(OUTPUT_DIR):
	@mkdir -p $@

# Verify the GC.Gen.Impl root closure and fail if new orphan modules appear.
check-orphans:
	@if [ -n "$(strip $(ORPHAN_SRC))" ]; then \
	  echo "=== unreachable generational modules from $(ROOT_SRC) ==="; \
	  printf '  %s\n' $(ORPHAN_SRC); \
	  exit 1; \
	fi

verify: check-orphans $(VERIFY_CHECKED)
	@echo "=== GC.Gen.Impl root closure verified ==="

# === Extraction (.krml → C) =================================================
#
# Extracts generational impl + mark-and-sweep impl + common impl into a
# single C file via KaRaMeL bundling.
#
# Prerequisites: M&S and common .checked files must already exist
# (run `make -C ../mark-and-sweep verify` first if needed).

# --- Modules to extract -----------------------------------------------------

ALL_KRML_MODS = \
  GC.Gen.Impl GC.Gen.Impl.MinorHeap GC.Gen.Impl.Cheney \
  GC.Gen.Impl.Promote GC.Gen.Impl.UpdatePtrs \
  GC.Gen.Base \
  GC.Impl GC.Impl.Fields \
  GC.Impl.MarkBounded GC.Impl.Coalesce \
  GC.Impl.FusedSweepCoalesce GC.Impl.Allocator \
  GC.Impl.ArrayWord GC.Impl.Heap GC.Impl.Object GC.Impl.Stack \
  GC.Spec.ZeroAddr GC.Spec.Base GC.Spec.Heap GC.Spec.Object \
  GC.Lib.Header GC.Lib.Address

ALL_KRML = $(foreach m,$(ALL_KRML_MODS),$(OUTPUT_DIR)/$(subst .,_,$(m)).krml) \
           $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

# --- .krml extraction rules -------------------------------------------------
#
# Pattern rule: _output/GC_Gen_Impl.krml from GC.Gen.Impl.fst
# fstar.exe finds the source via --include paths; prerequisite is verify.

$(OUTPUT_DIR)/%.krml: verify | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --codegen krml \
	  --extract_module $(subst _,.,$*) $(subst _,.,$*).fst

# GC.Impl.ArrayWord — interface-only module (assumed vals, no .fst)
$(OUTPUT_DIR)/GC_Impl_ArrayWord.krml: verify | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --codegen krml \
	  --extract_module GC.Impl.ArrayWord GC.Impl.ArrayWord.fsti

# GC.Spec.ZeroAddr — interface-only module (extern zero_addr, no .fst)
$(OUTPUT_DIR)/GC_Spec_ZeroAddr.krml: verify | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --codegen krml \
	  --extract_module GC.Spec.ZeroAddr GC.Spec.ZeroAddr.fsti

# FStar.Pervasives.Native (tuple types used by allocate) — special case
$(OUTPUT_DIR)/FStar_Pervasives_Native.krml: | $(OUTPUT_DIR)
	$(FSTAR_EXE) --cache_checked_modules --warn_error -321 \
	  --codegen krml --extract_module FStar.Pervasives.Native \
	  --odir $(OUTPUT_DIR) $(FSTAR_LIB)/ulib/FStar.Pervasives.Native.fst

# --- KaRaMeL bundling (.krml → C) ------------------------------------------
#
# Bundle layout:
#   GC_Gen_Impl.{c,h}  — all gen + M&S impl code (one translation unit)
#   Spec/constants      — heap_size_u64, minor_heap_size_u64, color enum (internal)
#
# API (public in header): GC.Gen.Impl, GC.Gen.Impl.MinorHeap, GC.Impl, GC.Impl.Allocator
# Internal (static):      Cheney, Promote, UpdatePtrs, Mark, Sweep, Fields, ...
# Hidden (no C output):   Spec modules, Prims, FStar, Pulse

KRML_FLAGS = \
  -tmpdir $(EXTRACT_DIR) \
  -skip-compilation -skip-linking \
  -bundle 'GC.Gen.Impl+GC.Gen.Impl.MinorHeap+GC.Gen.Impl.Cheney+GC.Gen.Impl.UpdatePtrs+GC.Impl+GC.Impl.Allocator+GC.Impl.MarkBounded=GC.Gen.Impl.*,GC.Impl.*[rename=GC_Gen_Impl]' \
  -bundle 'FStar.Pervasives.Native' \
  -bundle 'GC.Spec.ZeroAddr=GC.Spec.ZeroAddr' \
  -bundle 'GC.Gen.Base,GC.Spec.*,GC.Lib.Header,GC.Lib.Address' \
  $(foreach m,$(ALL_KRML_MODS),-no-prefix $(m)) \
  -warn-error -2-9-15

$(EXTRACT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR)/GC_Gen_Impl.c: $(ALL_KRML) | $(EXTRACT_DIR)
	$(KRML) $(KRML_FLAGS) $(ALL_KRML)

extract: $(EXTRACT_DIR)/GC_Gen_Impl.c
	@echo "=== Extraction complete: $(EXTRACT_DIR)/GC_Gen_Impl.{c,h} ==="

# --- Snapshot ---------------------------------------------------------------

snapshot: extract
	@echo "=== Creating snapshot ==="
	@mkdir -p $(SNAPSHOT_DIR)/krmllib/krml/internal $(SNAPSHOT_DIR)/internal
	@rm -f $(SNAPSHOT_DIR)/internal/*.h
	@cp $(EXTRACT_DIR)/GC_Gen_Impl.c $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/GC_Gen_Impl.h $(SNAPSHOT_DIR)/
	@cp $(EXTRACT_DIR)/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c $(SNAPSHOT_DIR)/ 2>/dev/null || true
	@cp $(EXTRACT_DIR)/GC_Spec_ZeroAddr.h $(SNAPSHOT_DIR)/ 2>/dev/null || true
	@cp $(EXTRACT_DIR)/internal/*.h $(SNAPSHOT_DIR)/internal/ 2>/dev/null || true
	@# Copy krmlinit.h but NOT krmlinit.c (we have a clean replacement in snapshot/)
	@cp $(EXTRACT_DIR)/krmlinit.h $(SNAPSHOT_DIR)/
	@cp $(KRML_HOME)/include/krmllib.h $(SNAPSHOT_DIR)/krmllib/ 2>/dev/null || true
	@cp -r $(KRML_HOME)/krmllib/dist/minimal/* $(SNAPSHOT_DIR)/krmllib/ 2>/dev/null || true
	@cp $(KRML_HOME)/include/krml/*.h $(SNAPSHOT_DIR)/krmllib/krml/ 2>/dev/null || true
	@cp $(KRML_HOME)/include/krml/internal/*.h $(SNAPSHOT_DIR)/krmllib/krml/internal/ 2>/dev/null || true
	@echo "=== Snapshot updated ==="

# --- Cleanup ----------------------------------------------------------------

clean:
	rm -f $(ALL_CHECKED)
	rm -f .depend .depend.raw
	rm -rf $(OUTPUT_DIR) $(EXTRACT_DIR)
