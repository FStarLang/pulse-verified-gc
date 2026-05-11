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

# --- F* flags ---------------------------------------------------------------

FSTAR_FLAGS = \
  --cache_checked_modules \
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
ALL_SRC  = $(SPEC_SRC) $(IMPL_SRC)

# --- Auto-generated dependency graph ----------------------------------------

.depend: $(ALL_SRC)
	$(FSTAR) --dep full $(ALL_SRC) --output_deps_to $@.raw
	@awk -v cwd="$$(pwd)/" -v proj="$$(cd .. && pwd)/" ' \
	  { gsub(cwd, ""); gsub(proj, "../") } \
	  /^[^ \t].*:/ { if (n) flush(); \
	    keep = (/\.checked:/) ? 1 : 0; n = 0 } \
	  keep { line =$$0; sub(/^[ \t]+/, "", line); sub(/[ \t]*\\?[ \t]*$$/, "", line); \
	    if (line == "") next; \
	    if (line !~ /:/ && line !~ /^(spec|impl|_output)\/|^\.\.\//) next; \
	    buf[n++] = $$0 } \
	  END { if (n) flush() } \
	  function flush() { if (!n) return; \
	    sub(/[ \t]*\\[ \t]*$$/, "", buf[n-1]); \
	    for (i=0;i<n;i++) print buf[i]; print ""; n=0 }' $@.raw > $@
	@rm -f $@.raw

# --- Default goal -----------------------------------------------------------

.PHONY: all verify extract snapshot clean

all: verify

-include .depend

# --- Pattern rules (verification) -------------------------------------------

spec/%.checked: spec/%
	$(FSTAR) $<

impl/%.checked: impl/%
	$(FSTAR) --z3rlimit 160 --split_queries always $<

$(OUTPUT_DIR):
	@mkdir -p $@

# Verify all modules
verify: $(addsuffix .checked,$(ALL_SRC))
	@echo "=== all generational modules verified ==="

# === Extraction (.krml → C) =================================================
#
# Extracts both generational impl + mark-and-sweep impl + common impl
# into a single C file via KaRaMeL bundling.
#
# Prerequisites: M&S and common .checked files must already exist
# (run `make -C ../mark-and-sweep verify` first if needed).

# --- .krml extraction rules -------------------------------------------------

# Generational impl modules
$(OUTPUT_DIR)/GC_Gen_Impl.krml: impl/GC.Gen.Impl.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --z3rlimit 160 --split_queries always \
	  --codegen krml --extract_module GC.Gen.Impl impl/GC.Gen.Impl.fst

$(OUTPUT_DIR)/GC_Gen_Impl_MinorHeap.krml: impl/GC.Gen.Impl.MinorHeap.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --z3rlimit 160 --split_queries always \
	  --codegen krml --extract_module GC.Gen.Impl.MinorHeap impl/GC.Gen.Impl.MinorHeap.fst

$(OUTPUT_DIR)/GC_Gen_Impl_Cheney.krml: impl/GC.Gen.Impl.Cheney.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --z3rlimit 160 --split_queries always \
	  --codegen krml --extract_module GC.Gen.Impl.Cheney impl/GC.Gen.Impl.Cheney.fst

$(OUTPUT_DIR)/GC_Gen_Impl_Promote.krml: impl/GC.Gen.Impl.Promote.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --z3rlimit 160 --split_queries always \
	  --codegen krml --extract_module GC.Gen.Impl.Promote impl/GC.Gen.Impl.Promote.fst

$(OUTPUT_DIR)/GC_Gen_Impl_UpdatePtrs.krml: impl/GC.Gen.Impl.UpdatePtrs.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --z3rlimit 160 --split_queries always \
	  --codegen krml --extract_module GC.Gen.Impl.UpdatePtrs impl/GC.Gen.Impl.UpdatePtrs.fst

# Generational spec (constants: minor_heap_size_u64, max_young_wosize_u64)
$(OUTPUT_DIR)/GC_Gen_Base.krml: spec/GC.Gen.Base.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Gen.Base spec/GC.Gen.Base.fst

# Mark-and-sweep impl modules
$(OUTPUT_DIR)/GC_Impl.krml: $(M)/impl/GC.Impl.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl $(M)/impl/GC.Impl.fst

$(OUTPUT_DIR)/GC_Impl_Fields.krml: $(M)/impl/GC.Impl.Fields.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Fields $(M)/impl/GC.Impl.Fields.fst

$(OUTPUT_DIR)/GC_Impl_Closure.krml: $(M)/impl/GC.Impl.Closure.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Closure $(M)/impl/GC.Impl.Closure.fst

$(OUTPUT_DIR)/GC_Impl_Mark.krml: $(M)/impl/GC.Impl.Mark.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Mark $(M)/impl/GC.Impl.Mark.fst

$(OUTPUT_DIR)/GC_Impl_MarkBounded.krml: $(M)/impl/GC.Impl.MarkBounded.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.MarkBounded $(M)/impl/GC.Impl.MarkBounded.fst

$(OUTPUT_DIR)/GC_Impl_Sweep.krml: $(M)/impl/GC.Impl.Sweep.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Sweep $(M)/impl/GC.Impl.Sweep.fst

$(OUTPUT_DIR)/GC_Impl_Coalesce.krml: $(M)/impl/GC.Impl.Coalesce.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Coalesce $(M)/impl/GC.Impl.Coalesce.fst

$(OUTPUT_DIR)/GC_Impl_FusedSweepCoalesce.krml: $(M)/impl/GC.Impl.FusedSweepCoalesce.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.FusedSweepCoalesce $(M)/impl/GC.Impl.FusedSweepCoalesce.fst

$(OUTPUT_DIR)/GC_Impl_Allocator.krml: $(M)/impl/GC.Impl.Allocator.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Allocator $(M)/impl/GC.Impl.Allocator.fst

# Common impl modules
$(OUTPUT_DIR)/GC_Impl_Heap.krml: $(C)/impl/GC.Impl.Heap.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Heap $(C)/impl/GC.Impl.Heap.fst

$(OUTPUT_DIR)/GC_Impl_Object.krml: $(C)/impl/GC.Impl.Object.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Object $(C)/impl/GC.Impl.Object.fst

$(OUTPUT_DIR)/GC_Impl_Stack.krml: $(C)/impl/GC.Impl.Stack.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Impl.Stack $(C)/impl/GC.Impl.Stack.fst

# Spec / common type modules (constants + types needed by krml)
$(OUTPUT_DIR)/GC_Spec_Base.krml: $(C)/spec/GC.Spec.Base.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Spec.Base $(C)/spec/GC.Spec.Base.fst

$(OUTPUT_DIR)/GC_Spec_Heap.krml: $(C)/spec/GC.Spec.Heap.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Spec.Heap $(C)/spec/GC.Spec.Heap.fst

$(OUTPUT_DIR)/GC_Spec_Object.krml: $(C)/spec/GC.Spec.Object.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Spec.Object $(C)/spec/GC.Spec.Object.fst

$(OUTPUT_DIR)/GC_Lib_Header.krml: $(C)/lib/GC.Lib.Header.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Lib.Header $(C)/lib/GC.Lib.Header.fst

$(OUTPUT_DIR)/GC_Lib_Address.krml: $(C)/lib/GC.Lib.Address.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) \
	  --codegen krml --extract_module GC.Lib.Address $(C)/lib/GC.Lib.Address.fst

# FStar.Pervasives.Native (tuple types used by allocate)
$(OUTPUT_DIR)/FStar_Pervasives_Native.krml: | $(OUTPUT_DIR)
	$(FSTAR_EXE) --cache_checked_modules --warn_error -321 \
	  --codegen krml --extract_module FStar.Pervasives.Native \
	  --odir $(OUTPUT_DIR) $(FSTAR_LIB)/ulib/FStar.Pervasives.Native.fst

# --- All .krml files --------------------------------------------------------

ALL_KRML = \
  $(OUTPUT_DIR)/GC_Gen_Impl.krml \
  $(OUTPUT_DIR)/GC_Gen_Impl_MinorHeap.krml \
  $(OUTPUT_DIR)/GC_Gen_Impl_Cheney.krml \
  $(OUTPUT_DIR)/GC_Gen_Impl_Promote.krml \
  $(OUTPUT_DIR)/GC_Gen_Impl_UpdatePtrs.krml \
  $(OUTPUT_DIR)/GC_Gen_Base.krml \
  $(OUTPUT_DIR)/GC_Impl.krml \
  $(OUTPUT_DIR)/GC_Impl_Fields.krml \
  $(OUTPUT_DIR)/GC_Impl_Closure.krml \
  $(OUTPUT_DIR)/GC_Impl_Mark.krml \
  $(OUTPUT_DIR)/GC_Impl_MarkBounded.krml \
  $(OUTPUT_DIR)/GC_Impl_Sweep.krml \
  $(OUTPUT_DIR)/GC_Impl_Coalesce.krml \
  $(OUTPUT_DIR)/GC_Impl_FusedSweepCoalesce.krml \
  $(OUTPUT_DIR)/GC_Impl_Allocator.krml \
  $(OUTPUT_DIR)/GC_Impl_Heap.krml \
  $(OUTPUT_DIR)/GC_Impl_Object.krml \
  $(OUTPUT_DIR)/GC_Impl_Stack.krml \
  $(OUTPUT_DIR)/GC_Spec_Base.krml \
  $(OUTPUT_DIR)/GC_Spec_Heap.krml \
  $(OUTPUT_DIR)/GC_Spec_Object.krml \
  $(OUTPUT_DIR)/GC_Lib_Header.krml \
  $(OUTPUT_DIR)/GC_Lib_Address.krml \
  $(OUTPUT_DIR)/FStar_Pervasives_Native.krml

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
  -bundle 'GC.Gen.Impl+GC.Gen.Impl.MinorHeap+GC.Impl+GC.Impl.Allocator=GC.Gen.Impl.*,GC.Impl.*[rename=GC_Gen_Impl]' \
  -bundle 'FStar.Pervasives.Native' \
  -bundle 'GC.Gen.Base,GC.Spec.*,GC.Lib.Header,GC.Lib.Address' \
  $(patsubst %,-no-prefix %, \
    GC.Gen.Impl GC.Gen.Impl.MinorHeap GC.Gen.Impl.Cheney \
    GC.Gen.Impl.Promote GC.Gen.Impl.UpdatePtrs GC.Gen.Base \
    GC.Impl GC.Impl.Mark GC.Impl.MarkBounded GC.Impl.Sweep \
    GC.Impl.Fields GC.Impl.Closure GC.Impl.Heap GC.Impl.Object \
    GC.Impl.Stack GC.Impl.Allocator \
    GC.Impl.FusedSweepCoalesce GC.Impl.Coalesce) \
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
	rm -f spec/*.checked impl/*.checked
	rm -f .depend .depend.raw
	rm -rf $(OUTPUT_DIR) $(EXTRACT_DIR)
