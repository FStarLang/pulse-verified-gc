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
  GC.Impl GC.Impl.Fields GC.Impl.Closure GC.Impl.Mark \
  GC.Impl.MarkBounded GC.Impl.Sweep GC.Impl.Coalesce \
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
