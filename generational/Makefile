# Makefile for Generational GC
#
# Builds on top of mark-and-sweep (major heap) and common modules.

FSTAR_HOME ?= $(CURDIR)/../fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML       ?= $(KRML_HOME)/krml

FSTAR_LIB  := $(shell $(FSTAR_EXE) --locate_lib 2>/dev/null)

C = ../common
M = ../mark-and-sweep

OUTPUT_DIR  = _output

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

.PHONY: all verify clean

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

# --- Extraction (.krml → C) -------------------------------------------------

EXTRACT_DIR = _extract

EXTRACT_IMPL_MODULES = GC.Gen.Impl.MinorHeap GC.Gen.Impl
EXTRACT_SPEC_MODULES = GC.Gen.Base

ALL_KRML = $(patsubst %,$(OUTPUT_DIR)/%.krml,$(subst .,_,$(EXTRACT_IMPL_MODULES) $(EXTRACT_SPEC_MODULES)))

# Extract impl modules (need higher rlimit)
$(OUTPUT_DIR)/GC_Gen_Impl_MinorHeap.krml: impl/GC.Gen.Impl.MinorHeap.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --z3rlimit 160 --codegen krml --extract_module GC.Gen.Impl.MinorHeap impl/GC.Gen.Impl.MinorHeap.fst

$(OUTPUT_DIR)/GC_Gen_Impl.krml: impl/GC.Gen.Impl.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --z3rlimit 160 --codegen krml --extract_module GC.Gen.Impl impl/GC.Gen.Impl.fst

$(OUTPUT_DIR)/GC_Gen_Base.krml: spec/GC.Gen.Base.fst.checked | $(OUTPUT_DIR)
	$(FSTAR) --codegen krml --extract_module GC.Gen.Base spec/GC.Gen.Base.fst

KRML_FLAGS = \
  -tmpdir $(EXTRACT_DIR) \
  -skip-compilation -skip-linking \
  -bundle 'GC.Gen.Impl+GC.Gen.Impl.MinorHeap+GC.Gen.Base=[rename=GC_Gen_Impl]' \
  -bundle 'GC.Gen.MinorHeap,GC.Spec.*,GC.Lib.*' \
  -bundle 'GC.Impl.*' \
  -bundle 'Prims,FStar.*,Pulse.*' \
  $(patsubst %,-no-prefix %,GC.Gen.Impl GC.Gen.Impl.MinorHeap GC.Gen.Base) \
  -warn-error -2-9-15

$(EXTRACT_DIR):
	@mkdir -p $@

$(EXTRACT_DIR)/GC_Gen_Impl.c: $(ALL_KRML) | $(EXTRACT_DIR)
	$(KRML) $(KRML_FLAGS) $(ALL_KRML)

.PHONY: extract
extract: verify $(EXTRACT_DIR)/GC_Gen_Impl.c
	@echo "=== Extraction complete: $(EXTRACT_DIR)/GC_Gen_Impl.{c,h} ==="

clean:
	rm -f spec/*.checked impl/*.checked
	rm -f .depend .depend.raw
	rm -rf $(OUTPUT_DIR) $(EXTRACT_DIR)
