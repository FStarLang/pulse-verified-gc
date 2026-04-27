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
  --odir $(OUTPUT_DIR) \
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
	$(FSTAR) --z3rlimit 80 $<

$(OUTPUT_DIR):
	@mkdir -p $@

# Verify all modules
verify: $(addsuffix .checked,$(ALL_SRC))
	@echo "=== all generational modules verified ==="

clean:
	rm -f spec/*.checked impl/*.checked
	rm -f .depend .depend.raw
	rm -rf $(OUTPUT_DIR)
