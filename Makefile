# Root Makefile for pulse-verified-gc
#
# Single unified build: one `fstar.exe --dep full` scan across ALL sources
# (common + mark-and-sweep + generational).  Enables `make -j8` for truly
# parallel, incremental verification.
#
# Usage:
#   make                Verify all modules
#   make common         Verify common/ only
#   make mark-and-sweep Verify mark-and-sweep/ + common/
#   make generational   Verify generational/ + mark-and-sweep/ + common/
#   make extract        Verify + extract both GCs to C
#   make clean          Clean all build artifacts

FSTAR_HOME ?= $(CURDIR)/fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML       ?= $(KRML_HOME)/krml

FSTAR_LIB  := $(shell $(FSTAR_EXE) --locate_lib 2>/dev/null)

OUTPUT_DIR = _output

# --- Include paths (all directories visible to all modules) -----------------

INCLUDES = \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl

# --- F* base flags ----------------------------------------------------------

FSTAR_FLAGS = \
  --cache_checked_modules \
  --odir $(OUTPUT_DIR) \
  --warn_error -321 \
  --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# --- Sources ----------------------------------------------------------------

COMMON_SRC = $(wildcard common/spec/*.fst common/spec/*.fsti \
                        common/lib/*.fst common/impl/*.fst common/impl/*.fsti)
MS_SRC     = $(wildcard mark-and-sweep/spec/*.fst mark-and-sweep/spec/*.fsti \
                        mark-and-sweep/impl/*.fst mark-and-sweep/impl/*.fsti)
GEN_SRC    = $(wildcard generational/spec/*.fst generational/spec/*.fsti \
                        generational/impl/*.fst generational/impl/*.fsti)
ALL_SRC    = $(COMMON_SRC) $(MS_SRC) $(GEN_SRC)

# --- Auto-generated dependency graph ----------------------------------------

.depend: $(ALL_SRC)
	$(FSTAR) --dep full $(ALL_SRC) --output_deps_to $@.raw
	@awk -v cwd="$$(pwd)/" ' \
	  { gsub(cwd, "") } \
	  /^[^ \t].*:/ { if (n) flush(); \
	    keep = (/\.checked:/) ? 1 : 0; n = 0 } \
	  keep { line = $$0; sub(/^[ \t]+/, "", line); sub(/[ \t]*\\?[ \t]*$$/, "", line); \
	    if (line == "") next; \
	    if (line !~ /:/ && line !~ /^(common|mark-and-sweep|generational)\//) next; \
	    buf[n++] = $$0 } \
	  END { if (n) flush() } \
	  function flush() { if (!n) return; \
	    sub(/[ \t]*\\[ \t]*$$/, "", buf[n-1]); \
	    for (i=0;i<n;i++) print buf[i]; print ""; n=0 }' $@.raw > $@
	@rm -f $@.raw

# --- Default goal (before -include .depend) ---------------------------------

.PHONY: all verify common mark-and-sweep generational extract clean

all: verify

-include .depend

# --- Verification targets ---------------------------------------------------

verify: $(addsuffix .checked,$(ALL_SRC))
	@echo "=== all modules verified ==="

common: $(addsuffix .checked,$(COMMON_SRC))
	@echo "=== common modules verified ==="

mark-and-sweep: $(addsuffix .checked,$(COMMON_SRC) $(MS_SRC))
	@echo "=== mark-and-sweep modules verified ==="

generational: $(addsuffix .checked,$(ALL_SRC))
	@echo "=== generational modules verified ==="

# --- Pattern rules (verification) -------------------------------------------
# Per-directory flags: different SMT tuning for different proof styles.

# common/ — default flags
common/spec/%.checked: common/spec/%
	$(FSTAR) $<

common/lib/%.checked: common/lib/%
	$(FSTAR) $<

common/impl/%.checked: common/impl/%
	$(FSTAR) --split_queries always $<

# mark-and-sweep/spec — default flags, with specific overrides
mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.fst.checked: mark-and-sweep/spec/GC.Spec.Allocator.Lemmas.fst
	$(FSTAR) --z3rlimit 400 $<

mark-and-sweep/spec/%.checked: mark-and-sweep/spec/%
	$(FSTAR) $<

# mark-and-sweep/impl — split_queries + z3refresh by default, with overrides
mark-and-sweep/impl/GC.Impl.Allocator.fst.checked: mark-and-sweep/impl/GC.Impl.Allocator.fst
	$(FSTAR) --z3rlimit 100 $<

mark-and-sweep/impl/GC.Impl.MarkBounded.fst.checked: mark-and-sweep/impl/GC.Impl.MarkBounded.fst
	$(FSTAR) --z3rlimit 300 --split_queries always --z3refresh $<

mark-and-sweep/impl/%.checked: mark-and-sweep/impl/%
	$(FSTAR) --split_queries always --z3refresh $<

# generational/spec — default flags, with specific overrides
# Promote.fst: --query_stats prevents Z3 context accumulation across queries
generational/spec/GC.Gen.Promote.fst.checked: generational/spec/GC.Gen.Promote.fst
	$(FSTAR) --query_stats --split_queries always $<

generational/spec/GC.Gen.WriteBodyLemmas.fst.checked: generational/spec/GC.Gen.WriteBodyLemmas.fst
	$(FSTAR) --query_stats --split_queries always $<

generational/spec/GC.Gen.MinorHeap.fst.checked: generational/spec/GC.Gen.MinorHeap.fst
	$(FSTAR) --split_queries always $<

generational/spec/GC.Gen.AllocProps.fst.checked: generational/spec/GC.Gen.AllocProps.fst
	$(FSTAR) --query_stats $<

generational/spec/%.checked: generational/spec/%
	$(FSTAR) $<

# generational/impl — higher rlimit + split_queries, with overrides
# GC.Gen.Impl.fst: promote_phase needs lemma-driven NL arithmetic — use split+refresh
generational/impl/GC.Gen.Impl.fst.checked: generational/impl/GC.Gen.Impl.fst
	$(FSTAR) --z3rlimit 200 --split_queries always --z3refresh $<

generational/impl/%.checked: generational/impl/%
	$(FSTAR) --z3rlimit 160 --split_queries always $<

# --- Extraction (mark-and-sweep) --------------------------------------------

$(OUTPUT_DIR):
	@mkdir -p $@

MS_EXTRACT_DIR = mark-and-sweep/_extract

$(MS_EXTRACT_DIR):
	@mkdir -p $@

.PHONY: extract-mark-and-sweep extract-generational extract

extract: extract-mark-and-sweep extract-generational

extract-mark-and-sweep: mark-and-sweep
	+$(MAKE) -C mark-and-sweep extract FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

extract-generational: generational
	+$(MAKE) -C generational extract FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

# --- Clean ------------------------------------------------------------------

clean:
	rm -f .depend .depend.raw
	rm -rf $(OUTPUT_DIR)
	find common mark-and-sweep generational -name '*.checked' -delete 2>/dev/null || true
	rm -rf mark-and-sweep/_output mark-and-sweep/_extract
	rm -rf generational/_output generational/_extract
