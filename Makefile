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
#   make extract        Verify + extract the generational GC to C
#   make clean          Clean all build artifacts

FSTAR_HOME ?= $(CURDIR)/fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML       ?= $(KRML_HOME)/krml

FSTAR_LIB  := $(shell $(FSTAR_EXE) --locate_lib 2>/dev/null)

# Z3 version used for all SMT queries (bundled with the F* installation).
Z3_VERSION ?= 4.15.3

# Z3 4.15.3 regression workaround.
#
# Z3's default `smt.qi.eager_threshold` is 10.  On 4.15.3 a number of this
# repo's goals send the solver into a search that never terminates *and* never
# charges the rlimit, so `--z3rlimit` cannot bound it; the same queries are
# discharged in seconds by Z3 4.13.3.  Raising the eager-instantiation
# threshold restores 4.13.3-like behaviour for those modules
# (GC.Spec.Allocator.fst: >15min hang -> 81s).
#
# It cannot be applied globally: at the higher threshold *other* modules (e.g.
# GC.Spec.DFS, GC.Spec.Heap) hang instead.  Modules are therefore opted in
# individually, through EAGER_QI_CHECKED below.
EAGER_QI ?= --z3smtopt '(set-option :smt.qi.eager_threshold 100)'

OUTPUT_DIR = _output

# Shared checked-file cache.
#
# F* writes `M.fst.checked` into `--cache_dir`, which defaults to the *current
# working directory* (it no longer drops the file next to the source).  Pointing
# every build at one explicit directory keeps `--dep full` output, the pattern
# rules below, and the per-directory Makefiles all in agreement.
CACHE_DIR ?= _cache

# --- Include paths (all directories visible to all modules) -----------------

INCLUDES = \
  --include common/spec --include common/lib --include common/impl \
  --include mark-and-sweep/spec --include mark-and-sweep/impl \
  --include generational/spec --include generational/impl

# --- F* base flags ----------------------------------------------------------

# Z3 4.15.3 flakiness workaround.
#
# Under Z3 4.15.3 a number of otherwise trivial goals (nat-ness side
# conditions, `x % 8 == 0` alignment facts, `fuel - 1 >= 0`) intermittently
# send the solver down a search path that exhausts the rlimit, in contexts
# where a neighbouring, identical goal is discharged in milliseconds.  Retrying
# the query with a fresh solver clears them.  `--retry N` re-runs a *failing*
# query up to N times and succeeds on the first one that goes through, so it
# costs nothing on the (vast majority of) queries that succeed immediately.
RETRY ?= --retry 3

# Hard per-query wall-clock bound.
#
# Some Z3 4.15.3 searches never terminate *and never charge the rlimit*, so
# `--z3rlimit` cannot bound them and the module hangs indefinitely (measured:
# >90 minutes on GC.Spec.Allocator.Lemmas.Part2 and several generational spec
# modules).  A hard `smt.timeout` turns those hangs back into ordinary query
# failures, which `--retry` can then absorb and which point at a source line
# instead of leaving the build wedged.
#
# 300 s is far above any query in this repository that legitimately succeeds
# (the slowest measured is well under 60 s), so it only ever fires on a runaway
# search.
Z3_TIMEOUT ?= --z3smtopt '(set-option :timeout 300000)'

FSTAR_FLAGS = \
  $(RETRY) \
  $(Z3_TIMEOUT) \
  $(OTHERFLAGS) \
  --cache_checked_modules \
  --cache_dir $(CACHE_DIR) \
  --z3version $(Z3_VERSION) \
  --odir $(OUTPUT_DIR) \
  --warn_error -321 \
  --report_assumes warn \
  --already_cached 'Prims FStar Pulse PulseCore -GC' \
  $(INCLUDES)

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

# --- Sources ----------------------------------------------------------------

# True entry points: only scan dependencies from these roots
# This identifies orphaned/unused files that are not reachable
ROOT_MODULES = \
  mark-and-sweep/impl/GC.Impl.MarkBoundedRootLemmas.fsti \
  mark-and-sweep/impl/GC.Impl.MarkBoundedRootLemmas.fst \
  mark-and-sweep/spec/GC.Spec.FreeList.Sweep.fst \
  generational/impl/GC.Gen.Impl.fsti \
  generational/impl/GC.Gen.Impl.fst

# All sources (for pattern rules and clean targets)
COMMON_SRC = $(wildcard common/spec/*.fst common/spec/*.fsti \
                        common/lib/*.fst common/impl/*.fst common/impl/*.fsti)
MS_SRC     = $(wildcard mark-and-sweep/spec/*.fst mark-and-sweep/spec/*.fsti \
                        mark-and-sweep/impl/*.fst mark-and-sweep/impl/*.fsti)
GEN_SRC    = $(wildcard generational/spec/*.fst generational/spec/*.fsti \
                        generational/impl/*.fst generational/impl/*.fsti)
SPOT_SRC   = $(wildcard spot/*.fst spot/*.fsti)
ALL_SRC    = $(COMMON_SRC) $(MS_SRC) $(GEN_SRC) $(SPOT_SRC)

MS_IMPL_SRC  = $(wildcard mark-and-sweep/impl/*.fst mark-and-sweep/impl/*.fsti)
GEN_IMPL_SRC = $(wildcard generational/impl/*.fst generational/impl/*.fsti)

# --- Auto-generated dependency graph ----------------------------------------

.depend: Makefile $(ROOT_MODULES) $(ALL_SRC)
	@echo "Scanning dependencies from roots: $(ROOT_MODULES)"
	$(FSTAR) --dep full $(ROOT_MODULES) --output_deps_to $@.raw
	@awk -v cwd="$$(pwd)/" ' \
	  { gsub(cwd, "") } \
	  /^[^ \t].*:/ { if (n) flush(); \
	    keep = (/\.checked:/) ? 1 : 0; n = 0 } \
	  /^[A-Z_]+=/ { if (n) flush(); keep = 1; n = 0 } \
	  keep { line = $$0; sub(/^[ \t]+/, "", line); sub(/[ \t]*\\?[ \t]*$$/, "", line); \
	    if (line == "") next; \
	    if (line !~ /:/ && line !~ /^(_cache|common|mark-and-sweep|generational|spot)\// && line !~ /^[A-Z_]+=/) next; \
	    buf[n++] = $$0 } \
	  END { if (n) flush() } \
	  function flush() { if (!n) return; \
	    sub(/[ \t]*\\[ \t]*$$/, "", buf[n-1]); \
	    for (i=0;i<n;i++) print buf[i]; print ""; n=0 }' $@.raw > $@
	@rm -f $@.raw

# --- Default goal (before -include .depend) ---------------------------------

.PHONY: all verify common mark-and-sweep generational extract clean orphans

all: verify

# --- Find orphaned files (not reachable from roots) -------------------------

orphans: .depend
	@echo "=== Orphaned files (not reachable from ROOT_MODULES) ==="
	@echo "Root modules:"
	@for f in $(ROOT_MODULES); do echo "  $$f"; done
	@echo ""
	@echo "Checking for orphans..."
	@find common mark-and-sweep generational spot -name '*.fst' -o -name '*.fsti' | grep -v archive | sort > /tmp/all_files.txt
	@awk '/^_cache\/.*\.checked:/ { getline; gsub(/^[ \t]+|[ \t]*\\?[ \t]*$$/, ""); print }' .depend | sort -u > /tmp/reachable.txt
	@comm -23 /tmp/all_files.txt /tmp/reachable.txt > /tmp/orphans.txt
	@if [ -s /tmp/orphans.txt ]; then \
	  cat /tmp/orphans.txt | while read f; do echo "  $$f"; done; \
	  count=$$(cat /tmp/orphans.txt | wc -l); \
	  echo ""; \
	  echo "Total: $$count orphaned files"; \
	else \
	  echo "  (none - all files are reachable)"; \
	fi
	@rm -f /tmp/all_files.txt /tmp/reachable.txt /tmp/orphans.txt

-include .depend

# --- Verification targets ---------------------------------------------------

# Sources live in several directories but all `.checked` files land in one
# shared cache, so targets are derived from the module file name alone.
checked = $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(notdir $(1))))

COMMON_CHECKED = $(call checked,$(COMMON_SRC))
MS_CHECKED     = $(call checked,$(MS_SRC))
GEN_CHECKED    = $(call checked,$(GEN_SRC))
SPOT_CHECKED   = $(call checked,$(SPOT_SRC))

MS_IMPL_CHECKED  = $(call checked,$(MS_IMPL_SRC))
GEN_IMPL_CHECKED = $(call checked,$(GEN_IMPL_SRC))

# Bind every cache target to its source file.  .depend only covers modules
# reachable from ROOT_MODULES; this makes orphan modules buildable too, and
# guarantees `$<` is always the source (.depend lists it first as well).
define bind_source
$(CACHE_DIR)/$(notdir $(1)).checked: $(1)
endef
$(foreach s,$(ALL_SRC),$(eval $(call bind_source,$(s))))

verify: $(ALL_CHECKED_FILES)
	@echo "=== all modules verified ==="

common: $(COMMON_CHECKED)
	@echo "=== common modules verified ==="

mark-and-sweep: $(COMMON_CHECKED) $(MS_CHECKED)
	@echo "=== mark-and-sweep modules verified ==="

generational: $(COMMON_CHECKED) $(MS_CHECKED) $(GEN_CHECKED) $(SPOT_CHECKED)
	@echo "=== generational modules verified ==="

# --- Verification rule ------------------------------------------------------
#
# One rule for every module; the prerequisites (and hence `$<`, the source
# file) come from .depend.  Per-module SMT tuning is applied through the
# target-specific variable EXTRA_FLAGS.
#
# `private` is essential: without it GNU make propagates a target-specific
# variable to every prerequisite, so one module's tuning would leak into its
# whole dependency cone.

$(CACHE_DIR)/%.checked:
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) $(EXTRA_FLAGS) $<

# --- Per-module SMT tuning --------------------------------------------------

# GC.Lib.Header needs a little more rlimit for bitvector mask reasoning.
HDR_CHECKED       = $(CACHE_DIR)/GC.Lib.Header.fst.checked
# mark-and-sweep/impl overrides
MS_ALLOC_CHECKED  = $(CACHE_DIR)/GC.Impl.Allocator.fst.checked
MS_MARKB_CHECKED  = $(CACHE_DIR)/GC.Impl.MarkBounded.fst.checked
# generational/spec overrides: --query_stats prevents Z3 context accumulation
GEN_QSTATS_CHECKED = $(CACHE_DIR)/GC.Gen.Promote.fst.checked \
                     $(CACHE_DIR)/GC.Gen.WriteBodyLemmas.fst.checked
# generational/impl root: promote_phase needs lemma-driven NL arithmetic
GEN_ROOT_CHECKED  = $(CACHE_DIR)/GC.Gen.Impl.fst.checked

# Modules that hang at Z3 4.15.3's default eager-instantiation threshold.
#
# This is an opt-in, not a default: at the raised threshold *other* modules
# (GC.Spec.DFS, GC.Spec.Heap) diverge instead.  Every entry below was measured
# to hang -- in a way `--z3rlimit` cannot bound, because the search never
# charges the rlimit -- without it, and to complete quickly with it.  E.g.
# GC.Gen.CheneyPreservation.Forwarding: >90 min -> 3m13s.
EAGER_QI_CHECKED = \
  $(CACHE_DIR)/GC.Spec.Allocator.fst.checked \
  $(CACHE_DIR)/GC.Spec.Allocator.Lemmas.Part2.fst.checked \
  $(CACHE_DIR)/GC.Impl.Allocator.fst.checked \
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

$(EAGER_QI_CHECKED):   private EXTRA_FLAGS = $(EAGER_QI)
$(HDR_CHECKED):        private EXTRA_FLAGS = --z3rlimit 20
$(MS_ALLOC_CHECKED):   private EXTRA_FLAGS = --z3rlimit 100 $(EAGER_QI)
$(MS_MARKB_CHECKED):   private EXTRA_FLAGS = --z3rlimit 300 --z3refresh
$(GEN_QSTATS_CHECKED): private EXTRA_FLAGS = --query_stats $(EAGER_QI)
$(GEN_ROOT_CHECKED):   private EXTRA_FLAGS = --z3rlimit 200 --z3refresh

# mark-and-sweep/impl — z3refresh by default
$(filter-out $(MS_ALLOC_CHECKED) $(MS_MARKB_CHECKED),$(MS_IMPL_CHECKED)): \
  private EXTRA_FLAGS = --z3refresh

# generational/impl — higher rlimit by default
$(filter-out $(GEN_ROOT_CHECKED) $(EAGER_QI_CHECKED),$(GEN_IMPL_CHECKED)): \
  private EXTRA_FLAGS = --z3rlimit 160

$(filter $(GEN_IMPL_CHECKED),$(EAGER_QI_CHECKED)): \
  private EXTRA_FLAGS = --z3rlimit 160 $(EAGER_QI)

# --- Extraction --------------------------------------------------------------
#
# One collector is extracted: the generational one, into generational/snapshot.
# Its major collections run the mark-and-sweep code verbatim, so every C
# function the mark-and-sweep directory could emit is already in that snapshot;
# a second bundle would only be a second thing to keep in sync.

$(OUTPUT_DIR):
	@mkdir -p $@

.PHONY: extract

extract: generational
	+$(MAKE) -C generational extract FSTAR_HOME=$(FSTAR_HOME) KRML_HOME=$(KRML_HOME)

# --- Dependence graph / unused-definition report -----------------------------
#
# `fstar-depgraph` (tools/depgraph) reads the .checked files in $(CACHE_DIR)
# directly -- no re-verification -- and emits an offline HTML dependence viewer
# plus a report of definitions that are unreachable from the roots.
#
# Roots are the two things we actually want to keep: the **interface** of the
# single extraction bundle, and the **top-level correctness theorems**.  Anything not
# reachable from those is dead weight.  SPOT scenario modules are added as roots
# too (DEPGRAPH_SPOT_ROOTS) because they are part of the repo's build; drop them
# from the root set to see what only SPOT keeps alive.
#
# NOTE on OCAMLPATH: the tool links against the *in-tree* fstar.compiler findlib
# library and unmarshals .checked files, so the library must be the same F*
# build that produced them (cache version + OCaml ABI).  $(FSTAR_HOME) is a
# binary nightly whose .cmi files are compiled against a different OCaml 5.3.0
# build than a typical local opam switch, so linking against it usually fails
# with "inconsistent assumptions over interface Stdlib".  In that case build F*
# from source at the *same commit* as $(FSTAR_HOME) and point DEPGRAPH_OCAMLPATH
# at its out/lib:
#
#   git -C <fstar-checkout> worktree add /tmp/fstar-src $$($(FSTAR_EXE) --version | sed -n 's/^commit=//p')
#   make -C /tmp/fstar-src stage2 -j FSTAR_USE_KRML_EXE=1 KRML_EXE=$$(command -v krml)
#   make depgraph DEPGRAPH_OCAMLPATH=/tmp/fstar-src/stage2/out/lib
#
# `make depgraph-check` verifies the cache version matches before running.

DEPGRAPH_DIR       = tools/depgraph
DEPGRAPH_EXE       = $(DEPGRAPH_DIR)/_build/default/src/fstar_depgraph.exe
DEPGRAPH_OUT      ?= _depgraph
DEPGRAPH_OCAMLPATH ?= $(FSTAR_HOME)/lib

# The interface: the API surface of the one extraction bundle, i.e. exactly the
# modules named on the left of `-bundle ...=` in generational/Makefile.  Modules
# they call (GC.Impl.Heap, GC.Impl.Object, GC.Impl.Stack, GC.Impl.Fields,
# GC.Impl.Coalesce, GC.Impl.FusedSweepCoalesce, ...) are reached transitively
# and must NOT be listed here -- listing a module as a root asserts that we want
# to keep it even if nothing calls it, which is how dead code survived before.
DEPGRAPH_IFACE_ROOTS = \
  GC.Impl GC.Impl.Allocator GC.Impl.MarkBounded \
  GC.Gen.Impl GC.Gen.Impl.Cheney GC.Gen.Impl.MinorHeap GC.Gen.Impl.UpdatePtrs \
  GC.Gen.Impl.Promote

# The top-level theorems.  These are results, so nothing refers to them; they
# have to be named explicitly or the whole proof development looks dead.
DEPGRAPH_THEOREM_ROOTS = \
  GC.Spec.Correctness GC.Spec.MarkBoundedCorrectness GC.Gen.CheneyCorrectness \
  GC.Impl.MarkBoundedRootLemmas GC.Spec.FreeList.Sweep

DEPGRAPH_SPOT_ROOTS = $(sort $(basename $(notdir $(wildcard spot/GC.SPOT.*.fst))))

DEPGRAPH_ROOTS ?= $(DEPGRAPH_IFACE_ROOTS) $(DEPGRAPH_THEOREM_ROOTS) $(DEPGRAPH_SPOT_ROOTS)

.PHONY: depgraph depgraph-build depgraph-check depgraph-inventory \
        depgraph-prune depgraph-clean

depgraph-build:
	@command -v dune >/dev/null || { echo "ERROR: dune not found; depgraph needs OCaml + dune."; exit 1; }
	cd $(DEPGRAPH_DIR) && OCAMLPATH=$(abspath $(DEPGRAPH_OCAMLPATH)) dune build 2>&1 | \
	  sed -e 's/^/  /' ; \
	  test -x $(abspath $(DEPGRAPH_EXE))

depgraph-check:
	@want=$$($(FSTAR_EXE) --print_cache_version | grep -oE '[0-9]+$$'); \
	echo "$(FSTAR_HOME) produces cache version $$want"; \
	echo "checked files in $(CACHE_DIR): $$(ls $(CACHE_DIR)/*.checked 2>/dev/null | wc -l)"

depgraph: depgraph-build
	$(DEPGRAPH_EXE) \
	  $(foreach r,$(DEPGRAPH_ROOTS),--root $(r)) \
	  --include $(CACHE_DIR) \
	  --source common --source mark-and-sweep --source generational --source spot \
	  --out $(DEPGRAPH_OUT)
	@echo ""
	@echo "Viewer:  $(DEPGRAPH_OUT)/index.html   (open directly, no web server needed)"
	@echo "Report:  $(DEPGRAPH_OUT)/unused-report.txt"

# Regenerate docs/dead-code-inventory.md from the last `make depgraph` run.
DEPGRAPH_INVENTORY ?= docs/dead-code-inventory.md

depgraph-inventory:
	@test -f $(DEPGRAPH_OUT)/unused-report.txt || { echo "ERROR: run 'make depgraph' first."; exit 1; }
	python3 $(DEPGRAPH_DIR)/unused_inventory.py $(DEPGRAPH_OUT) $(DEPGRAPH_INVENTORY)

# Delete every definition the last `make depgraph` run reported unreachable.
# `DEPGRAPH_PRUNE_FLAGS=--dry-run` reports without touching anything.
depgraph-prune:
	@test -f $(DEPGRAPH_OUT)/unused-report.txt || { echo "ERROR: run 'make depgraph' first."; exit 1; }
	python3 $(DEPGRAPH_DIR)/prune.py $(DEPGRAPH_OUT) . $(DEPGRAPH_PRUNE_FLAGS)
	@echo ""
	@echo "Now re-verify:  make -k -j24 && make -C spot -j24 && make extract"

depgraph-clean:
	rm -rf $(DEPGRAPH_OUT) $(DEPGRAPH_DIR)/_build# --- Clean ------------------------------------------------------------------

clean:
	rm -f .depend .depend.raw
	rm -rf $(OUTPUT_DIR) $(CACHE_DIR)
	find common mark-and-sweep generational spot -name '*.checked' -delete 2>/dev/null || true
	rm -rf mark-and-sweep/_output
	rm -rf generational/_output generational/_extract
