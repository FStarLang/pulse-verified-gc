# Makefile for common GC infrastructure
#
# Modules: GC.Spec.* (pure spec), GC.Lib.* (utilities), GC.Impl.* (Pulse impl)
# Hand-written dependency graph for parallel-safe builds (make -j8).

FSTAR_HOME ?= $(CURDIR)/../fstar
FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe

# Include paths
COMMON_INCLUDES = --include lib --include spec

# Pulse library sources
PULSE_LIB ?= $(FSTAR_HOME)/pulse/lib/pulse/lib

# Shared checked-file cache (see the root Makefile).  F* writes `M.fst.checked`
# into --cache_dir, which defaults to the current working directory, so every
# build in this repo points at one explicit directory.
CACHE_DIR ?= ../_cache

# Z3 version used for all SMT queries (bundled with the F* installation).
Z3_VERSION ?= 4.15.3


Z3_FLAGS = --z3version $(Z3_VERSION) --cache_dir $(CACHE_DIR)

# Spec+Lib: pure F*, no Pulse plugin needed
# Z3 4.15.3 flakiness workaround -- see the top-level Makefile.
RETRY ?= --retry 3

# Hard per-query wall-clock bound; see the root Makefile for the rationale.
# Some Z3 4.15.3 searches never terminate and never charge the rlimit, so
# `--z3rlimit` alone cannot bound them.
Z3_TIMEOUT ?= --z3smtopt '(set-option :timeout 300000)'

FSTAR_SPEC_FLAGS = $(RETRY) $(Z3_TIMEOUT) $(Z3_FLAGS) --cache_checked_modules --report_assumes warn \
  $(COMMON_INCLUDES) \
  --already_cached 'FStar -GC'

# Impl: needs Pulse
FSTAR_IMPL_FLAGS = $(RETRY) $(Z3_TIMEOUT) $(Z3_FLAGS) --cache_checked_modules --report_assumes warn \
  $(COMMON_INCLUDES) --include impl --include $(PULSE_LIB) \
  --already_cached 'FStar Pulse -GC'

# Spec+Lib checked files
SPEC_CHECKED = \
  $(CACHE_DIR)/GC.Lib.Header.fst.checked \
  $(CACHE_DIR)/GC.Lib.Address.fst.checked \
  $(CACHE_DIR)/GC.Spec.ZeroAddr.fsti.checked \
  $(CACHE_DIR)/GC.Spec.Base.fsti.checked \
  $(CACHE_DIR)/GC.Spec.Base.fst.checked \
  $(CACHE_DIR)/GC.Spec.Heap.fsti.checked \
  $(CACHE_DIR)/GC.Spec.Heap.fst.checked \
  $(CACHE_DIR)/GC.Spec.Object.fsti.checked \
  $(CACHE_DIR)/GC.Spec.Object.fst.checked \
  $(CACHE_DIR)/GC.Spec.Graph.fst.checked \
  $(CACHE_DIR)/GC.Spec.Fields.fst.checked \
  $(CACHE_DIR)/GC.Spec.DFS.fst.checked \
  $(CACHE_DIR)/GC.Spec.HeapGraph.fst.checked \
  $(CACHE_DIR)/GC.Spec.HeapModel.fst.checked

# Impl checked files
IMPL_CHECKED = \
  $(CACHE_DIR)/GC.Impl.ArrayWord.fsti.checked \
  $(CACHE_DIR)/GC.Impl.Heap.fst.checked \
  $(CACHE_DIR)/GC.Impl.Object.fst.checked \
  $(CACHE_DIR)/GC.Impl.Stack.fsti.checked \
  $(CACHE_DIR)/GC.Impl.Stack.fst.checked

# --- Targets ---

.PHONY: all verify verify-spec verify-impl clean

all: verify

verify: verify-spec
@echo "=== common: all modules verified ==="

verify-spec: $(SPEC_CHECKED)

verify-impl: verify-spec $(IMPL_CHECKED)
@echo "=== common: impl modules verified ==="

# --- Spec+Lib dependencies ---

$(CACHE_DIR)/GC.Lib.Header.fst.checked: lib/GC.Lib.Header.fst

$(CACHE_DIR)/GC.Lib.Address.fst.checked: lib/GC.Lib.Address.fst \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

$(CACHE_DIR)/GC.Spec.ZeroAddr.fsti.checked: spec/GC.Spec.ZeroAddr.fsti

$(CACHE_DIR)/GC.Spec.Base.fsti.checked: spec/GC.Spec.Base.fsti

$(CACHE_DIR)/GC.Spec.Base.fst.checked: spec/GC.Spec.Base.fst \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked \
$(CACHE_DIR)/GC.Spec.ZeroAddr.fsti.checked

$(CACHE_DIR)/GC.Spec.Heap.fsti.checked: spec/GC.Spec.Heap.fsti \
$(CACHE_DIR)/GC.Lib.Header.fst.checked \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

$(CACHE_DIR)/GC.Spec.Heap.fst.checked: spec/GC.Spec.Heap.fst \
$(CACHE_DIR)/GC.Spec.Heap.fsti.checked

$(CACHE_DIR)/GC.Spec.Object.fsti.checked: spec/GC.Spec.Object.fsti \
$(CACHE_DIR)/GC.Lib.Header.fst.checked \
$(CACHE_DIR)/GC.Spec.Heap.fsti.checked \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

$(CACHE_DIR)/GC.Spec.Object.fst.checked: spec/GC.Spec.Object.fst \
$(CACHE_DIR)/GC.Spec.Object.fsti.checked

$(CACHE_DIR)/GC.Spec.Graph.fst.checked: spec/GC.Spec.Graph.fst \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

$(CACHE_DIR)/GC.Spec.Fields.fst.checked: spec/GC.Spec.Fields.fst \
$(CACHE_DIR)/GC.Lib.Header.fst.checked \
$(CACHE_DIR)/GC.Spec.Object.fsti.checked \
$(CACHE_DIR)/GC.Spec.Heap.fsti.checked \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

$(CACHE_DIR)/GC.Spec.DFS.fst.checked: spec/GC.Spec.DFS.fst \
$(CACHE_DIR)/GC.Spec.Graph.fst.checked

$(CACHE_DIR)/GC.Spec.HeapGraph.fst.checked: spec/GC.Spec.HeapGraph.fst \
$(CACHE_DIR)/GC.Lib.Address.fst.checked \
$(CACHE_DIR)/GC.Spec.Graph.fst.checked \
$(CACHE_DIR)/GC.Spec.Object.fsti.checked \
$(CACHE_DIR)/GC.Spec.Heap.fsti.checked \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

$(CACHE_DIR)/GC.Spec.HeapModel.fst.checked: spec/GC.Spec.HeapModel.fst \
$(CACHE_DIR)/GC.Spec.HeapGraph.fst.checked \
$(CACHE_DIR)/GC.Spec.Fields.fst.checked \
$(CACHE_DIR)/GC.Spec.Graph.fst.checked \
$(CACHE_DIR)/GC.Spec.Object.fsti.checked \
$(CACHE_DIR)/GC.Spec.Heap.fsti.checked \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

# --- Impl dependencies ---

$(CACHE_DIR)/GC.Impl.ArrayWord.fsti.checked: impl/GC.Impl.ArrayWord.fsti \
$(CACHE_DIR)/GC.Spec.Heap.fsti.checked \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

$(CACHE_DIR)/GC.Impl.Heap.fst.checked: impl/GC.Impl.Heap.fst \
$(CACHE_DIR)/GC.Impl.ArrayWord.fsti.checked \
$(CACHE_DIR)/GC.Spec.Heap.fsti.checked \
$(CACHE_DIR)/GC.Spec.Base.fsti.checked

$(CACHE_DIR)/GC.Impl.Object.fst.checked: impl/GC.Impl.Object.fst \
$(CACHE_DIR)/GC.Lib.Header.fst.checked \
$(CACHE_DIR)/GC.Spec.Object.fsti.checked \
$(CACHE_DIR)/GC.Impl.Heap.fst.checked

$(CACHE_DIR)/GC.Impl.Stack.fsti.checked: impl/GC.Impl.Stack.fsti \
$(CACHE_DIR)/GC.Impl.Heap.fst.checked

$(CACHE_DIR)/GC.Impl.Stack.fst.checked: impl/GC.Impl.Stack.fst \
$(CACHE_DIR)/GC.Impl.Stack.fsti.checked

# --- Pattern rules ---
#
# All checked files live in one directory, so a single rule serves every
# module and the flag set is selected per target.  `private` stops GNU make
# from propagating the variable to the target's prerequisites.

HDR_CHECKED = $(CACHE_DIR)/GC.Lib.Header.fst.checked

$(filter-out $(HDR_CHECKED),$(SPEC_CHECKED)): private MODE_FLAGS = $(FSTAR_SPEC_FLAGS)
$(HDR_CHECKED):  private MODE_FLAGS = $(FSTAR_SPEC_FLAGS) --z3rlimit 20
$(IMPL_CHECKED): private MODE_FLAGS = $(FSTAR_IMPL_FLAGS)

$(CACHE_DIR)/%.checked:
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) $(MODE_FLAGS) $<

# --- Cleanup ---

clean:
	rm -f $(SPEC_CHECKED) $(IMPL_CHECKED)
	rm -f .depend
