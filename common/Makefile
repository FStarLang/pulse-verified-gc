# Makefile for common GC infrastructure
#
# Modules: GC.Spec.* (pure spec), GC.Lib.* (utilities), GC.Impl.* (Pulse impl)
# Hand-written dependency graph for parallel-safe builds (make -j8).

FSTAR_HOME ?= $(CURDIR)/../FStar
FSTAR ?= $(FSTAR_HOME)/bin/fstar.exe

# Include paths
COMMON_INCLUDES = --include lib --include spec

# Pulse library sources
PULSE_LIB ?= $(FSTAR_HOME)/pulse/lib/pulse/lib

# Spec+Lib: pure F*, no Pulse plugin needed
FSTAR_SPEC_FLAGS = --cache_checked_modules --report_assumes warn \
  $(COMMON_INCLUDES) \
  --already_cached 'FStar -GC'

# Impl: needs Pulse
FSTAR_IMPL_FLAGS = --cache_checked_modules --report_assumes warn \
  $(COMMON_INCLUDES) --include impl --include $(PULSE_LIB) \
  --already_cached 'FStar Pulse -GC'

# Spec+Lib checked files
SPEC_CHECKED = \
  lib/GC.Lib.Header.fst.checked \
  lib/GC.Lib.Address.fst.checked \
  spec/GC.Spec.Base.fsti.checked \
  spec/GC.Spec.Base.fst.checked \
  spec/GC.Spec.Heap.fsti.checked \
  spec/GC.Spec.Heap.fst.checked \
  spec/GC.Spec.Object.fsti.checked \
  spec/GC.Spec.Object.fst.checked \
  spec/GC.Spec.Graph.fst.checked \
  spec/GC.Spec.Fields.fst.checked \
  spec/GC.Spec.DFS.fst.checked \
  spec/GC.Spec.HeapGraph.fst.checked \
  spec/GC.Spec.HeapModel.fst.checked

# Impl checked files
IMPL_CHECKED = \
  impl/GC.Impl.Heap.fst.checked \
  impl/GC.Impl.Object.fst.checked \
  impl/GC.Impl.Stack.fsti.checked \
  impl/GC.Impl.Stack.fst.checked

# --- Targets ---

.PHONY: all verify verify-spec verify-impl clean

all: verify

verify: verify-spec
@echo "=== common: all modules verified ==="

verify-spec: $(SPEC_CHECKED)

verify-impl: verify-spec $(IMPL_CHECKED)
@echo "=== common: impl modules verified ==="

# --- Spec+Lib dependencies ---

lib/GC.Lib.Header.fst.checked: lib/GC.Lib.Header.fst

lib/GC.Lib.Address.fst.checked: lib/GC.Lib.Address.fst \
spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.Base.fsti.checked: spec/GC.Spec.Base.fsti

spec/GC.Spec.Base.fst.checked: spec/GC.Spec.Base.fst \
spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.Heap.fsti.checked: spec/GC.Spec.Heap.fsti \
lib/GC.Lib.Header.fst.checked \
spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.Heap.fst.checked: spec/GC.Spec.Heap.fst \
spec/GC.Spec.Heap.fsti.checked

spec/GC.Spec.Object.fsti.checked: spec/GC.Spec.Object.fsti \
lib/GC.Lib.Header.fst.checked \
spec/GC.Spec.Heap.fsti.checked \
spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.Object.fst.checked: spec/GC.Spec.Object.fst \
spec/GC.Spec.Object.fsti.checked

spec/GC.Spec.Graph.fst.checked: spec/GC.Spec.Graph.fst \
spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.Fields.fst.checked: spec/GC.Spec.Fields.fst \
lib/GC.Lib.Header.fst.checked \
spec/GC.Spec.Object.fsti.checked \
spec/GC.Spec.Heap.fsti.checked \
spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.DFS.fst.checked: spec/GC.Spec.DFS.fst \
spec/GC.Spec.Graph.fst.checked

spec/GC.Spec.HeapGraph.fst.checked: spec/GC.Spec.HeapGraph.fst \
lib/GC.Lib.Address.fst.checked \
spec/GC.Spec.Graph.fst.checked \
spec/GC.Spec.Object.fsti.checked \
spec/GC.Spec.Heap.fsti.checked \
spec/GC.Spec.Base.fsti.checked

spec/GC.Spec.HeapModel.fst.checked: spec/GC.Spec.HeapModel.fst \
spec/GC.Spec.HeapGraph.fst.checked \
spec/GC.Spec.Fields.fst.checked \
spec/GC.Spec.Graph.fst.checked \
spec/GC.Spec.Object.fsti.checked \
spec/GC.Spec.Heap.fsti.checked \
spec/GC.Spec.Base.fsti.checked

# --- Impl dependencies ---

impl/GC.Impl.Heap.fst.checked: impl/GC.Impl.Heap.fst \
spec/GC.Spec.Heap.fsti.checked \
spec/GC.Spec.Base.fsti.checked

impl/GC.Impl.Object.fst.checked: impl/GC.Impl.Object.fst \
lib/GC.Lib.Header.fst.checked \
spec/GC.Spec.Object.fsti.checked \
impl/GC.Impl.Heap.fst.checked

impl/GC.Impl.Stack.fsti.checked: impl/GC.Impl.Stack.fsti \
impl/GC.Impl.Heap.fst.checked

impl/GC.Impl.Stack.fst.checked: impl/GC.Impl.Stack.fst \
impl/GC.Impl.Stack.fsti.checked

# --- Pattern rules ---

spec/%.checked: spec/%
	$(FSTAR) $(FSTAR_SPEC_FLAGS) $<

lib/%.checked: lib/%
	$(FSTAR) $(FSTAR_SPEC_FLAGS) $<

impl/%.checked: impl/%
	$(FSTAR) $(FSTAR_IMPL_FLAGS) $<

# --- Cleanup ---

clean:
	rm -f spec/*.checked* lib/*.checked* impl/*.checked*
	rm -f .depend
