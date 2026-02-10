# Makefile for common GC infrastructure
FSTAR ?= fstar.exe
FSTAR_FLAGS = --include Lib --include Spec --cache_checked_modules

COMMON_LIB = Lib/Pulse.Lib.Header.fst Lib/Pulse.Lib.Address.fst
COMMON_IFACES = Spec/Pulse.Spec.GC.Base.fsti Spec/Pulse.Spec.GC.Heap.fsti Spec/Pulse.Spec.GC.Object.fsti
COMMON_SPEC = Spec/Pulse.Spec.GC.Base.fst Spec/Pulse.Spec.GC.Heap.fst Spec/Pulse.Spec.GC.Object.fst \
              Spec/Pulse.Spec.GC.Graph.fst Spec/Pulse.Spec.GC.DFS.fst Spec/Pulse.Spec.GC.HeapGraph.fst \
              Spec/Pulse.Spec.GC.Fields.fst Spec/Pulse.Spec.GC.HeapModel.fst
ALL_MODULES = $(COMMON_LIB) $(COMMON_IFACES) $(COMMON_SPEC)

# Pulse Lib modules require Pulse tooling (--load_cmxs pulse)
PULSE_FLAGS = --include Pulse.Lib.GC --load_cmxs pulse
PULSE_LIB_GC = Pulse.Lib.GC/Pulse.Lib.GC.Heap.fst Pulse.Lib.GC/Pulse.Lib.GC.Object.fst \
               Pulse.Lib.GC/Pulse.Lib.GC.Stack.fst

.PHONY: all lax verify verify-pulse clean

all: lax

lax:
	@for f in $(ALL_MODULES); do echo "Checking $$f..."; $(FSTAR) $(FSTAR_FLAGS) --lax $$f || exit 1; done

verify:
	@for f in $(ALL_MODULES); do echo "Verifying $$f..."; $(FSTAR) $(FSTAR_FLAGS) $$f || exit 1; done

verify-pulse:
	@for f in $(PULSE_LIB_GC); do echo "Verifying $$f..."; $(FSTAR) $(FSTAR_FLAGS) $(PULSE_FLAGS) $$f || exit 1; done

clean:
	rm -f Spec/*.checked* Lib/*.checked* Pulse.Lib.GC/*.checked*
