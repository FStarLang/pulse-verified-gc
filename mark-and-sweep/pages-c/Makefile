# The page allocator (GC.Impl.Pages.*), extracted to C, and its test.
#
#   make extract   Extract GC.Impl.Pages.{Init,Alloc,Sweep} from
#                  their checked files (verify first: `make verify` at the
#                  root) into GC_Pages.{c,h} here.
#   make test      Build and run pages_test.c against the extracted C.  Needs
#                  neither F* nor KaRaMeL: it uses the extracted files here,
#                  and compat.c and krmllib/ from ../../generational/snapshot.
#   make clean     Remove build artifacts.

FSTAR_HOME ?= $(CURDIR)/../../fstar
FSTAR_EXE  ?= $(FSTAR_HOME)/bin/fstar.exe
KRML_HOME  ?= $(FSTAR_HOME)/karamel
KRML       ?= $(KRML_HOME)/krml

ROOT       = ../..
CACHE_DIR ?= $(ROOT)/_cache
OUTPUT_DIR = _output
EXTRACT_DIR = _extract
SNAP       = $(ROOT)/generational/snapshot

# Read checked files only: everything must already be verified.
FSTAR = $(FSTAR_EXE) \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --already_cached 'Prims FStar Pulse PulseCore GC' \
  --warn_error -321 \
  --include $(ROOT)/common/spec --include $(ROOT)/common/lib --include $(ROOT)/common/impl \
  --include $(ROOT)/mark-and-sweep/spec --include $(ROOT)/mark-and-sweep/impl \
  --include $(ROOT)/generational/spec

ENTRY_MODS = GC.Impl.Pages.Init GC.Impl.Pages.Alloc GC.Impl.Pages.Sweep

KRML_MODS = \
  GC.Impl.Pages.Init GC.Impl.Pages.Alloc GC.Impl.Pages.Sweep GC.Impl.Pages.SweepRun GC.Impl.Pages.SweepPage \
  GC.Impl.Pages.Large GC.Impl.Pages.Pool GC.Impl.Pages.Heap GC.Impl.Pages.State \
  GC.Impl.Pages.Params GC.Impl.Heap GC.Impl.Object GC.Impl.ArrayWord \
  GC.Spec.ZeroAddr GC.Spec.Base GC.Spec.Heap GC.Spec.Object GC.Lib.Header GC.Lib.Address

KRML_FLAGS = \
  -tmpdir $(EXTRACT_DIR) \
  -skip-compilation -skip-linking \
  -bundle 'GC.Impl.Pages.Init+GC.Impl.Pages.Alloc+GC.Impl.Pages.Sweep=GC.Impl.Pages.*,GC.Impl.Heap,GC.Impl.Object,GC.Impl.ArrayWord,Pulse.Lib.Array[rename=GC_Pages]' \
  -bundle 'GC.Spec.ZeroAddr=GC.Spec.ZeroAddr' \
  -bundle 'GC.Spec.*,GC.Lib.Header,GC.Lib.Address,GC.Gen.*[rename=GC_Pages_Spec]' \
  $(foreach m,$(KRML_MODS),-no-prefix $(m)) \
  -warn-error -2-9-15

.PHONY: all extract test clean

all: test

$(OUTPUT_DIR) $(EXTRACT_DIR):
	@mkdir -p $@

$(OUTPUT_DIR)/Custard.krml: | $(OUTPUT_DIR)
	$(FSTAR) --odir $(OUTPUT_DIR) --codegen KrmlC --custard_split \
	  $(addprefix --custard_entry_module ,$(ENTRY_MODS)) \
	  $(ROOT)/mark-and-sweep/impl/GC.Impl.Pages.fst

extract: $(OUTPUT_DIR)/Custard.krml | $(EXTRACT_DIR)
	$(KRML) $(KRML_FLAGS) $(OUTPUT_DIR)/Custard.krml
	cp $(EXTRACT_DIR)/GC_Pages.c $(EXTRACT_DIR)/GC_Pages.h .
	cp $(EXTRACT_DIR)/GC_Pages_Spec.c $(EXTRACT_DIR)/GC_Pages_Spec.h .
	cp $(EXTRACT_DIR)/GC_Spec_ZeroAddr.h .
	cp $(EXTRACT_DIR)/krmlinit.c $(EXTRACT_DIR)/krmlinit.h .
	rm -rf internal && mkdir -p internal && cp $(EXTRACT_DIR)/internal/*.h internal/
	@echo "=== GC_Pages.{c,h} extracted ==="

CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function
CFLAGS += -I. -Iinternal -I$(SNAP) -I$(SNAP)/krmllib -I$(SNAP)/krmllib/krml -I$(SNAP)/krmllib/krml/internal
CFLAGS += -include $(SNAP)/compat.h

SOURCES = GC_Pages.c GC_Pages_Spec.c krmlinit.c $(SNAP)/compat.c pages_test.c

pages_test: $(SOURCES) GC_Pages.h
	$(CC) $(CFLAGS) $(SOURCES) -o $@

test: pages_test
	./pages_test

clean:
	rm -rf $(OUTPUT_DIR) $(EXTRACT_DIR) pages_test
