# Build libvergc_gen.a from the verified generational GC + bridge
#
# Extracted (verified) sources live in ../../snapshot/ (relative to
# this Makefile's real location) and are used directly via VPATH.

CC      ?= gcc

# Resolve the real directory of this Makefile (works through symlinks)
MAKEFILE_DIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
SNAPSHOT := $(MAKEFILE_DIR)../../snapshot

CFLAGS  ?= -O2 -flto -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
CFLAGS  += -include $(SNAPSHOT)/compat.h
CFLAGS  += -I$(SNAPSHOT) -I$(SNAPSHOT)/internal \
           -I$(SNAPSHOT)/krmllib -I$(SNAPSHOT)/krmllib/krml -I$(SNAPSHOT)/krmllib/krml/internal
# Extra flags for test builds, e.g. VGC_EXTRA_CFLAGS=-DVGC_CHECK_ALLOC
CFLAGS  += $(VGC_EXTRA_CFLAGS)
# Allow access to OCaml runtime internals (for alloc_gen.c)
CFLAGS  += -I.. -I../ocaml-4.14-verified-gen/runtime -I../ocaml-4.14-verified-gen
# None of the runtime headers alloc_gen.c includes depend on TARGET_*, so
# NATIVE_CODE is the only flag the native build needs.
NATIVE_CFLAGS  = $(CFLAGS) -DNATIVE_CODE

# VPATH lets make find .c files in the snapshot directory
VPATH = $(SNAPSHOT)

OBJECTS = GC_Gen_Impl.o GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.o \
          krmlinit.o compat.o alloc_gen.o

# Allocator-comparison prototypes (proto/, docs/allocator-comparison-results.md),
# unverified and for measurement only:
#   make PROTO=A   A, with the parallel and incremental sweep baselines
#   make PROTO=B   B, pages by size class
# Both link a copy of the extracted GC_Gen_Impl.c with hooks, written by
# proto/hook_snapshot.py; the snapshot itself is not changed.  `make clean`
# between variants: the objects do not record the flags they were built with.
PROTO ?=
ifneq ($(PROTO),)
VPATH   := $(SNAPSHOT):proto
CFLAGS  += -DVERGC_PROTO -DVERGC_PROTO_$(PROTO) -Iproto
PROTO_IMPL_A = sweep_lists.o
PROTO_IMPL_B = alloc_pages.o
OBJECTS = GC_Gen_Impl_proto.o GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.o \
          krmlinit.o compat.o alloc_gen.o proto_common.o proto_check.o $(PROTO_IMPL_$(PROTO))
GC_Gen_Impl_proto.c: $(SNAPSHOT)/GC_Gen_Impl.c proto/hook_snapshot.py
	python3 proto/hook_snapshot.py $< $@
endif
NATIVE_OBJECTS = $(OBJECTS:.o=.n.o)

all: libvergc_gen.a libvergc_gen_native.a

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.n.o: %.c
	$(CC) $(NATIVE_CFLAGS) -c $< -o $@

libvergc_gen.a: $(OBJECTS)
	$(AR) rcs $@ $^

libvergc_gen_native.a: $(NATIVE_OBJECTS)
	$(AR) rcs $@ $^

clean:
	rm -f *.o *.a GC_Gen_Impl_proto.c

.PHONY: all clean
