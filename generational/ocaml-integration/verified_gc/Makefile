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
# Allow access to OCaml runtime internals (for alloc_gen.c)
CFLAGS  += -I.. -I../ocaml-4.14-verified-gen/runtime -I../ocaml-4.14-verified-gen
# None of the runtime headers alloc_gen.c includes depend on TARGET_*, so
# NATIVE_CODE is the only flag the native build needs.
NATIVE_CFLAGS  = $(CFLAGS) -DNATIVE_CODE

# VPATH lets make find .c files in the snapshot directory
VPATH = $(SNAPSHOT)

# The page allocator (VERGC_ALLOC=pages, stop-the-world only; see
# alloc_gen.c): the extracted GC.Impl.Pages.* of mark-and-sweep/pages-c, at
# 32 KB pages (pages-c) and 16 KB pages (pages-c/16k), each compiled into
# its own object by pages/pages_unit.c.  GC_Gen_Impl_hooked.c is the
# extracted GC_Gen_Impl.c with `allocate` dispatching to it
# (pages/hook_allocate.py); the snapshot itself is unchanged.
PAGES32 := $(MAKEFILE_DIR)../../../mark-and-sweep/pages-c
PAGES16 := $(PAGES32)/16k

OBJECTS = GC_Gen_Impl_hooked.o GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.o \
          krmlinit.o compat.o alloc_gen.o pages32.o pages16.o
NATIVE_OBJECTS = $(OBJECTS:.o=.n.o)

GC_Gen_Impl_hooked.c: $(SNAPSHOT)/GC_Gen_Impl.c $(MAKEFILE_DIR)pages/hook_allocate.py
	python3 $(MAKEFILE_DIR)pages/hook_allocate.py $< $@

PAGES_SRC = $(MAKEFILE_DIR)pages/pages_unit.c
pages32.o: $(PAGES_SRC) $(PAGES32)/GC_Pages.c
	$(CC) -I$(PAGES32) $(CFLAGS) -DPAGES_KB=32 -c $< -o $@
pages16.o: $(PAGES_SRC) $(PAGES16)/GC_Pages.c
	$(CC) -I$(PAGES16) $(CFLAGS) -DPAGES_KB=16 -c $< -o $@
pages32.n.o: $(PAGES_SRC) $(PAGES32)/GC_Pages.c
	$(CC) -I$(PAGES32) $(NATIVE_CFLAGS) -DPAGES_KB=32 -c $< -o $@
pages16.n.o: $(PAGES_SRC) $(PAGES16)/GC_Pages.c
	$(CC) -I$(PAGES16) $(NATIVE_CFLAGS) -DPAGES_KB=16 -c $< -o $@

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
	rm -f *.o *.a GC_Gen_Impl_hooked.c

.PHONY: all clean
