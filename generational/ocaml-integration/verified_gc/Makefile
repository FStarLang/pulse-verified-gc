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

# The parallel sweep (docs/parallel-sweep-phase1.md, §9, Stage 3): its
# extracted C (parallel-sweep/snapshot), the thread pool, and the bridge.  Off
# at run time unless VERGC_PAR_SWEEP_THREADS is set.  Their own snapshot comes
# first on the include path; its krmlinit_globals is renamed so it does not
# clash with the generational one.  -fno-common: its two globals are otherwise
# common symbols, which the macOS linker does not pull out of an archive.
# PAR_SWEEP_CHECK=1 builds the test bridge,
# which compares every parallel sweep with the sequential one.
PSW := $(MAKEFILE_DIR)../../../parallel-sweep
PSW_CFLAGS = -I$(PSW)/snapshot $(CFLAGS) -fno-common -Dkrmlinit_globals=sweep_par_krmlinit_globals \
             $(if $(PAR_SWEEP_CHECK),-DVERGC_PAR_SWEEP_CHECK)
PSW_OBJECTS = psw_GC_SweepPar.o psw_GC_Spec_GC_Lib_Header_GC_Lib_Address.o \
              psw_krmlinit.o psw_par_sweep.o par_sweep_bridge.o

OBJECTS = GC_Gen_Impl.o GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.o \
          krmlinit.o compat.o alloc_gen.o $(PSW_OBJECTS)
NATIVE_OBJECTS = $(OBJECTS:.o=.n.o)

all: libvergc_gen.a libvergc_gen_native.a

psw_%.o: $(PSW)/snapshot/%.c
	$(CC) $(PSW_CFLAGS) -c $< -o $@

psw_%.n.o: $(PSW)/snapshot/%.c
	$(CC) $(PSW_CFLAGS) -DNATIVE_CODE -c $< -o $@

psw_%.o: $(PSW)/c/%.c
	$(CC) $(PSW_CFLAGS) -c $< -o $@

psw_%.n.o: $(PSW)/c/%.c
	$(CC) $(PSW_CFLAGS) -DNATIVE_CODE -c $< -o $@

par_sweep_bridge.o: par_sweep_bridge.c
	$(CC) $(PSW_CFLAGS) -c $< -o $@

par_sweep_bridge.n.o: par_sweep_bridge.c
	$(CC) $(PSW_CFLAGS) -DNATIVE_CODE -c $< -o $@

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

%.n.o: %.c
	$(CC) $(NATIVE_CFLAGS) -c $< -o $@

libvergc_gen.a: $(OBJECTS)
	$(AR) rcs $@ $^

libvergc_gen_native.a: $(NATIVE_OBJECTS)
	$(AR) rcs $@ $^

clean:
	rm -f *.o *.a

.PHONY: all clean
