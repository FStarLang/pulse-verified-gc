# Build libvergc_gen.a from the verified generational GC + bridge
#
# Extracted (verified) sources live in ../../snapshot/ and are used
# directly via VPATH — no manual copy needed.

CC      ?= gcc
SNAPSHOT = ../../snapshot

CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
CFLAGS  += -I$(SNAPSHOT) -I$(SNAPSHOT)/internal \
           -I$(SNAPSHOT)/krmllib -I$(SNAPSHOT)/krmllib/krml -I$(SNAPSHOT)/krmllib/krml/internal
# Allow access to OCaml runtime internals (for alloc_gen.c)
CFLAGS  += -I.. -I../ocaml-4.14-verified-gen/runtime -I../ocaml-4.14-verified-gen

# VPATH lets make find .c files in the snapshot directory
VPATH = $(SNAPSHOT)

OBJECTS = GC_Gen_Impl.o GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.o \
          krmlinit.o compat.o alloc_gen.o

all: libvergc_gen.a

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

libvergc_gen.a: $(OBJECTS)
	$(AR) rcs $@ $^

clean:
	rm -f *.o *.a

.PHONY: all clean
