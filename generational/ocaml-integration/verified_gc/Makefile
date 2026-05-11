# Build libvergc_gen.a from the verified generational GC + bridge
CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
CFLAGS  += -I. -Iinternal -Ikrmllib -Ikrmllib/krml -Ikrmllib/krml/internal
# Allow access to OCaml runtime internals (for alloc_gen.c)
CFLAGS  += -I..

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
