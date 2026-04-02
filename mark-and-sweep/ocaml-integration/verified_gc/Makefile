# Build libvergc.a from the verified GC + allocator + bridge
CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
CFLAGS  += -I. -Iinternal -Ikrmllib -Ikrmllib/krml -Ikrmllib/krml/internal
# Allow access to OCaml runtime internals (for alloc.c)
CFLAGS  += -I..

OBJECTS = GC_Impl.o allocator.o alloc.o

all: libvergc.a

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

libvergc.a: $(OBJECTS)
	$(AR) rcs $@ $^

clean:
	rm -f *.o *.a

.PHONY: all clean
