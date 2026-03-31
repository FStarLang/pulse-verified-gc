# Build the extracted Pulse GC from snapshot
CC ?= cc
CFLAGS = -O2 -Wall -Wextra -std=c11 -I. -Ikrmllib -Ikrmllib/krml -Ikrmllib/krml/internal

OBJS = GC_Impl.o pulsegc_runtime.o krmlinit.o

all: libpulsegc.a

libpulsegc.a: $(OBJS)
	ar rcs $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

GC_Impl.o: GC_Impl.c pulsegc_compat.h GC_Impl.h \
  internal/GC_Impl.h internal/GC_Spec_GC_Lib_Header_GC_Lib_Address.h

clean:
	rm -f *.o libpulsegc.a
