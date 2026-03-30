# Build the extracted Pulse GC from snapshot
CC ?= cc
CFLAGS = -O2 -Wall -Wextra -std=c11 -I. -Ikrmllib -Ikrmllib/krml -Ikrmllib/krml/internal

OBJS = Pulse_Lib_GC.o pulsegc_runtime.o krmlinit.o

all: libpulsegc.a

libpulsegc.a: $(OBJS)
	ar rcs $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

Pulse_Lib_GC.o: Pulse_Lib_GC.c pulsegc_compat.h Pulse_Lib_GC.h \
  internal/Pulse_Lib_GC.h internal/Pulse_Spec_GC_Pulse_Lib_Header_Pulse_Lib_Address.h

clean:
	rm -f *.o libpulsegc.a
