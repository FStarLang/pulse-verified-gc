# Snapshot Makefile for extracted Pulse GC
#
# Build: make
# Clean: make clean
#
# This builds the verified GC as a static library (libpulsegc.a).
# Requires: a C99 compiler (gcc/clang)

CC       ?= gcc
CFLAGS   ?= -std=c99 -Wall -Wextra -O2
CPPFLAGS  = -I. -Ikrmllib -Ikrmllib/krml -Ikrmllib/krml/internal

SRCS = Pulse_Lib_GC.c krmlinit.c pulsegc_runtime.c
OBJS = $(SRCS:.c=.o)

all: libpulsegc.a

libpulsegc.a: $(OBJS)
	$(AR) rcs $@ $^

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -c -o $@ $<

clean:
	rm -f $(OBJS) libpulsegc.a

.PHONY: all clean
