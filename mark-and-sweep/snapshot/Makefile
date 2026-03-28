# Makefile for PulseGC snapshot (standalone, no F*/KaRaMeL required)
#
# This directory contains C code extracted from the verified Pulse GC
# implementation. It can be compiled without the F* toolchain.
#
# Usage:
#   make            Build libpulsegc.a
#   make clean      Remove build artifacts

CC     ?= gcc
AR     ?= ar
CFLAGS ?= -O2 -Wall -Wno-unused-variable -Wno-unused-but-set-variable
CFLAGS += -I. -Ikrmllib

SRCS = PulseGC.c PulseGC_stubs.c
OBJS = $(SRCS:.c=.o)
LIB  = libpulsegc.a

.PHONY: all clean

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $^

%.o: %.c PulseGC.h PulseGC_compat.h
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)
