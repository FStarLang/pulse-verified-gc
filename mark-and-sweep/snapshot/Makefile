# Standalone build for the verified mark-and-sweep GC snapshot.
#
# This compiles the KaRaMeL-extracted C code without needing F* or KaRaMeL
# installed.  The krmllib/ headers are vendored in this directory.
#
# Usage:
#   make            Build and run the test harness
#   make test       Same as above
#   make clean      Remove build artifacts

CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter

# krmllib headers are vendored under krmllib/
CFLAGS += -I. -Iinternal -Ikrmllib -Ikrmllib/krml -Ikrmllib/krml/internal

SOURCES = GC_Impl.c main.c
TARGET  = gc_test

.PHONY: all test clean

all: test

test: $(TARGET)
	./$(TARGET)

$(TARGET): $(SOURCES) GC_Impl.h internal/GC_Impl.h
	$(CC) $(CFLAGS) $(SOURCES) -o $@

clean:
	rm -f $(TARGET)
