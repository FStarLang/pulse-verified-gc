# Standalone build for the verified generational GC snapshot.
#
# This compiles the KaRaMeL-extracted C code without needing F* or KaRaMeL
# installed. The krmllib/ headers are vendored in this directory.
#
# Usage:
#   make            Build and run the test harness
#   make test       Same as above
#   make clean      Remove build artifacts

CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable

# krmllib headers are vendored under krmllib/
CFLAGS += -I. -Iinternal -Ikrmllib -Ikrmllib/krml -Ikrmllib/krml/internal
CFLAGS += -include compat.h

SOURCES = GC_Gen_Impl.c GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c krmlinit.c compat.c main.c
TARGET  = gc_gen_test

.PHONY: all test clean

all: test

test: $(TARGET)
	./$(TARGET)

$(TARGET): $(SOURCES) GC_Gen_Impl.h internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h
	$(CC) $(CFLAGS) $(SOURCES) -o $@

clean:
	rm -f $(TARGET)
