# Microbenchmark of the extracted page allocator and sweep against the
# prototype B2 (see bench.c).  `make bench` builds both and runs every
# workload in its own process, the two alternately (bench.sh), printing the
# medians; `make` builds only.
#
# The prototype's sources are read from the branch sheera/alloc-pages-proto
# (git show), so nothing of it is copied into this tree.  Both builds use the
# same compiler and flags, with link-time optimisation so that the extracted
# code's word reads (compat.c's read_u64_le) inline as the prototype's do.

PROTO_BRANCH ?= sheera/alloc-pages-proto
PROTO_DIR     = generational/ocaml-integration/verified_gc/proto
SNAP          = ../../../generational/snapshot
CC           ?= cc
OPT          ?= -O2 -flto
ROUNDS       ?= 5
REPS         ?= 7

all: bench_proto bench_verified

_proto/alloc_pages.c _proto/proto.h:
	@mkdir -p _proto
	git show $(PROTO_BRANCH):$(PROTO_DIR)/alloc_pages.c > _proto/alloc_pages.c
	git show $(PROTO_BRANCH):$(PROTO_DIR)/proto.h > _proto/proto.h

bench_proto: bench.c proto_stubs.c _proto/alloc_pages.c _proto/proto.h
	$(CC) $(OPT) -DPROTO -DVERGC_B_VARIANT=2 -I_proto -Istub bench.c proto_stubs.c _proto/alloc_pages.c -o $@

VSRC = ../GC_Pages.c ../GC_Pages_Spec.c ../krmlinit.c $(SNAP)/compat.c
VINC = -I.. -I../internal -I$(SNAP) -I$(SNAP)/krmllib -I$(SNAP)/krmllib/krml -I$(SNAP)/krmllib/krml/internal \
       -include $(SNAP)/compat.h

bench_verified: bench.c $(VSRC) ../GC_Pages.h
	$(CC) $(OPT) $(VINC) -Wno-everything bench.c $(VSRC) -o $@

bench: all
	@./bench.sh $(ROUNDS) $(REPS)

clean:
	rm -rf _proto bench_proto bench_verified

.PHONY: all bench clean
