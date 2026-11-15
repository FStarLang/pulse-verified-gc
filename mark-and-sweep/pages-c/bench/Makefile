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

# The parallel sweep against the parallel prototype (pbench.sh): the
# prototype's alloc_pages.c and proto.h from the P0 worktree branch
# sheera/pages-parallel-proto (PPROTO_DIR, uncommitted there), on its own
# worker pool (proto_par_stubs.c); the verified one over pages_par.c.
PPROTO_DIR ?= $(HOME)/Documents/pgc-pages-par-proto/$(PROTO_DIR)

_pproto/alloc_pages.c _pproto/proto.h:
	@mkdir -p _pproto
	cp $(PPROTO_DIR)/alloc_pages.c $(PPROTO_DIR)/proto.h _pproto/

bench_pproto: bench.c proto_par_stubs.c _pproto/alloc_pages.c _pproto/proto.h
	$(CC) $(OPT) -pthread -DPROTO -DPAR -DVERGC_B_VARIANT=2 -I_pproto -Istub bench.c proto_par_stubs.c _pproto/alloc_pages.c -o $@

bench_pverified: bench.c $(VSRC) ../pages_par.c ../GC_Pages.h ../pages_par.h
	$(CC) $(OPT) -pthread -DPAR $(VINC) -Wno-everything bench.c $(VSRC) ../pages_par.c -o $@

pbench: bench_pproto bench_pverified
	@./pbench.sh $(ROUNDS) $(REPS)

bench: all
	@./bench.sh $(ROUNDS) $(REPS)

clean:
	rm -rf _proto _pproto bench_proto bench_verified bench_pproto bench_pverified

.PHONY: all bench pbench clean
