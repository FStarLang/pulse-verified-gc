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

# The same with the tagged allocator (alloc_tag) in place of alloc_white.
bench_tagged: bench.c $(VSRC) ../GC_Pages.h
	$(CC) $(OPT) $(VINC) -Wno-everything -DTAGGED bench.c $(VSRC) -o $@

bench: all
	@./bench.sh $(ROUNDS) $(REPS)

# Incremental mode (plan section 28): allocations interleaved with sweep
# slices, against the prototype's incremental sweep, with an A/A control.
bench-inc: bench_proto bench_verified
	@./bench_inc.sh $(ROUNDS) $(REPS)

bench-tagged: bench_proto bench_tagged
	@VERIFIED=bench_tagged ./bench.sh $(ROUNDS) $(REPS)

# Promotion (plan section 30): the minor collection with the page allocator
# against main's, with the first-fit free list (generational/snapshot, the C
# of origin/main), both Idle, with an A/A control (bench_promo.c).
MSRC = $(SNAP)/GC_Gen_Impl.c $(SNAP)/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.c \
       $(SNAP)/krmlinit.c $(SNAP)/compat.c
MINC = -I$(SNAP) -I$(SNAP)/internal -I$(SNAP)/krmllib -I$(SNAP)/krmllib/krml -I$(SNAP)/krmllib/krml/internal \
       -include $(SNAP)/compat.h

bench_promo_main: bench_promo.c $(MSRC)
	$(CC) $(OPT) $(MINC) -Wno-everything -DMAIN bench_promo.c $(MSRC) -o $@

bench_promo_pages: bench_promo.c $(VSRC) ../GC_Pages.h
	$(CC) $(OPT) $(VINC) -Wno-everything bench_promo.c $(VSRC) -o $@

bench-promo: bench_promo_main bench_promo_pages
	@./bench_promo.sh $(ROUNDS) $(REPS)

clean:
	rm -rf _proto bench_proto bench_verified bench_tagged bench_promo_main bench_promo_pages

.PHONY: all bench bench-inc bench-tagged bench-promo clean
