# Root Makefile for pulse-verified-gc
#
# Orchestrates builds across all subdirectories.
# common/ is built first; mark-and-sweep/ depends on it.

SUBDIRS = common mark-and-sweep

.PHONY: all verify clean $(SUBDIRS)

all: verify

verify: common
	$(MAKE) -C mark-and-sweep

common:
	$(MAKE) -C common

mark-and-sweep: common
	$(MAKE) -C mark-and-sweep

clean:
	@for d in $(SUBDIRS); do $(MAKE) -C $$d clean; done
