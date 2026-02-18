# Root Makefile for pulse-verified-gc
#
# Orchestrates builds across all subdirectories.
# common/ is built first; downstream directories depend on it.

SUBDIRS = common mark-and-sweep concurrent fly

.PHONY: all verify clean $(SUBDIRS)

all: verify

verify: common
	$(MAKE) -C mark-and-sweep
	$(MAKE) -C concurrent
	$(MAKE) -C fly

common:
	$(MAKE) -C common

mark-and-sweep: common
	$(MAKE) -C mark-and-sweep

concurrent: common
	$(MAKE) -C concurrent

fly: common
	$(MAKE) -C fly

clean:
	@for d in $(SUBDIRS); do $(MAKE) -C $$d clean; done
