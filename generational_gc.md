Extend the current mark and sweep garbage collector with a generation, copying collector, a la OCaml. The details of the OCaml GC can be found in https://dev.realworldocaml.org/garbage-collector.html. In particular, all the small allocations go into the fixed-sized minor heap first. Large allocations directly go into the major heap. Once the minor heap is full, do a minor collection that does a copying collection to the major heap. You will use the major heap allocation function for this. The combined GC should still preserve the abstract GC correctness. As a reference, you may want to look at what the sequential OCaml 4 runtime system does: https://github.com/ocaml/ocaml/tree/4.14.

I want a full implementation of a generational collector as described above in
GC.Impl.fst/fsti, but with the same end-to-end correctness theorem, i.e.,
full_gc_correctness. We have to update both the allocator and the collector,
parameterizing them by the size of large objects and the size of the minor and
major heaps. We will reuse our existing coalescing ark-and-sweep collector for
the major heap.