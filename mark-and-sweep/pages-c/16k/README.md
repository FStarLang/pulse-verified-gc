# The page allocator at 16 KB pages

The C files here are the extraction of `GC.Impl.Pages.{Init,Alloc,Sweep}`
with 16 KB pages (2048 words), for the runtime's `VERGC_PAGE_KB=16`
(`generational/ocaml-integration/verified_gc/pages/`). The files in the
directory above are the same extraction at 32 KB pages, the page size the
source tree is set to.

They were made from the source tree as committed, in a scratch worktree:

1. `make verify` from an empty cache, at 32 KB. `make extract` in `pages-c`
   gives C identical to the committed files.
2. `python3 mark-and-sweep/pages-c/16k/make_params_16k.py <worktree>`.
   This rewrites the two parameter modules:
   - `GC.Spec.Pages.Params`: `page_wsize = page_wsize_16k`;
   - `GC.Impl.Pages.Params`: the page size literal, and the slot counts
     `n_slots c = 2048 / cls c` in `ns_values` and `n_slots_u64`.

   Every other module sees the parameters only through the two
   interfaces. `GC.Spec.Pages.Params.both_candidates_ok` checks the
   conditions at both sizes.
3. `make verify` again. It re-checks exactly the two parameter modules.
4. `rm -rf _output _extract; make extract` in `pages-c`, then copy the C
   files here.

The C differs from the 32 KB extraction only in the page size constants
(16384 bytes, 2048 words) and the slot-count table.

`pages_test.c` checks values worked out by hand for 32 KB pages, so it is
not run on these files.
