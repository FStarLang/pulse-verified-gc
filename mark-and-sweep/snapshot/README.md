# PulseGC Extracted C Snapshot

This directory contains C code extracted from the verified Pulse GC
(mark-and-sweep) implementation via KaRaMeL. It builds standalone
without the F*/Pulse/KaRaMeL toolchain.

## Building

```bash
make            # Build libpulsegc.a
make clean      # Clean
```

## Files

| File | Description |
|------|-------------|
| `PulseGC.c` | KaRaMeL-extracted GC implementation |
| `PulseGC.h` | Public API header |
| `PulseGC_compat.h` | Type definitions for F* spec types (hp_addr → uint64_t, color_sem → enum) |
| `PulseGC_stubs.c` | Runtime stubs for functions KaRaMeL couldn't fully translate |
| `Makefile` | Standalone build |
| `internal/` | KaRaMeL internal headers |
| `krmllib/` | KaRaMeL runtime headers (subset of krmllib) |

## Extraction Status

The extracted code covers the per-object GC operations. Some top-level
loops are not yet extracted because the Pulse implementation uses
`Seq.seq` (a spec-level type) for the gray stack rather than a Low*-compatible
array type.

### Fully Extracted Functions

- **Heap**: `read_word`, `write_word`, `alloc_heap`, `read_byte`, `write_byte`
- **Object**: `getWosize`, `getTag`, `makeHeader`, `color_of_object`,
  `is_white_object`, `is_gray_object`, `is_black_object`, `colorHeader`, `isPointer`
- **Sweep**: `sweep_object`, `sweep_white_case`, `sweep_black_case`,
  `sweep_white_spec`, `sweep_black_spec`
- **Fields**: `field_address`, `read_succ`, `is_pointer`, `for_each_successor`,
  `is_valid_header`, `next_object_addr`
- **Closure**: `closinfo_val`, `start_env_from_closinfo`, `is_infix_object`,
  `is_closure_object`, `resolve_object`, `scan_closure_env`, `is_no_scan`

### Not Yet Extracted (require Seq.seq → Array/Vec refactoring)

- `mark_loop`, `mark_step` — depend on gray stack (uses `ref (Seq.seq obj_addr)`)
- `sweep_loop`, `sweep` — type mismatch between hp_addr and uint64_t
- `collect` — top-level entry point (depends on mark_loop + sweep)
- Stack operations (`create_stack`, `push`, `pop`, `is_empty`)

### Path to Full Extraction

To extract the complete GC:
1. Replace `gray_stack = ref (Seq.seq obj_addr)` with `Pulse.Lib.Vec.vec obj_addr`
2. Ensure all hp_addr/obj_addr casts are explicit `U64.t` operations
3. Add `inline_for_extraction` to small helper functions

## Regenerating

From the repository root:
```bash
cd mark-and-sweep
make snapshot    # Verify + extract + create snapshot/
```
