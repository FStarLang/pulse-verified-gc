---
name: krmlextraction
description: Extract verified F*/Pulse code to C using KaRaMeL, including bundling, naming, coding patterns, and build integration
---

## Invocation
This skill is used when:
- Extracting verified F* or Pulse code to C via KaRaMeL
- Configuring `-bundle` options for controlling C output structure
- Designing F*/Pulse module hierarchies for clean C extraction
- Debugging extraction issues (missing symbols, naming, includes)
- Building and testing extracted C code

## Overview

KaRaMeL (krml) translates a subset of F* (called Low*) and Pulse to C.
The pipeline is:

1. **F* verification** — `fstar.exe` checks `.fst`/`.fsti` files
2. **F* extraction to .krml** — `fstar.exe --codegen krml --extract ModuleName`
3. **KaRaMeL translation to C** — `krml` reads `.krml` files and produces `.c`/`.h`

## Two-Phase Extraction

### Phase 1: F* → .krml

Each module is extracted individually:

```bash
# Regular F* modules
fstar.exe --codegen krml --extract 'MyModule' --odir _output MyModule.fst

# #lang-pulse modules produce out.krml instead of ModuleName.krml
fstar.exe --codegen krml --extract 'My.Pulse.Module' --odir _output pulse/My.Pulse.Module.fst
# IMPORTANT: rename out.krml to expected name
mv -f _output/out.krml _output/My_Pulse_Module.krml
```

**Multi-module quirk**: When `--extract 'M'` causes **multiple modules** to be
extracted in a single invocation (e.g., `M` depends on `M.Sub`, so both are
extracted), the output is named `out.krml` instead of `M.krml`. This is not
Pulse-specific — it happens with plain F* modules too.

**Best fix**: Use `--extract_module M` instead of `--extract 'M'`. This
extracts exactly the named module and always produces `M.krml`:
```bash
fstar.exe --codegen krml --extract_module My.Module pulse/My.Module.fst
# Produces: _output/My_Module.krml  (never out.krml)
```
Use one invocation per module. This also enables `make -j` parallelism
via per-file make targets (see Build Integration below).

### Phase 2: .krml → C

```bash
krml \
  -tmpdir _extract \
  -skip-compilation \
  -warn-error -2-9-11-15-17 \
  -bundle '...' \
  -no-prefix ModuleName \
  _output/*.krml \
  $KRML_HOME/krmllib/.extract/*.krml
```

Key flags:
- `-tmpdir DIR` — output directory for `.c`/`.h` files
- `-skip-compilation` — don't compile; just generate C
- `-warn-error -N` — silence warning N (see `krml -help` for list)
- `-no-prefix M` — strip module prefix from declarations in module M
- `-minimal` — omit `#include "krmllib.h"` (but also omits `<stdint.h>` — usually not what you want)

Always pass `$KRML_HOME/krmllib/.extract/*.krml` so KaRaMeL knows the
signatures of standard library types (FStar.UInt64, etc.).

## Bundle Syntax

The `-bundle` flag controls how F* modules map to C translation units.

### Basic Syntax

```
-bundle 'Api=Pattern1,Pattern2,...,PatternN'
```

- **Api** (left of `=`): modules whose declarations remain **public** (appear in `.h`)
- **Patterns** (right of `=`): modules whose declarations are **bundled** into the same `.c` but marked `static`
- Patterns can be exact (`Foo.Bar`) or prefix (`Foo.Baz.*`)
- The Api module(s) must appear among the input `.krml` files

### Merging Multiple Modules with `+`

To keep declarations from **multiple** modules public, separate them with `+`:

```
-bundle 'A.Impl+A.Impl.Search=A.Impl,A.Impl.Types,A.Impl.Helpers,A.Impl.Search'
```

Without `+`, only the single left-hand-side module's declarations stay public.
Functions from other modules on the right-hand side become `static` — which
means they're silently dropped from the header and may be dead-code-eliminated.

### Renaming Output Files with `[rename=Name]`

Append `[rename=OutputName]` inside the pattern list to control the `.c`/`.h` filename:

```
-bundle 'A.Impl+A.Impl.Search=A.Impl,...,A.Impl.Search[rename=My_Output]'
```

This produces `My_Output.c`, `My_Output.h`, and `internal/My_Output.h`.

The `[rename=...]` attribute is placed **inside** the `=` right-hand side,
typically at the end of the pattern list. It is parsed by KaRaMeL's
`KParser.mly` grammar as a bracket-delimited attribute on the bundle pattern.

### Dropping Unused Modules

Use a second `-bundle` to drop spec-only and library modules that should not
produce C code:

```
-bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,My.Spec.Types,My.Spec.Logic'
```

A `-bundle` with no `Api=` prefix (no left-hand side) means: bundle these
modules together and mark everything static. Since nothing references them
from outside, they're dead-code-eliminated entirely.

### Complete Example

```bash
krml \
  -tmpdir _extract \
  -skip-compilation \
  -warn-error -2-9-11-15-17 \
  -bundle 'Impl+Impl.Search=Impl,Impl.Types,Impl.Arith,LowTypes,BitOps,Impl.Search,Impl.Search.Lemmas[rename=Verified_Output]' \
  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,Spec.Types,Spec.Logic' \
  -no-prefix Impl \
  -no-prefix Impl.Search \
  _output/*.krml \
  $KRML_HOME/krmllib/.extract/*.krml
```

## F*/Pulse Coding Patterns for Clean Extraction

### Module Architecture

Organize code into layers that separate extractable code from proof-only code:

| Layer | Purpose | Extracted? |
|-------|---------|------------|
| **Spec types** (`spec/`) | Abstract mathematical types, pure functions | No (OCaml only) |
| **Low-level types** | `U64.t` aliases, bitfield getters/setters | Yes → C functions |
| **Correspondence predicates** | Link spec ↔ low-level types | No (erased) |
| **Helper lemmas** | Arithmetic, bitfield, domain reasoning | No (`Lemma` return type) |
| **Pulse implementation** | `#lang-pulse` `fn` definitions with pre/post | Yes → C functions |

### Extractable Types

KaRaMeL extracts the following F* types to C:

| F* Type | C Type |
|---------|--------|
| `FStar.UInt64.t` (`U64.t`) | `uint64_t` |
| `FStar.UInt32.t` (`U32.t`) | `uint32_t` |
| `FStar.Int64.t` (`I64.t`) | `int64_t` |
| `FStar.SizeT.t` (`SZ.t`) | `size_t` |
| `bool` | `bool` |
| `a & b` (F* tuple) | C struct with `.fst`, `.snd` fields |
| `Pulse.Lib.Array.array t` | `t *` (C pointer) |
| `noeq type` with named fields | C `typedef struct` |

### Types to Avoid in Extracted Code

- **`list`** — unbounded, heap-allocated; not Low*. Use arrays with size.
- **`option`** in return types — use a struct with a `bool` flag instead, or
  encode `None` as a sentinel value.
- **`string`** — not directly extractable; use `C.String.t` if needed.
- **Recursive algebraic types** — only simple (non-recursive) `noeq type`
  with named fields extract cleanly.
- **Higher-order functions** — KaRaMeL cannot extract closures. Use
  monomorphized, first-order code.

### Ghost and Erased Types

Ghost/erased parameters are the key mechanism for carrying proof state
without runtime cost:

```fstar
fn my_function
  (arr: A.array U64.t)       (* concrete: extracted to C parameter *)
  (len: U32.t)               (* concrete: extracted *)
  (#ghost_seq: Ghost.erased (Seq.seq U64.t))  (* erased: NOT in C *)
  requires
    A.pts_to arr ghost_seq ** (* proof-only assertion *)
    pure (Seq.length ghost_seq == U32.v len)
  returns result: U64.t
  ensures
    A.pts_to arr ghost_seq ** (* frame preserved *)
    pure (U64.v result == spec_function (Ghost.reveal ghost_seq))
```

Extracted C signature:
```c
uint64_t my_function(uint64_t *arr, uint32_t len);
```

**Rules**:
- `#`-prefixed parameters (implicit) with `Ghost.erased` type are erased
- `requires`/`ensures` clauses are entirely erased
- `pure (...)` predicates inside pre/post are erased
- Refinement types on scalars (e.g., `U32.t{U32.v x < 1024}`) are erased —
  the refinement becomes a proof obligation, not a runtime check

### Correspondence Predicates

Define `prop`-valued functions that relate low-level words to spec types:

```fstar
let key_corresponds (kw: U64.t) (k: SpecTypes.key) : prop =
  U64.v (get_field kw 0ul 48ul) == k.target /\
  U64.v (get_field kw 48ul 10ul) == k.index /\
  get_bit kw 62ul == k.tail
```

These are used only in `requires`/`ensures` and are fully erased.

### inline_for_extraction

Use `inline_for_extraction` for:
- **Constants** — shift amounts, masks, magic numbers:
  ```fstar
  inline_for_extraction let key_target_shift : U32.t = 0ul
  inline_for_extraction let key_target_width : U32.t = 48ul
  inline_for_extraction let key_target_mask : U64.t = 0xFFFFFFFFFFFFUL
  ```
- **Small wrapper functions** that should be inlined at call sites

Do NOT use `inline_for_extraction` on large functions — they bloat the
generated C.

### Lemma Functions

Lemmas have return type `Lemma` and are **never extracted**:

```fstar
val my_arithmetic_fact (x: U64.t)
  : Lemma (requires U64.v x < pow2 50)
          (ensures U64.v (U64.(x >>^ 2ul <<^ 2ul)) == (U64.v x / 4) * 4)
```

Call lemmas in Pulse code for their proof side-effect:

```fstar
fn compute_aligned (x: U64.t)
  requires pure (U64.v x < pow2 50)
  returns r: U64.t
  ensures pure (U64.v r == (U64.v x / 4) * 4)
{
  my_arithmetic_fact x;   // ← lemma call; erased from C
  U64.(x >>^ 2ul <<^ 2ul)
}
```

### Intermediate Result Types

For functions that return multiple values, define a `noeq type`:

```fstar
noeq type step_result = {
  done: bool;
  next_index: U64.t;
  dest: U64.t;
  src: U64.t;
}
```

This extracts to a C struct:
```c
typedef struct step_result_s {
  bool done;
  uint64_t next_index;
  uint64_t dest;
  uint64_t src;
} step_result;
```

Avoid F* tuples for more than 2 elements — named structs produce more
readable C.

### Pulse fn Patterns

A typical extractable Pulse function:

```fstar
fn do_lookup
  (table: A.array node_word)
  (index: U32.t{U32.v index < 1024})
  (quantum: I64.t)
  (#s: Ghost.erased (Seq.seq node_word))
  requires
    A.pts_to table s **
    pure (Seq.length s == 1024 /\ valid_table s)
  returns result: action_word
  ensures
    A.pts_to table s **
    pure (action_corresponds result (spec_lookup (table_of s) index (I64.v quantum)))
{
  // Read from array — generates C array access
  let node = A.op_Array_Access table (SZ.uint32_to_sizet index);
  let chamber = fst node;
  let route = snd node;

  // Call pure helper lemma
  some_arithmetic_lemma chamber;

  // Bitfield extraction — generates C bit operations
  let base = get_field chamber 0ul 48ul;

  // Conditional — generates C if/else
  if get_bit chamber 62ul then
    ...
  else
    ...
}
```

### Array Access in Pulse

Pulse uses `Pulse.Lib.Array` for heap-allocated arrays:

```fstar
// Read: requires pts_to permission
let elem = A.op_Array_Access arr (SZ.uint32_to_sizet idx);

// Write: requires pts_to permission (full)
A.op_Array_Assignment arr (SZ.uint32_to_sizet idx) new_val;
```

Array indices must be `FStar.SizeT.t`. Convert with:
```fstar
SZ.uint32_to_sizet idx    // U32 → SizeT
SZ.uint64_to_sizet idx    // U64 → SizeT (requires bounds proof)
```

### Loops in Pulse

Use `while` with mutable references:

```fstar
let mut done = false;
let mut idx = initial_index;
while (let d = !done; not d)
  invariant b.
    exists* (i: U64.t) (d: bool).
      pts_to idx i ** pts_to done d **
      A.pts_to table s **
      pure (b == not d /\ loop_invariant i d ...)
{
  let i = !idx;
  let node = A.op_Array_Access table (SZ.uint64_to_sizet i);
  // ... loop body ...
  done := true;  // or update idx
}
```

Extracted C:
```c
bool done = false;
uint64_t idx = initial_index;
while (!done) {
  node_word node = table[idx];
  // ... loop body ...
  done = true;
}
```

## Build Integration

### krmllib Include Path

Extracted C files include `"krmllib.h"` which chains to type definitions.
The compiler needs:

```makefile
CFLAGS += -I$(KRML_HOME)/include -I$(KRML_HOME)/krmllib/dist/minimal
```

**Gotcha**: `KRML_HOME` is relative to the directory where `make` runs.
If using `$(MAKE) -C subdir`, recompute the path:
```makefile
# From parent Makefile invoking sub-make
$(MAKE) -C test KRML_HOME=$(abspath $(KRML_HOME))
```

### Stubs

KaRaMeL's generated code may reference runtime helpers. Provide stubs:

```c
// stubs.c
#include <stdio.h>
#include <stdlib.h>
void KRML_HOST_EPRINTF(const char *fmt, ...) { /* optional */ }
void KRML_HOST_EXIT(int code) { exit(code); }
```

Or define them as macros via CFLAGS:
```makefile
CFLAGS += -DKRML_HOST_EPRINTF=eprintf_helper -DKRML_HOST_EXIT=exit
```

### Snapshot Directory

For checked-in extracted C (CI without F*/KaRaMeL toolchain):

```
snapshot/
  Verified_Output.c          # Extracted C
  Verified_Output.h          # Public header
  internal/Verified_Output.h # KaRaMeL internal header
  krmllib/                   # Copied from $KRML_HOME (krmllib.h, dist/minimal, krml/)
  stubs.c                    # Runtime stubs
  test.c                     # Test driver
  Makefile                   # Standalone build
```

Copy `krmllib.h` and `krmllib/dist/minimal/` so the snapshot builds
without a KaRaMeL installation.

### Symbol Collision When Linking Against Original Code

When comparing extracted code against an original C implementation with
identical function names, use `-D` rename flags:

```makefile
RENAME_FLAGS = \
  -Dmy_function=v_my_function \
  -Dother_function=v_other_function

# Compile ONLY the extracted .c with renames
compare: extracted.c original.c test.c
	$(CC) $(CFLAGS) $(RENAME_FLAGS) -c extracted.c -o extracted_cmp.o
	$(CC) $(CFLAGS) -c original.c -o original.o
	$(CC) $(CFLAGS) -DCOMPARE_MODE -c test.c -o test_cmp.o
	$(CC) -o $@ test_cmp.o extracted_cmp.o original.o
```

In the test file, use dispatch macros:
```c
#ifdef COMPARE_MODE
// Declare renamed verified functions
extern result_type v_my_function(uint64_t *table, uint64_t key, int64_t quantum);
#define V_my_function v_my_function
#else
#include "Verified_Output.h"
#define V_my_function my_function
#endif
```

## Debugging Extraction

### Common Warnings

| Warning | Meaning | Fix |
|---------|---------|-----|
| 2 | Reference to function without implementation | Ensure module is in bundle or provide stub |
| 9 | Need manual static initializer call | Avoid mutable globals, or call initializer |
| 11 | Subexpression is not Low* | Refactor to avoid higher-order or unbounded types |
| 15 | Function is not Low*; needs compat headers | Ensure all types are extractable |

### Useful Debug Flags

```bash
krml -d bundle ...     # Debug bundle resolution
krml -d reachability ...  # Debug dead-code elimination
krml -d c-names ...    # Debug C name generation
krml -dast ...         # Dump internal AST
krml -verbose ...      # Show all intermediate steps
```

### Missing Functions in Output

If a function disappears from the extracted `.c`:
1. Check it's in the `+` part of `-bundle` (public API)
2. Check it's not in a dropped bundle (`FStar.*,...`)
3. Use `-d reachability` to see if it's being eliminated
4. Verify the `.fsti` exposes the function signature

### Wrong Prefix on Names

If extracted names have module prefixes like `Impl_my_function`:
- Add `-no-prefix Impl` for each module whose names you want unprefixed
- Only affects the specified module — other modules keep their prefix

## Additional Resources

- `krml -help` — full option listing
- KaRaMeL repository: https://github.com/FStarLang/karamel
- KaRaMeL bundle grammar: `karamel/_build/default/lib/parser/KParser.mly`
- Low* tutorial: https://fstarlang.github.io/lowstar/html/
- krmllib headers: `$KRML_HOME/include/` and `$KRML_HOME/krmllib/dist/minimal/`
