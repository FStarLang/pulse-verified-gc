# headers-colors-plan.md

## Goal

You have:

- A packed `u64` header containing 3 bitfields and an enum field `color`.
- Existing proofs about packed words, typically of the form `R : u64 -> Prop`.

You want:

- An unpacked view type `t` (explicit record + enum).
- A reusable equivalence/transport lemma so that proofs about `R w` can be restated as proofs about a corresponding predicate on the unpacked struct.

**Important constraint:** For an arbitrary `R`, you cannot prove `R w <-> exists x. lift R x` unless you tie `x` to `w` via `pack/unpack` (and typically require `valid w`). The correspondence must mention `pack`/`unpack` (or `unpack_opt`) and `valid`.

---

## Strategy Overview

### Define an unpacked view + codecs
1. Define an unpacked record `t` with explicit fields.
2. Define `pack : t -> u64`.
3. Define either:
   - Pattern A: `valid : u64 -> Prop` and `unpack : u64 -> Tot t` (total unpack; meaningful under `valid`), or
   - Pattern B: `unpack_opt : u64 -> option t` (partial unpack; `None` for invalid encodings).

### Transport predicates uniformly
Define `lift` (the only uniform “cast” that works for arbitrary `R`):

- `lift (R : u64 -> Prop) : t -> Prop = fun x -> R (pack x)`

Then prove your “iff lemma” using your codec round-trip lemma.

---

## Pattern A (recommended): `valid` + total `unpack`

### A1. Define types
- `type color = ...` (enum constructors)
- `type t = { f0: ...; f1: ...; f2: ...; color: color }`

### A2. Define enum codecs
- `color_to_u64 : color -> u64`
- `u64_to_color : u64 -> option color` (or total with default in unpack)

### A3. Define packing
- `pack : t -> u64`
  - set bit ranges for `f0`, `f1`, `f2`
  - set bit range for `color`
  - ensure reserved bits are zero (or document behavior)

### A4. Define validity
- `valid : u64 -> Prop`
  - reserved bits must be zero
  - enum bits must decode (`u64_to_color tag_bits <> None`)
  - any extra constraints your format requires

### A5. Define total unpack
- `unpack : u64 -> Tot t`
  - decode fields using masks/shifts
  - decode enum bits; if invalid, pick a default constructor (safe under `valid`)

### A6. Prove the key round-trip lemma
Prove once; everything else is rewriting:

- `pack_unpacked_roundtrip : w:u64 -> Lemma (valid w ==> pack (unpack w) == w)`

### A7. Define predicate transport
- `lift (R:u64 -> Prop) : t -> Prop = fun x -> R (pack x)`

### A8. Prove the iff transport lemma (the main deliverable)
- `lift_iff : R:(u64 -> Prop) -> w:u64 -> Lemma (valid w ==> (R w <-> lift R (unpack w)))`

Proof idea:
- assume `valid w`
- rewrite `pack (unpack w)` to `w` using `pack_unpacked_roundtrip`
- discharge by rewriting under `R`

### A9. Prove `valid_pack` to reuse existing packed proofs on the struct side
- `valid_pack : x:t -> Lemma (valid (pack x))`

This is what makes porting proofs trivial.

### A10. Proof reuse pattern (packed -> unpacked)
Given an old theorem:
- `old_thm : w:u64 -> Lemma (valid w ==> R w)`

Derive the struct-side theorem:
- `new_thm : x:t -> Lemma (lift R x)`

Sketch:
- prove `valid (pack x)` via `valid_pack x`
- apply `old_thm (pack x)`

---

## Pattern B: `unpack_opt : u64 -> option t`

### B1–B4. Same as A1–A4
Define `color`, `t`, codecs, `pack`, and validity constraints.

### B5. Define partial unpack
- `unpack_opt : u64 -> option t`
  - if reserved bits nonzero, return `None`
  - if enum decode fails, return `None`
  - else return `Some { ...decoded fields... }`

Optionally define:
- `valid w : Prop = unpack_opt w <> None`

### B6. Prove the key partial round-trip lemma
- `pack_of_unpack : w:u64 -> x:t -> Lemma (unpack_opt w == Some x ==> pack x == w)`

### B7. Define `lift`
- `lift (R:u64 -> Prop) : t -> Prop = fun x -> R (pack x)`

### B8. Prove the existential transport lemma
- `exists_equiv : R:(u64 -> Prop) -> w:u64 ->
    Lemma (valid w ==> (R w <-> exists x. unpack_opt w == Some x /\ lift R x))`

Proof idea:
- `->`: choose `x` from the `Some x` witness of `unpack_opt w`
- `<-`: use `pack_of_unpack` to rewrite `pack x` into `w`

### B9. Prove `valid_pack`
- `valid_pack : x:t -> Lemma (valid (pack x))`
  - usually via showing `unpack_opt (pack x) == Some x` (or at least not `None`)

---

## Why validity is required

Without restricting to well-formed encodings:
- there is no canonical `t` that corresponds to an arbitrary `u64`
- “for all `R`” forces parametric transport, and the only uniform map is `R ∘ pack`
- any equivalence must tie the struct witness to the packed word (`pack/unpack`)

---

## Recommended module organization

- `Headers.Colors.Types`
  - `color`, `t`
- `Headers.Colors.Codec`
  - `pack`, `unpack` / `unpack_opt`, `valid`
  - enum codecs and masks/bit helpers
- `Headers.Colors.Lemmas`
  - `pack_unpacked_roundtrip` or `pack_of_unpack`
  - `valid_pack`
  - `lift_iff` or `exists_equiv`
- `Headers.Colors.Reuse`
  - adapters that turn old packed theorems into new struct theorems via `lift`

---

## Minimal implementation checklist

- [ ] `type color`
- [ ] `type t = { f0; f1; f2; color }`
- [ ] `color_to_u64`, `u64_to_color`
- [ ] `pack : t -> u64`
- [ ] `valid : u64 -> Prop`
- [ ] `unpack : u64 -> Tot t` (Pattern A) OR `unpack_opt : u64 -> option t` (Pattern B)
- [ ] `pack_unpacked_roundtrip` (Pattern A) OR `pack_of_unpack` (Pattern B)
- [ ] `lift : (u64 -> Prop) -> t -> Prop` defined as `fun x -> R (pack x)`
- [ ] `lift_iff` (Pattern A) OR `exists_equiv` (Pattern B)
- [ ] `valid_pack : x:t -> Lemma (valid (pack x))` for proof reuse

---
