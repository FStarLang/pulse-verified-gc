# Parallel mark, Stage 1: model, statement, and tests

Branch `sheera/parallel-mark`, from `origin/main` `5033531`. The approach is the one `docs/parallel-sweep-phase1.md` used for the sweep: first a pure F* model and a theorem statement, then tests that run the model against the sequential spec. There is no Pulse yet.

**Status.**

- **The model and the theorem are written.** `mark_par_correct` says that every run that ends leaves the heap the sequential mark leaves. Beside it are its restatement in terms of reachability, the ownership lemma and the termination statement (§2). No existing `val` was changed, and no existing file was touched.
- **Stage 2, the proofs (§5).** `step_writes_own` is proved. `mark_par_reachable`, `mark_par_correct` and `mark_par_terminates` are still `admit`, and are the only `admit`s. Every lemma with a precondition is called once on arguments that meet it (§5, "Vacuity").
- **Changes after review.** Roots may now repeat and may be infix pointers, as the roots `gen_gc` darkens can be (§1, "Roots"). A termination statement, with its measure, is added and admitted (§2).
- **Tests: no counterexample.** 27,040 runs of the model over 439 heaps and 4,421 cut lists, with 1, 2, 4 and 8 ranges. Each one ended with the heap the sequential mark gives, byte for byte. No step wrote a colour its worker does not own, and every step lowered the termination measure.
- **All four broken variants are caught** (§4).

Everything is new, under `parallel-mark/`. The directory is left out of the root build.

| File | Contents |
|---|---|
| `parallel-mark/spec/GC.Spec.MarkPar.Exec.fst` | Executable twins of the sequential mark's ghost spec, each proven equal to the original. |
| `parallel-mark/spec/GC.Spec.MarkPar.Model.fst` | The model, the sequential reference, and the termination measure. |
| `parallel-mark/spec/GC.Spec.MarkPar.fst` | The four statements. It includes `GC.Spec.MarkPar.Model`, so the model's names are also its own. |
| `parallel-mark/spec/GC.Spec.MarkPar.Mutants.fst` | Four broken variants of the model. Used only by the tests. |
| `parallel-mark/spec/GC.Spec.MarkPar.Recolour.fst` | `recoloured g h`: h is g with some objects recoloured. One colour change keeps it (§5). |
| `parallel-mark/spec/GC.Spec.MarkPar.Field.fst` | A pointer in field i: its target is enumerated, non-blue, and a graph successor (§5). |
| `parallel-mark/spec/GC.Spec.MarkPar.Own.fst` | The ownership invariant and its proof; `step_writes_own` follows (§5). |
| `parallel-mark/spec/GC.Spec.MarkPar.Witness.fst` | A concrete heap meeting `mark_pre` (§5, "Vacuity"). |
| `parallel-mark/spec/GC.Spec.MarkPar.WitnessRun.fst` | A concrete run on it, through every kind of step, to the end (§5). |
| `parallel-mark/spec/GC.Spec.MarkPar.Vacuity.fst` | One satisfying call for every lemma with a precondition (§5). |
| `parallel-mark/test/` | The OCaml driver, the build script, the runner, and the `GC.Spec.ZeroAddr` realisation. |
| `parallel-mark/Makefile` | `make verify` and `make test`. |

Toolchain: only the pinned `./fstar` (F* `nightly-2026-10-17`, `f43a1127`, Z3 5.3.0), with the repo's own F* flags. The OCaml side uses opam switch `fstar-gc` (OCaml 4.14.0). Build with `gmake`.

---

## 1. The model, in plain words

### Ranges and owners

The heap from `zero_addr` to `heap_size` is cut into k address ranges by a list of k − 1 cut addresses. The cuts must increase strictly and lie strictly between `zero_addr` and `heap_size`. Otherwise they can be anywhere: on a header, inside a header word, in the middle of an object's fields.

An object **belongs to the range that holds its header**. Worker i owns range i. A pointer may point into the middle of a closure, at an infix object. Such a pointer is first resolved to the closure around it (`resolve_object`), and the closure's header decides the owner. So the infix header and its closure can lie in different ranges, and the closure's range is the one that counts.

### What each worker has

- a **work list**: grey objects it still has to scan. It is a stack, as in the sequential mark.
- an **inbox**: addresses other workers sent it, in the order they arrived.
- possibly an object it is **part-way through scanning**, and the next field to look at.

There is also the **network**: messages that have been sent but not yet delivered.

### The steps

A run is made of four kinds of step. Each happens all at once.

- **Pop i.** Worker i is not part-way through an object. It takes the top object off its work list and blackens it. If the object can be scanned and has fields, the worker starts on field 1.
- **Scan i.** Worker i looks at the next field of the object it is scanning. If the field is not a pointer, nothing else happens. If it is, the worker resolves it to an object c and looks up c's owner.
  - If worker i owns c and c is white, it greys c and pushes it on its work list. If c is grey or black, it does nothing.
  - If another range owns c, worker i sends c's address to that range. It does not read c's colour.
- **Take i.** Worker i takes the first address from its inbox. If that object is white, it greys it and pushes it.
- **Deliver j.** Message j in the network is put at the end of its range's inbox.

Each root is resolved to the object it names, and that object starts in its owner's inbox (§1, "Roots"). The network starts empty.

A step can only change a colour in two ways: greying a white object, or blackening the object just popped. Both are done by the owner. No step reads the colour of an object its worker does not own.

### Roots

The roots are what the real callers pass:

- `gen_gc` darkens a raw roots array with `check_and_darken_bounded_spec` (`mark-and-sweep/impl/GC.Impl.MarkBounded.fsti`). It skips values that are not pointers, resolves an infix pointer to its closure, and greys the object only if it is white. A root may therefore be an interior pointer (`root_points_to_object` says so), and the same object may be named twice.
- `collect_with_roots` takes roots that are already grey and on the stack, and distinct (`is_vertex_set`).

So the model allows roots that repeat and roots that are infix pointers. Each root r is resolved, and `resolve_object r g` goes to its owner's inbox. A repeat is harmless: the second Take finds the object no longer white and does nothing. The precondition asks only that each root *names* an enumerated white object. Roots stay `obj_addr` values: a value that is not a pointer at all is the caller's to skip.

### Interleavings

A **schedule** is any list of these steps. Running a step that cannot happen, such as popping an empty work list, leaves the state unchanged. So every list of steps is a schedule, and every interleaving of the workers is some schedule. Any message may be delivered next, so messages can overtake one another. Two workers can send the same address, and so can one worker twice, and nothing removes the duplicates.

`run cs g roots sched` is the state after running `sched` from the initial state.

### The end

Marking has **ended** (`quiescent`) when every work list and every inbox is empty, the network is empty, and no worker is part-way through an object. The model does not say how workers find this out. Detecting it is a separate problem, and mutant 4 (§4) shows what goes wrong if messages in transit are forgotten.

### Choices to review

These are places where the description left room, and what the model chose:

1. **Scanning is one field per step**, not one object per step. This gives strictly more interleavings, since other workers can run between two fields of the same object.
2. **A worker may take from its inbox while it is part-way through an object.** Nothing depends on this. Forbidding it would only remove interleavings.
3. **A colour check and the write that follows it are one step.** For instance, "if c is white, grey it" happens at once. This is sound only because one worker writes c's colour and every other worker leaves it alone, so the eventual Pulse version needs no atomic instruction for it. The ownership lemma (§2) states this rule.
4. **The network can reorder messages; each inbox is first in, first out.** Together these give every delivery order.
5. **Roots name white objects.** In the sequential precondition the roots are already grey and on the stack. Here the objects they name are white, because greying them is the owners' job.

## 2. The statement

The sequential reference takes the objects the roots name (`root_objs`: each root resolved, repeats removed), greys them, and runs the existing `GC.Spec.Mark.mark` with them as its stack. This is what `gen_gc`'s darkening followed by the mark does, up to the order of the stack:

```fstar
let sequential_mark (g: heap) (roots: list obj_addr) : GTot heap =
  let rs = root_objs g roots in
  Mark.mark (grey_all g rs) (Seq.seq_of_list rs)
```

The precondition is the sequential one (`end_to_end_correctness`), with the named objects white:

```fstar
let mark_pre (g: heap) (roots: list obj_addr) : prop =
  well_formed_heap g /\ Mark.noGreyObjects g /\ Mark.no_black_objects g /\
  Mark.no_pointer_to_blue g /\
  (forall (r: obj_addr). L.memP r roots ==>
     Seq.mem (resolve_object r g) (objects zero_addr g) /\ is_white (resolve_object r g) g)
```

**The theorem.** For every cut list and every schedule, if the run has ended, its heap equals the sequential mark's heap:

```fstar
val mark_par_correct (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs /\ quiescent (run cs g roots sched))
          (ensures (run cs g roots sched).heap == sequential_mark g roots)
```

The heaps are equal as byte sequences, so this covers every colour and every other byte.

**The same conclusion, stated without the sequential mark.** `mark_par_reachable` has the same hypotheses, plus the graph hypotheses of `end_to_end_correctness` for the named objects (`graph_pre`). It says three things about the final heap, where reachable means reachable from `root_objs g roots`:

- an enumerated object is black exactly when it is reachable from the roots;
- each reachable object's header is its original header made black;
- every other word of the heap is unchanged.

It should follow from `mark_par_correct` and the sequential mark's existing theorems (`mark_reachable_is_black`, `mark_black_is_reachable`, and the field and wosize preservation lemmas).

**Only the owner writes a colour.** Take any state that a run reaches. `step_writes_own` says the next step changes the heap only in the header of an enumerated object, and the worker that takes the step owns that object. The model is built so this holds. The lemma states the rule so that the Pulse version can rely on it later.

```fstar
val step_writes_own (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
    (e: event) (a: hp_addr)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs /\
                    (let s = run cs g roots sched in
                     read_word (step cs s e).heap a <> read_word s.heap a))
          (ensures exists (x: obj_addr). a == hd_address x /\ Seq.mem x (objects zero_addr g) /\
                                         owner cs x == actor e)
```

**Every run ends.** `mark_par_terminates` bounds the number of *effective* steps, those that are enabled when they are taken. A step that is not enabled changes nothing, and a run that has not ended always has an enabled step. So a run that keeps taking enabled steps reaches `quiescent` within the bound:

```fstar
val mark_par_terminates (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs)
          (ensures (let s = run cs g roots sched in
                    effective_steps cs (init cs g roots) sched <= measure (init cs g roots) /\
                    (forall (e: event). ~(L.mem e (enabled s)) ==> step cs s e == s) /\
                    (enabled s == [] <==> quiescent s)))
```

The measure counts the work still to do, in steps. With f the number of fields a worker scans in x (its wosize, or 0 if x is no-scan):

| Item | Weight | Why |
|---|---|---|
| a white enumerated object x | 2 + 3f | grey and push it, pop it, scan its f fields |
| an object x on a work list | 1 + 3f | pop it, scan its fields |
| a field not yet scanned | 3 | scan it; deliver the message it may send; take it |
| a message in transit | 2 | deliver it, take it |
| an inbox entry | 1 | take it |

Every effective step lowers the measure by at least one. Greying a white object turns 2 + 3f into 1 + 3f, and the Take or Scan that does it removes an inbox entry or a field as well. A pop turns 1 + 3f into 3f. A scan removes 3 and adds at most 2. A delivery turns 2 into 1. A Take that finds the object non-white removes 1. At the start the measure is at most 3 × `heap_words` plus the number of roots.

All four statements are `admit`. `make verify` reports exactly those four, and no other `admit` or `assume`.

**What the statement does not say.**

- **It does not depend on where the cuts are.** `valid_cuts` is a hypothesis, but the proof should need only that `owner` is a function. The cut list then decides only who does the work.

## 3. How it was tested

### Running the spec itself

`GC.Spec.Mark.mark` and everything under it are `GTot`, so extraction erases them. `GC.Spec.MarkPar.Exec` gives each one a `Tot` twin, and the twin's type states that it equals the original:

```fstar
let resolve_x (a: obj_addr) (g: heap) : r:obj_addr{r == resolve_object a g} = ...
let mark_x (g: heap) (st: seq obj_addr) : r:heap{r == Mark.mark g st} = ...
```

The colour tests, `makeGray`, `makeBlack`, `wosize_of_object`, `is_no_scan`, `is_infix`, `resolve_object`, `get_field`, `objects`, `push_children`, `mark_step` and `mark_aux` get twins the same way. The model is built from these twins, and `sequential_mark_x` is proven equal to `sequential_mark`. So the test compares the very functions that appear in the theorem; nothing is translated by hand.

### Build

`make test` verifies the three modules, then extracts them with Custard (`--codegen OCaml --custard_split`), as the sweep's tests do. It builds the driver against the F* OCaml runtime sources, fails if any erased value is still used, and runs 16 jobs, 8 at a time. `test/GC_Spec_ZeroAddr.ml` is copied from the sweep: `zero_addr = 2048`, and the heap holds `PS_WORDS` words after it.

### What each run checks

For each heap, the driver first checks the executable part of the precondition:

- the heap has objects, and each one fits;
- no enumerated object has the infix tag;
- every object is white or blue;
- every pointer field of a scannable, non-blue object resolves to an enumerated, non-blue object, and an infix target meets the infix conditions;
- each root, resolved, is an enumerated white object.

It then checks the reference itself, against a reachability search the driver does on its own (with its own copy of `resolve_object`). The reference must make exactly the reachable objects black, each header must be its original made black, and every other word must be unchanged. That is `mark_par_reachable`'s conclusion, checked on the reference.

Then, for each cut list and each run of the model, it checks:

1. **At every step:** the step changes only bytes inside the header of an enumerated object owned by the acting worker. This is `step_writes_own`. It also checks that the mutant module's copy of the step, run with no mutation, gives the same state as `step`.
2. **Termination:** every step taken lowers `measure`. One step in eight, the driver also tries a step that is not enabled and checks it changes nothing. At the end, the number of steps is at most the initial measure, and `effective_steps` counts them correctly.
3. **At the end:** no step is enabled exactly when `quiescent` holds.
4. **The result:** the final heap equals `sequential_mark_x g roots`, byte for byte.
5. **Replay:** running the recorded schedule through `run`, the function in the theorem, gives the same heap.

The first failure stops the job and prints the heap, the cuts, the roots, the whole schedule, and the first differing word.

### Interleavings

Each run draws its steps at random from the enabled ones, under one of five strategies, used in turn:

| Strategy | What it favours |
|---|---|
| uniform | any enabled step |
| late delivery | worker steps first; deliver only when nothing else can happen. This lets the most messages build up. |
| newest first | half the time, deliver the newest message, so messages overtake one another |
| one worker | stay with one worker 90% of the time. Long solo runs, then a switch. |
| round robin | one step per worker in turn, with deliveries in between |

### Heaps

**Generated (428 heaps, 4 to 128 words, 15 seeds).**

- **Objects:** ordinary blocks (tags 0 to 2, wosize 0 to 7, mostly 0 to 2); no-scan blocks (tag 252); and closures (tag 247, wosize 4 to 11) with one or two infix headers inside.
- **Colours:** white, with 0%, 10% or 30% free (blue) blocks.
- **Fields of live scannable objects:** each is a pointer to a live object, or to an infix object in a live closure, with probability 0.2, 0.5, 0.8 or 1, chosen per heap. Otherwise it is a word that is not a pointer: 0, an odd integer, an aligned address below or above the heap, an unaligned address inside it, or a random word.
- **No-scan bodies and free blocks:** anything, including addresses of live and free objects. The mark must never follow these.
- **Roots:** none (5%); one to four distinct live objects; or every live object (10%). A third of the time an infix pointer into a live closure is added, and a third of the time one root is repeated.
- **Cut lists:** for k = 2, 4 and 8, three cut lists per heap; for k = 1, the empty one. Each cut is one of four kinds: any address; a header; one byte into a header word or an object's first field; or between a closure's header and one of its infix headers. The last kind puts an infix header in a different range from its closure.
- **Runs:** 5 runs of the model for each cut list.

**Hand-built (11 heaps, `PS_WORDS=40`).** Each has its own cut lists and the generated ones too, with 40 runs of the model for each cut list.

| Case | What it exercises |
|---|---|
| cycle across two ranges | a reference cycle across a cut, with cuts on a header, inside a header word, and inside a field |
| chain bouncing between ranges | a chain whose every link is in another range (up to 6 ranges) |
| infix header in another range than its closure | a pointer to an infix object whose header is across a cut from its closure's header |
| two ranges send the same object | duplicate messages for one object, from two senders |
| roots in every range | plus an unreachable cycle across ranges, which must stay white |
| no roots | nothing may be marked |
| no-scan object in another range | it is blackened, and the pointer-like word inside it is not followed |
| cuts inside a header word and inside fields | cuts at odd addresses |
| self pointer next to free blocks | |
| wosize-0 objects, and an object with no pointers | |
| infix roots across a cut from their closure, and repeated roots | two infix roots into one closure, the closure itself, and a repeated root |

### Results

| | |
|---|---|
| model runs | 27,040 (k = 1: 2,580; k = 2: 8,500; k = 4: 7,780; k = 8: 7,740) |
| steps run | 449,930 |
| messages sent between ranges | 53,285; at most 37 in transit at once |
| deliveries that overtook an older message | 16,808 |
| cut lists that put a reachable closure and its infix header in different ranges | 1,054 |
| heaps with an infix root / with a repeated root | 65 / 157 |
| reachable objects (black at the end) / unreachable white objects (left white) | 1,348 / 624 |
| steps tried that were not enabled (each changed nothing) | 48,575 |
| effective steps, as a share of the initial measure | at most 0.88 |
| failures | none |

## 4. Broken variants

`GC.Spec.MarkPar.Mutants` changes one rule at a time. Each mutant runs twice on every generated cut list and ten times on every hand-built one, under the same strategies. A mutant counts as caught if its final heap differs from the sequential mark's, or if one of its steps writes a colour its worker does not own.

| Mutant | The bug | Caught | How it shows |
|---|---|---|---|
| 1 foreign_grey | A worker that finds a white child in another range greys it itself, then sends it. The owner then finds it grey and never pushes it, so nobody scans it. | 3,157 of 9,970 | heap differs (objects left grey) and owner rule broken, every time |
| 2 overwrite | Each inbox holds one address: delivering to a non-empty inbox replaces its last address, so a message is lost. | 150 of 9,970 | heap differs |
| 3 route_raw | A child is routed by the range of the raw pointer, not of the closure it resolves to. An infix header across a cut from its closure sends the closure to a worker that does not own it. | 515 of 9,970 | owner rule broken. The final heap is still right, because the model's steps are atomic; in real code this is a race on the closure's header. |
| 4 early_stop | Marking is taken to have ended when work lists and inboxes are empty, while messages are still in transit. | 1,945 of 9,970 | heap differs (reachable objects left white) |

A mutant is caught only when the case brings out its bug. With one range, for instance, mutants 1 and 3 behave exactly like the model. The runner fails if any mutant is never caught across all jobs.

## 5. The proofs

### The heap relation (`GC.Spec.MarkPar.Recolour`)

Both marks change the heap only by `set_object_color`, on an enumerated object that is not blue, to a colour that is not blue. `recoloured g h` collects what such changes keep:

- the same objects, a well-formed heap, the same graph, nothing pointing to blue;
- every word that is not the header of an enumerated object is g's word;
- every enumerated object keeps its wosize and tag; it is blue exactly when it is in g;
- every address resolves as in g, and every field of an enumerated object reads as in g.

`recoloured_set` shows one such colour change keeps it, from the colour-change lemmas the sequential proof already has (`color_change_preserves_objects`, `color_change_preserves_wf`, `color_preserves_create_graph`, `color_change_preserves_resolve`, `color_preserves_get_field`, and others). At the end, a header is fixed by its wosize, tag and colour (`colorHeader_idempotent` and `colorHeader_same_wz_tag` from `GC.Spec.SweepCoalesce.Helpers`). So a recoloured heap is fixed by its colours (`recoloured_marked_as`), and two heaps that agree on every aligned word are equal (`heap_ext`, from `write_word_id`).

### Ownership (`GC.Spec.MarkPar.Own`): `step_writes_own`

The invariant, in every state a run reaches:

- the heap is g recoloured;
- every work list holds distinct grey objects of its own range;
- every inbox entry, and every message's address, is a non-blue enumerated object of the range it is for;
- a worker part-way through an object owns it; the object is black and scannable, and the next field is within its wosize.

The initial state meets it: each root names a white object, and it goes to its owner's inbox. Each step keeps it:

- **Pop** blackens a grey object from the worker's own list.
- **Scan** reads a field of a black object. A pointer there resolves to an enumerated, non-blue object (`GC.Spec.MarkPar.Field`, from well-formedness and `no_pointer_to_blue`). If the worker owns that object and it is white, the worker greys it and pushes it. Being white, it is on no work list, so the work list stays free of repeats. Otherwise the object is sent to its owner.
- **Take** greys and pushes an inbox entry if it is white.
- **Deliver** moves a message to the inbox of its range.

Each step recolours at most one object, and that object is in the acting worker's range. A step for worker i never touches another worker's record, and everything another worker holds is owned by that worker, so it differs from the object i recolours. `step_writes_own` is this fact, for the step after any run.

Each step case is proved by small lemmas, each with a narrow precondition: one for replacing a worker's record (`replace_worker`), one for greying and pushing (`push_step`), and one for a change with no colour write (`move_step`). Proved whole, the step cases timed out. Split this way, the module checks in under 7 seconds. No rlimit is above 60.

### Vacuity

`GC.Spec.MarkPar.Vacuity` calls every lemma that has a precondition, once, on arguments that meet it. If a precondition were contradictory, its call would not verify.

The arguments come from a concrete heap, `GC.Spec.MarkPar.Witness.g2`: the all-zero heap with two objects written into it.

- A, at `zero_addr + 8`, has wosize 1 and tag 0, is white, and its field points to B.
- B, at `zero_addr + 24`, has a zero header.
- Every later word is zero, which reads as further white objects of wosize 0.

`g2_pre` proves `mark_pre g2 [A]` from these words alone, including well-formedness. `heap_size` is abstract, so the witness assumes the heap has room for A and B (`big`: `zero_addr + 32 <= heap_size`, which holds in the tests for `PS_WORDS >= 4`).

`GC.Spec.MarkPar.WitnessRun` cuts g2 at B's header, so A is worker 0's and B is worker 1's. It then runs `Take 0; Pop 0; Scan 0; Deliver 0; Take 1; Pop 1` and proves the shape of each state. The run greys and blackens A, sends B to worker 1 when scanning A's field, and greys and blackens B there. So it passes through every kind of step and ends quiescent. Its states are the arguments for the step lemmas.

`step_writes_own` itself is called with the empty schedule and the first Take, whose write to A's header is a real change.

## 6. Running it

```
cd parallel-mark
gmake verify    # every module; reports the admits that remain
gmake test      # verify, extract, build, and run all jobs (tens of minutes on 8 cores; recomputing the measure at every step dominates)
```

The logs are in `parallel-mark/_build/logs/`, one per job. Each ends with an `ok:` line, coverage counts, and one line per mutant.
