# Parallel mark: design

Nov 2, 2026

## Summary

Each of k workers runs the ordinary sequential mark on the objects whose header lies in its address range, and hands every pointer into another range to that range's owner. Five rules make this race-free:

1. **Ownership by header.** An object belongs to the range holding its header, `hd_address v = v - 8`. During a round, only its owner reads or writes that header.
2. **Fields are read-only.** During a round no field or infix header is written, so any worker may read them, even across a cut.
3. **Nobody waits on anybody.** A full stack or a full inbox sets the worker's own overflow flag instead of blocking.
4. **A round ends when `work_in_flight` is 0.** Stacks and inboxes are never inspected to decide this.
5. **Anything touching several owners' objects runs between rounds, on one thread:** darkening the roots, repairing overflow, and later ephemeron checks and field writes.

**Status.** Modelled and proved in F\*, with no `admit` (Stage 3, `GC.Spec.MarkPar2`; see `docs/parallel-mark-stage3.md`). The model takes try_take and the counter read as two steps, as real code does them. A finished run leaves the sequential mark's heap. A worker step reads and writes only what the race-freedom table allows. `work_in_flight` equals the counted entries, and a 0 is final. Every run ends. Random-interleaving runs match the sequential mark, and six broken variants are caught. Proving found no flaw in the design. "Atomicity in the model" lists what the C code must keep atomic. An unverified C prototype, for measurement only, is reported in `docs/parallel-mark-prototype.md`.

## State

Each worker keeps a private stack, a lockable inbox and a private flag; the only state every worker updates is one atomic counter.

| Name | What it is | Who touches it |
| --- | --- | --- |
| `c[0..k]` | Cut addresses; `c[0]` is the heap's start, `c[k]` its end | Set by the main thread before round 1; read-only after |
| `owner(a)` | The `i` with `c[i] <= a < c[i+1]` | Arithmetic only, no memory read |
| `stack[i]` | Mark stack of worker `i`, capacity `S` | Worker `i` only |
| `inbox[i]` | Queue of raw pointers for worker `i`, capacity `Q`, one lock | Any worker appends; worker `i` takes; both under the lock |
| `overflow[i]` | Flag: worker `i` dropped or could not push something | Written by worker `i`; read by the main thread after the stop barrier |
| `work_in_flight` | Count of messages and stack entries not yet fully handled | Every worker, with atomic add and subtract |

## The worker algorithm

A worker repeatedly pops its own stack, then takes from its inbox, and stops only when `work_in_flight` is 0.

```
worker(me):
  loop:
    if stack[me] not empty:
      x = pop(stack[me]); scan(x); work_in_flight -= 1
    else if try_take(inbox[me]) gives v:     // tested and taken under the lock
      accept(v); work_in_flight -= 1
    else if work_in_flight == 0:
      arrive at the stop barrier and wait    // only the main thread releases it
    else:
      pause, then look again                 // a message may still come

try_take(inbox[i]):
  lock inbox[i]
  if empty: result = none else: result = remove one entry
  unlock inbox[i]; return result

scan(x):                                     // x is mine and grey
  colour(x) = black
  if no_scan(x): return
  for i in 1 .. wosize(x):
    v = field(x, i)                          // may lie past a cut: read-only
    if is_heap_pointer(v): route(v)

route(v):
  j = owner(v - 8)                           // arithmetic only
  if j == me: accept(v) else: send(j, v)

send(j, v):
  lock inbox[j]
  if inbox[j] full: overflow[me] = true      // dropped; fix-up finds it
  else: work_in_flight += 1; append v to inbox[j]
  unlock inbox[j]

accept(v):                                   // v - 8 is in my range
  h = header at v - 8                        // mine: no race
  if is_infix(h):
    c = v - infix_offset(h)                  // the closure's start
    if owner(c - 8) != me: send(owner(c - 8), c); return
    v = c
  if colour(v) == white:
    colour(v) = grey
    if stack[me] full: overflow[me] = true   // stays grey; fix-up finds it
    else: work_in_flight += 1; push v on stack[me]
```

Every header read or written here is at `v - 8` for a `v` that `route` or the inbox has already shown to be in the worker's own range, or at `c - 8` for a closure `c` that the `owner(c - 8)` test has just shown to be mine. Fields are only read, in `scan`.

## Ending a round: `work_in_flight`

A round ends exactly when `work_in_flight` reaches 0, and a 0 is always final, so delays in seeing stacks and inboxes do not matter.

**The rules.**

1. Each piece of work, a message or a stack entry, adds 1 before it exists: before the append in `send`, before the push in `accept`.
2. It subtracts 1 only after it is fully handled, after any work it created has been added.
3. Before releasing the workers, the main thread sets `work_in_flight` to the number of entries it pushed.

**Why a 0 is final.** Only a thread holding counted work ever adds 1. At 0 nobody holds work, so nobody can add 1 again; a thread that reads 0, even late, reads the final 0.

**What it needs.** Atomic add and subtract on the counter, sequentially consistent, which is C11's default. The count never exceeds `k * (S + Q + 1)`: each stack and inbox entry, plus the one item each worker may hold after a pop or a take. So 32 bits suffice; F\*'s 32-bit CAS is truly atomic since FStar#4812.

## Overflow and the fix-up phase

Overflow never stops a round; after the stop barrier one thread repairs it alone, with one heap walk, as today's rescan does.

**Two kinds of overflow, both recoverable from the heap itself.**

- **Stack full, in `accept`:** the object stays grey but is not pushed.
- **Inbox full, in `send`:** the message is dropped, but the object being scanned is black and still points to the white child.

**Fix-up, on the main thread, after every worker has stopped.**

1. Clear every `overflow[i]` and `overflow_main`.
2. Walk every object from the heap's start.
3. A grey object: push it on its owner's stack.
4. A black, scannable object: for each field pointing to a white object, resolving infix pointers, grey that object. Push it on its owner's stack only if it lies below the walk's position; one above it is pushed by step 3 when the walk reaches it, so no object is pushed twice.
5. If that stack is full: leave the object grey and set the main thread's own flag, `overflow_main`.
6. If anything was pushed: set `work_in_flight` to the number pushed and start a new round. Otherwise marking is done.

Each repair round pushes at least one object, and every pushed object ends black, so the rounds end.

That argument needs `S` of at least 1; `Q` may be 0, which is slow but still correct.

**Performance trap: repeated overflow.** With a small `Q` and many pointers crossing ranges, every round can overflow again, and each round costs a full heap walk. A small `S` does the same: an object with `n` white children in its own range needs about `n / S` rounds, since a round, and the fix-up after it, push at most `S` entries on each stack. To limit this, enlarge `S` or `Q` before the next round, and measure how often overflow happens. OCaml avoids the `S` case by pushing ranges, (object, next field), instead of single children, so one entry stands for many fields.

## Phases

Workers run in parallel only between a start and a stop barrier; everything that touches several owners' objects runs alone, between rounds.

```
Setup, main thread: cut the heap into k ranges; grey the roots, push on owners' stacks
  -> start barrier
  -> parallel round, k workers, until work_in_flight is 0
  -> stop barrier (all k workers arrived)
  -> any overflow[i] or overflow_main set?  yes: fix-up, one thread -> back to start barrier
  -> no: new ephemeron roots? (later)  yes: push them -> back to start barrier
  -> no: field writes, one thread (later)
  -> sweep
```

Both loops return to the start barrier, so a collection may run several parallel rounds; with no overflow and no ephemerons it runs exactly one.

## Requirements on the implementation

The design is correct only if the implementation meets these six requirements.

1. **The stop barrier is a real barrier.** A worker that reads 0 arrives and waits; the main thread starts the fix-up only after all `k` have arrived. Otherwise a slow worker can start marking again while the fix-up is writing headers in its range.
2. **The barrier is reusable.** Rounds repeat, so a fast worker must never enter the next round's barrier before a slow one has left the last. Starting threads per round and joining them, as `par_sweep.c` does, is the simplest safe choice; it costs 25 to 100 µs per round.
3. **The barrier orders memory.** The main thread's counter reset and stack pushes must be visible to workers before they start, and the workers' header writes visible to the main thread before the fix-up. A join gives both.
4. **The atomics stay sequentially consistent,** C11's default. Correctness needs only that each add and subtract is atomic: the count is set before the workers start, never returns to 0 inside a round, and carries no data, since stacks and inboxes are handed over through locks and the barriers. So even a relaxed read cannot see a 0 that is not final; sequential consistency only keeps the argument simple.
5. **The main thread has its own flag, `overflow_main`,** set when a stack is full during setup or fix-up. The overflow check after each round reads every `overflow[i]` and `overflow_main`, and the fix-up clears all of them.
6. **Setup darkens the roots as `check_and_darken_bounded_spec` does:** it skips a root that is not a pointer, resolves an infix pointer to its closure, and greys and pushes the object only if it is white. A repeated root is then pushed once, and no infix header is ever coloured.

## Atomicity in the model

The F\* model (`GC.Spec.MarkPar2.Model`) runs each worker as a sequence of steps, and treats each step as one indivisible event. A real worker's step is several machine operations. So the model is sound only if every interleaving of real operations gives the same result as some order of whole steps. That holds when each step does at most one shared action, and every other operation in it touches only state no other thread reads or writes during a round. The private operations then commute with anything another thread does, so the step can be taken to happen at the instant of its shared action.

The shared actions are a critical section on one inbox's lock, and one atomic operation on `work_in_flight`. Each row below is a model step, the real operations it stands for, and why treating them as one is sound. The last column is what the C code must do so that it stays sound.

| Model step | Real operations, in order | Why one step is sound | Requirement on the C code |
| --- | --- | --- | --- |
| **Pop** (`Loop`, stack not empty) | Test own stack; pop x; read x's header (size, tag); write x's colour black | Stack and x's header are private: x is in my range, and during a round only the owner touches a header (rule 1) | A1 |
| **Take** (`Loop`, stack empty, inbox not empty) | Test own stack; lock own inbox; test it; remove the oldest entry; unlock | Stack test private; the rest is one critical section | A2 |
| **Empty take** (`Loop` → `Idle`) | Test own stack; lock own inbox; find it empty; unlock | Stack test private; one critical section | A2 |
| **Counter read** (`Idle` → `Stopped` or `Loop`) | One atomic load of `work_in_flight`; at 0, return from the thread function | One atomic action. A message may arrive between the empty take and this read; the model has them as two steps, so it covers that | A3 |
| **Scan one field** (`Scan`) | Read field j of x; test whether it is a heap pointer; `route`: compute the owner, then `accept` (own range) or `send` (other range) | The field is read-only during a round (rule 2), so when it is read does not matter. `route`'s owner test is arithmetic. `accept` and `send` are below | A4, and those of accept and send |
| **Accept** (`Got v`, or inside a scan) | Read header at v − 8; if infix, compute the closure c and test its owner; if another's, `send`; else read c's colour; if white: write grey, then either set own flag (stack full) or add 1 to `work_in_flight` and push c | Headers at v − 8 and c − 8 are mine (the owner test comes first), the stack and flag are mine. The one shared action is the atomic add, or the `send` | A1, A5, A6 |
| **Send**, part of a scan or accept step | Lock inbox j; test full; if full set own flag; else add 1 to `work_in_flight` and append v; unlock | One critical section. The add happens inside it but is not protected by it, so another thread may see the higher count before the append. That is harmless: the sender still holds a counted item, so the count was already at least 1, and a reader only tells 0 from not-0. The owner cannot take v before the unlock | A5, A6 |
| **Finish** | One atomic subtract of 1 from `work_in_flight` | One atomic action | A3, A6 |
| **Main**: overflow check, fix-up, counter reset, restart | Read every flag; clear them; walk the heap, greying and pushing; set `work_in_flight`; start k threads | No worker thread exists between the join and the next create, so nothing observes the main thread | A7 |
| **Setup** (`init`) | Darken the roots; set `work_in_flight`; start k threads | As for Main: it runs before any worker exists | A7 |

A step may hold several private operations and one shared one, as Accept does, or a field read and a send, as Scan does. Two shared actions are never in one step: try_take and the counter read used to be one step, and are now two (`Loop` → `Idle` → `Stopped` or `Loop`).

**Requirements on the C code.** These add to "Requirements on the implementation" above.

- **A1. Headers are written whole and only by their owner.** A colour change reads the header word, changes the colour bits, and writes the word back, with no other thread reading or writing that word during a round. The header is one aligned 8-byte word (assumption 6), and the store is an 8-byte store of that word only. No atomic is needed.
- **A2. try_take is one critical section,** with the empty test and the removal under the same hold of `inbox[me]`'s lock. The stack test before it needs no lock, because only `me` pushes to `stack[me]`.
- **A3. The counter read is a separate atomic load,** made after try_take has released the lock, and the worker stops only on a 0 from that load. The worker never stops on its own stack and inbox being empty. Mutant 6 in the tests does that, and is caught.
- **A4. Fields are read with plain loads,** and nobody writes them during a round. If marking ever writes fields (see Later phases), this step is no longer one event.
- **A5. send is one critical section on `inbox[j]`,** holding the full test, the flag or the append, and the add to `work_in_flight`. The full test and the append must not be split: a split could overfill the inbox, or drop a message without setting a flag.
- **A6. Order of counter updates.** The add for a new item comes before the item is visible to anyone: before the unlock in `send`, and before the push in `accept`. The subtract for an item comes after everything its handling adds (Finish is the last step). Every update is one atomic read-modify-write.
- **A7. Main and setup run only with no worker thread alive:** after joining all k threads and before creating the next k. Thread create and join supply the memory ordering for the stacks, flags, headers and the counter reset (requirements 1–3).

## Why it is race-free

During a round, every word is either written by one thread only and read by no other, or read-only, or reached through a lock or an atomic; between rounds one thread runs alone.

| Word | Read during a round by | Written during a round by |
| --- | --- | --- |
| Header of object `x` | The owner of `x` | The owner of `x`, colour bits only |
| Field of `x` | The owner of `x`, in `scan` | Nobody |
| Infix header | The worker that owns its address, in `accept` | Nobody |
| `stack[i]` | Worker `i` | Worker `i` |
| `inbox[i]` | Worker `i`, under the lock | Senders and worker `i`, under the lock |
| `overflow[i]` | Nobody | Worker `i` |
| `work_in_flight` | Every worker, atomically | Every worker, atomically |

**Assumptions.** The table holds only while these do.

1. The program is paused for the whole of marking.
2. During a round, only header colour bits are written. This breaks if marking ever writes fields; see Later phases.
3. The heap layout is fixed: no allocation, no moving.
4. Every heap pointer in a field points at an object's first field, or just past an infix header inside a closure.
5. The cuts cover the whole heap.
6. A header is one aligned 8-byte word, read and written whole.

## Later phases: ephemerons and field writes

The verified GC has neither today; the design leaves room for both by running them between rounds, on one thread.

- **Ephemeron check.** After the overflow check, one thread finds every ephemeron whose key is black and whose data is white. Those data objects are new roots: grey them, push them on their owners' stacks, and run another parallel round. Repeat until none are found.
- **Field writes.** After the last round, one thread shortcuts pointers to `Forward_tag` blocks, and clears weak entries whose keys are white. This needs a list of weak objects and ephemerons kept by the runtime.

A worker writing a pointer field of its own object during a round would also be race-free, since only the owner reads its pointer fields. The one exception to "only the owner reads its fields" is an infix header: it is a word of its closure, but the worker that owns its address reads it, in `accept`. Nobody writes infix headers, so this stays race-free. What must wait for a phase boundary is touching another owner's object, as following a chain of forward blocks does.

## Open questions

1. **Inboxes:** one lock each, as written, or one single-writer channel per pair of workers, which needs no lock?
2. **Capacities `S` and `Q`:** how large, relative to the heap? How often do the benchmarks overflow?
3. **Counter contention:** every push and pop touches `work_in_flight`. Later, count a worker's own stack locally and update the shared count only when it becomes busy or idle?
4. **Cuts:** equal slices of the heap, or slices by live data from the last collection?
5. **Idle waiting:** spin, or sleep and be woken?
6. **Pulse support:** an atomic 32-bit counter, a lock per inbox, and two barriers. Which parts stay trusted C, as `par_sweep.c` does for the sweep?

## Statement changes

Stage 3 states the theorems for the model of this design, `GC.Spec.MarkPar2`, beside the Stage 1–2 ones for `GC.Spec.MarkPar`, which are unchanged. Where a statement differs from its Stage 1–2 counterpart, this is what changed and why. None is weaker for the design: each follows what the design does.

1. **The run has ended when the main thread says so.** `mark_par_correct` and `mark_par_reachable` assume `(run k g roots sched).finished` in place of `quiescent (run cs g roots sched)`. In the design a round ends at `work_in_flight = 0`, and marking ends only when the main thread finds no overflow flag set, or the fix-up pushes nothing. That moment is `finished`. A quiescent state of a round can still have work left for the fix-up.
2. **The configuration includes the capacities.** The cut list becomes a configuration `k = { cs; cap_s; cap_q }`, and `valid_cuts cs` becomes `valid_cfg k`: valid cuts and `S >= 1`. The design needs `S >= 1` ("Overflow and the fix-up phase"), and the theorem is false without it. For example, with `S = 0` and root A, setup greys A but cannot push it, and every later fix-up fails to push it too. The fix-up then pushes nothing, so marking is done with A grey.
3. **The ownership lemma is about worker steps.** `step_writes_own` takes worker `i`'s step, `W i`, in place of any event with its actor. The main thread writes headers in every range by design, but only between rounds. `main_at_barrier` states that it changes nothing unless every worker has stopped.
4. **The step lemma also covers reads.** `step_reads_own` is new: a worker step gives the same result on any heap that agrees on the words `readable` allows, which are its own range and the fields of the object it is scanning. `step_race_free` follows from it and `step_writes_own`.
5. **Termination allows spinning.** "Enabled" now means an event that makes progress. try_take and the counter read are separate steps (`Loop` → `Idle` → `Loop`, `Stopped`), so a worker with nothing to do, while `work_in_flight > 0`, spins between `Loop` and `Idle`. Those spin steps change the state but are not enabled. The statement has three parts. First, at most `measure (init ...)` effective steps. Second, a step that is not enabled changes nothing, or is a spin step that keeps the measure and that the same worker's next step undoes. Third, nothing is enabled exactly when marking is done. So a schedule runs for ever only if some workers spin while the ones with work are never scheduled. An `Idle` worker is enabled when the counter is 0 or a message has come into its inbox. To make spinning keep the measure, an `Idle` worker's weight depends on whether the counter is 0 (`idle_w`).

One proof lemma's precondition was relaxed, with no theorem affected. `GC.Spec.MarkPar2.Step.scan_unscanned` asked for a pointer field at the later index. Its proof needs only that the index lies within the scan. Asking only that lets the vacuity checks meet it on the witness heap, where no object has two pointer fields.

Roots are object addresses, as in Stage 1. Requirement 6's "skip a root that is not a pointer" is the caller's job. The model resolves an infix root to its closure and greys only white objects.
