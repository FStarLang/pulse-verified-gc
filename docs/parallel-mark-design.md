# Parallel mark: design

Nov 2, 2026

## Summary

Each of k workers runs the ordinary sequential mark on the objects whose header lies in its address range, and hands every pointer into another range to that range's owner. Five rules make this race-free:

1. **Ownership by header.** An object belongs to the range holding its header, `hd_address v = v - 8`. During a round, only its owner reads or writes that header.
2. **Fields are read-only.** During a round no field or infix header is written, so any worker may read them, even across a cut.
3. **Nobody waits on anybody.** A full stack or a full inbox sets the worker's own overflow flag instead of blocking.
4. **A round ends when `work_in_flight` is 0.** Stacks and inboxes are never inspected to decide this.
5. **Anything touching several owners' objects runs between rounds, on one thread:** darkening the roots, repairing overflow, and later ephemeron checks and field writes.

**Status.** Checked by reading only: two passes found two races, both fixed below. The design is not yet modelled or proved; the F\* model, random-interleaving tests and ThreadSanitizer come next.

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
