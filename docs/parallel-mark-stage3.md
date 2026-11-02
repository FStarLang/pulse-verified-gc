# Parallel mark, Stage 3: the design, modelled and proved

Branch `sheera/parallel-mark`. Stage 3 models the design in `docs/parallel-mark-design.md` in F\*, proves its theorems with no `admit`, and tests the extracted model under random interleavings. The Stage 1–2 model, `GC.Spec.MarkPar`, is unchanged and still passes its tests. Stage 2 had left its termination theorem admitted; Stage 3 also proves that (`GC.Spec.MarkPar.Term`), so no module in `parallel-mark/` has an `admit`.

**Status.**

- **The theorems are proved, with no `admit`.** They are listed in §2. Proving found no flaw in the design. Where a statement differs from its Stage 1–2 counterpart, `docs/parallel-mark-design.md` ("Statement changes") says how and why.
- **Every lemma with a precondition is checked for vacuity.** That is 236 lemmas, each called once on arguments that meet its precondition (§4).
- **Tests: no counterexample** in 29,000 runs of the model over 443 heaps, with random stack and inbox capacities. Every run ends with the heap the sequential mark gives, byte for byte, and every per-step check holds (§5).
- **All five broken variants are caught** (§5).

Everything is new, under `parallel-mark/`, apart from the design document. The directory stays out of the root build.

| File | Contents |
|---|---|
| `spec/GC.Spec.MarkPar2.Model.fst` | The model: state, worker step, setup, fix-up, main step, runs; the counter, the readable words, and the termination measure. |
| `spec/GC.Spec.MarkPar2.fst` | The statements (§2). It includes the model. |
| `spec/GC.Spec.MarkPar2.Mutants.fst` | Five broken variants. Used only by the tests. |
| `spec/GC.Spec.MarkPar2.Lists.fst` | Lists of worker records; the object list is sorted by address. |
| `spec/GC.Spec.MarkPar2.Inv.fst` | The invariant (§3). |
| `spec/GC.Spec.MarkPar2.Upd.fst` | Each part of the invariant under one record replaced. |
| `spec/GC.Spec.MarkPar2.Act.fst` | `send`, `grey_push`, `accept`, `route` keep the invariant. |
| `spec/GC.Spec.MarkPar2.Step.fst` | Every worker step keeps it. |
| `spec/GC.Spec.MarkPar2.Fix.fst` | The fix-up walk. |
| `spec/GC.Spec.MarkPar2.Main.fst` | The main thread's step keeps the invariant. |
| `spec/GC.Spec.MarkPar2.Init.fst` | Setup establishes it. |
| `spec/GC.Spec.MarkPar2.End.fst` | Every run keeps it; a finished run is the sequential mark's heap. |
| `spec/GC.Spec.MarkPar2.Count.fst` | `work_in_flight`. |
| `spec/GC.Spec.MarkPar2.Foot.fst` | What a worker step reads and writes; race freedom. |
| `spec/GC.Spec.MarkPar2.Weight.fst`, `.Meas.fst`, `.Term.fst` | Termination. |
| `spec/GC.Spec.MarkPar2.Witness.fst` | A concrete heap with a cycle, meeting `mark_pre`. |
| `spec/GC.Spec.MarkPar2.Runs.fst`, `.RunR1.fst`–`.RunR4.fst` | Concrete runs on it, each state's shape proved. |
| `spec/GC.Spec.MarkPar2.VacBase.fst`, `.VacA.fst`–`.VacD.fst` | The vacuity checks. |
| `spec/GC.Spec.MarkPar.Term.fst`, `spec/GC.Spec.MarkPar.VacuityTerm.fst` | Stage 1's termination, proved (`mark_par_terminates` no longer `admit`), and its vacuity checks. |
| `test/mark_par2_test.ml`, `test/run2.sh`, `test/fast_rt.sh` | The test driver, the runner, and a speed-up of two extracted F\* library modules (§5). |
| `Makefile` | `gmake verify` and `gmake test2`. `gmake test` still runs the Stage 1 tests. |

Toolchain: the pinned `./fstar` (F\* `nightly-2026-10-17`, Z3 5.3.0), with the repo's own flags, and opam switch `fstar-gc` (OCaml 4.14.0) for the tests. Build with `gmake`. `gmake verify` checks Stages 1–3 from a clean cache in about 8 minutes; Stage 3 alone takes about 3 minutes, plus 2 for the vacuity checks.

---

## 1. The model

### State

The heap is cut into `k` ranges by a cut list, as in Stage 1. An object belongs to the range holding its header word (`own k x`). The configuration is `{ cs; cap_s; cap_q }`, which holds the cuts, S and Q. `valid_cfg` asks for valid cuts and `S >= 1`.

Each worker has:

- a stack of at most S objects;
- an inbox of at most Q raw addresses;
- a program counter: `Loop`, `Scan sc` (part-way through an object), `Got v` (has taken v), `Finish` (has yet to subtract) or `Stopped`;
- an overflow flag.

The state also holds the counter `count` (work_in_flight), `ovf_main`, and `finished`.

### Steps

Each worker is a deterministic program, and the event `W i` runs worker i's next step. A step does at most one shared action, plus actions on its own stack, headers and program counter, which no other worker sees. So every interleaving of the real workers is some schedule of these steps. The shared actions are:

- a send, under the target's lock;
- a take, under the worker's own lock;
- one atomic update or read of the counter.

| pc | The step |
|---|---|
| `Loop`, stack not empty | Pop x and blacken it. Go to `Scan` (from field 1), or to `Finish` if x is no-scan or has no fields. |
| `Loop`, stack empty, inbox not empty | Take the oldest entry v: `Got v`. |
| `Loop`, both empty | Read the counter. At 0, go to `Stopped`; otherwise nothing changes. |
| `Scan sc` | Route field `snext` if it is a pointer; move to the next field, or to `Finish`. |
| `Got v` | Accept v, then go to `Finish`. |
| `Finish` | Subtract 1, then go to `Loop`. |

`route`, `accept` and `send` are the design's, word for word. One step reads both the empty inbox and the counter. That is sound because the read can give 0 only when no message exists, and any other outcome leaves the state unchanged.

`Main` is the main thread. It acts only when every worker has stopped, the stop barrier:

- If no flag is set, marking is done.
- Otherwise it clears the flags and walks the objects in address order (fix-up steps 3 and 4).
- If the walk pushed nothing, marking is done.
- Otherwise it sets the counter to the number pushed and restarts every worker (the start barrier).

Setup (`init`) darkens the roots as requirement 6 says.

## 2. The statements (`GC.Spec.MarkPar2`)

All share the precondition `pre k g roots = mark_pre g roots /\ valid_cfg k`.

| Theorem | What it says |
|---|---|
| `mark_par_correct` | If `run k g roots sched` has finished, its heap is `sequential_mark g roots`, over all rounds and fix-ups. |
| `mark_par_reachable` | The same, said with reachability: exactly the reachable objects are black, each with its original header made black, and every other word is unchanged. |
| `step_writes_own` | From any reachable state, worker i's step changes only headers of enumerated objects that i owns. |
| `step_reads_own` | Worker i's step gives the same workers, counter, flags and writes on any heap that agrees on `readable k s i`, which is range i plus the fields of the object i is scanning. |
| `step_race_free` | A word worker j's step writes is never one worker i ≠ j may read, in the same state. |
| `main_at_barrier` | The main thread changes nothing unless every worker has stopped. |
| `count_exact` | In every reachable state, `count` equals the stack entries plus inbox entries plus items held. |
| `zero_final` | From a reachable state with `count = 0`, every worker step leaves it at 0. |
| `mark_par_terminates` | At most `measure (init ...)` effective steps; a step that is not enabled changes nothing; nothing is enabled exactly when marking is done. |

## 3. The proofs

**The invariant** (`Inv.inv`) holds in every reachable state. It has seven parts:

- **Ownership.** Stacks hold grey objects the worker owns, without repeats. Inbox entries, and a taken entry, have their header word in the worker's range. A scanning worker holds a black object it owns.
- **Counter.** It equals the counted entries, and it is 0 whenever any worker has stopped.
- **Greys.** A grey object is on its owner's stack, or some flag is set.
- **Soundness.** Grey and black objects are reachable, and so is every object an entry names.
- **Roots.** Root objects are not white.
- **Black objects.** A pointer field of a black object names an object that is non-white, or pending, or still to be scanned, or some flag is set.
- **End.** Once finished, no flag is set, every worker has stopped, and the count is 0.

At the end, these leave no grey object and no black object pointing to a white one, with the roots black. The rest is Stage 2's argument (`End`, reusing `Recolour`, `Field`, `Roots` and `Seq`).

**The fix-up walk** (`Fix`) keeps track of what it has visited. A visited grey object is on its owner's stack, or `overflow_main` is set. A stack entry has been visited. A visited black object has no white child. The object list is strictly increasing by address (`Lists.objects_above`). So a child below the walk's position has been visited and must be pushed at once, while one above has not, and step 3 pushes it when the walk reaches it. This is the rule from fix-up step 4.

**Footprint** (`Foot`). Every read a step makes goes through `read_word` at the header of an object it owns, or at a field of the object it is scanning. For race freedom, a header another worker owns lies in another range, and objects do not overlap (`Fields.objects_separated`).

**Termination** (`Term`). An object costs:

| Object | Cost |
|---|---|
| white | nr + 3 + 7f |
| grey, on its owner's stack | 2 + 7f |
| grey, off every stack | nr + 3 + 7f |
| black | 0 |

Here f is the number of fields still to scan and nr the number of ranges. A worker costs 1 at `Loop`, 0 at `Stopped`, 2 at `Finish`, 7 per field left plus 2 at `Scan`, and 3 or 6 for `Got v`; an inbox entry costs 3 or 6. Every enabled worker step lowers the total by at least 1. The fix-up raises the workers' part by nr, moving each from `Stopped` to `Loop`. It pushes at least one object that was white or grey and off every stack, which lowers the objects' part by at least nr + 1.

## 4. Vacuity

Every lemma with a precondition (236 of them) is called once on arguments that meet it (`VacA`–`VacD`). If a precondition were contradictory, its call would not verify.

The arguments come from the witness heap `g5`: the Stage 1 witness with B's field pointing back to A. So A has fields [B; 0] and B has [A], and every later word is zero. They also come from five concrete runs on it. Each state is the previous one stepped, so the invariant holds by `init_inv` and `step_inv`, and only each state's shape is worked out by hand.

| Run | Setting | What it covers |
|---|---|---|
| R0 | One range, no roots | Stops and finishes at once; A is unreachable. |
| R1 | One range, S = 1, roots A and B | Setup fills the stack (`overflow_main`). The fix-up pushes the grey B and a second round runs. It finishes, so it is the witness for `mark_par_correct`. |
| R2 | Two ranges (cut at B's header), Q = 1 | A message is sent, taken and accepted (greyed and pushed), a second is accepted with nothing to do, and it finishes. |
| R3 | Two ranges, Q = 0 | A dropped message; the fix-up greys B above the walk's position without pushing it, then pushes it on reaching it; a second fix-up finds nothing and finishes. |
| R4 | Two ranges, Q = 0, root B | The fix-up passes the white A, then greys and pushes it from B, below the walk's position. |

One proof lemma's precondition was relaxed for this, with no theorem affected (design document, "Statement changes").

## 5. Tests

`gmake test2` verifies, extracts the model with Custard, builds `test/mark_par2_test.ml` and runs `test/run2.sh`. It uses the same heap generator as Stage 1, plus four hand cases aimed at overflow. Each run draws S from {1, 2, 3, 1000} and Q from {0, 1, 2, 4, 1000}, and uses one of four schedulers: uniform, one worker in focus, round robin, or one slow worker.

At every step of the model the test checks:

- **writes:** every changed word is the header of an enumerated object the acting worker owns, and `Main` runs only when every worker has stopped;
- **reads:** the step gives the same result on a heap where every word it may not read is scrambled (random, infix-looking headers, or zeros);
- **counter:** `count` equals the counted entries, and a worker step from 0 leaves it 0;
- **measure:** an enabled step lowers it, a step that is not enabled changes nothing, and nothing is enabled exactly when marking is done.

The run must end with the sequential mark's heap, and replaying its schedule through `run` must give the same.

| Totals | |
|---|---|
| Runs | 443 heaps, 4,470 cut lists, 29,000 model runs, 727,388 events |
| Paths taken | 44,880 sends, 8,709 dropped, 1,368 greys left off a full stack, 4,777 setups that filled a stack, 4,803 forwards (closures sent on) |
| Rounds | 12,992 fix-ups started a round; up to 24 rounds in one run |

Across all runs, 1,527,978 read checks ran, and 490,584 worker steps were taken with the counter at 0.

| Broken variant | Caught | How |
|---|---|---|
| 1. `overflow_main` never read | 1,726 of 10,460 | wrong final heap |
| 2. infix root greyed in place | 1,590 of 10,460 | wrong final heap, and a write outside owned headers |
| 3. sender resolves the child | 2,690 of 10,460 | the read check alone: it reads another owner's header word, and the colours stay right |
| 4. drop without the flag | 513 of 10,460 | wrong final heap |
| 5. subtract before adding | 9,830 of 10,460 | the counter check; 1,484 of those runs also stuck, with nothing enabled before the end |

`test/fast_rt.sh` rewrites two extracted F\* library modules for the test build only. These are `FStar.Seq`'s `index` and `upd`, and `FStar.UInt`'s bit operations. The originals work on arbitrary-precision bit vectors; the rewrites use native arithmetic and compute the same values. The test compares the two on random inputs before it starts. It makes the test about 9 times faster.
