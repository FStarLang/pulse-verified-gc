/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.ParMark.Model - the parallel mark (BP), as atomic steps of k workers
/// ---------------------------------------------------------------------------
///
/// docs/pages-parallel-gc-design.md §1, stage M1.  The mark of the P0
/// prototype (`par_mark_pages.c`, BP with the §1.3 fixes, step 2) as a state
/// machine: `wstep p s w` is one atomic step of worker `w`; a run is any
/// interleaving of them.  Each step does at most one access to shared memory
/// (or, inside the pool lock, one access plus lock-protected pool updates),
/// and the comment on each case names the operation it is:
///
///   - bitmap:  LOAD-BM   an atomic load of one bitmap word
///              CAS-BM    a 32-bit CAS on one bitmap word (`cas_cell`)
///   - words:   LOAD-W    an atomic load (only ever a test against 0)
///              CAS-W     a CAS on one word (`cas_word`)
///              FAA-W     fetch-and-add, a verified loop over CAS-W; it takes
///                        effect at its successful CAS
///              ACQ       one try of the spin lock: CAS-W lock 0 -> 1
///              REL       the spin lock's release: CAS-W lock 1 -> 0
///   - LOCAL    no shared access (worker-owned packets, the read-only heap).
///
/// The heap is read only: the model sees it through `params`: `tst a` is the
/// address whose bit the bitmap-first test reads for the word at `a` (if the
/// word is a heap pointer), `tgt a` the object a visit of that word claims
/// (after resolving infix pointers and skipping blue targets), and `nf y` the
/// number of fields pushed for a claimed object `y` (0 if no-scan).
/// `GC.Spec.Pages.ParMark.Heap` instantiates them from a heap.
///
/// What is left out, because it has no logical effect: the empty-packet
/// free list and `malloc` (packet memory), `idle_workers` (read only by
/// fix 0), back-off and `sched_yield`, statistics.  Two choices differ from
/// the prototype, for the model's determinism, and the Pulse code follows
/// the model: an idle worker tests `share_wanted` on every round (the
/// prototype every 64th), and `tick` also counts the first entry after a take.

module GC.Spec.Pages.ParMark.Model

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Bitmap
open GC.Spec.Pages.ParMark.Bits

module U32 = FStar.UInt32
module Seq = FStar.Seq
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Parameters
/// ---------------------------------------------------------------------------

noeq type params = {
  k: pos;                   (* workers *)
  pkt: pos;                 (* entries per packet (PKT) *)
  chunk: pos;               (* fields scanned before the rest is pushed back (CHUNK) *)
  maxlen: pos;              (* fields per entry (MAXLEN) *)
  smin: nat;                (* entries a worker must hold to share (S_min) *)
  tickp: pos;               (* entries between share checks *)
  nf: nat -> nat;           (* fields pushed for a claimed object *)
  tst: nat -> option nat;   (* the bitmap-first test's address for the word at a *)
  tgt: nat -> option nat;   (* the object a visit of the word at a claims *)
}

/// ---------------------------------------------------------------------------
/// State
/// ---------------------------------------------------------------------------

/// A mark entry: `el` words from address `es` (one field range).
type entry = { es: nat; el: nat }

let no_entry : entry = { es = 0; el = 0 }

/// The claim in progress for a visited word's target `y`.
type claim =
  | CNone
  | CLoad of nat               (* load the word of `y`'s bit *)
  | CCas of nat & U32.t        (* CAS it from the value read *)

type pc =
  | Run                        (* busy: scan, push, pop *)
  | Sh1 | Sh2 | Sh3            (* maybe_share: nfull, share_wanted, CAS share_wanted *)
  | Lk                         (* waiting for the pool lock, to publish `pub` *)
  | Cs1 | Cs2 | Cs3            (* publishing: count, pool, release *)
  | Id1 | Id2 | Id3 | Id4 | Id5  (* idle: nfull, try lock, share_wanted, set it, count *)
  | Tk1 | Tk2                  (* taking, under the lock: pop the pool, release *)
  | Done

noeq type wst = {
  pc: pc;
  inp: list entry;             (* the input packet; head = top *)
  out: list entry;             (* the output packet *)
  pend: list entry;            (* entries still to push to `out` *)
  pub: list entry;             (* the packet being published *)
  got: option (list entry);    (* the packet taken from the pool *)
  scan: entry;                 (* the fields still to visit of the entry being scanned *)
  vis: claim;
  active: bool;                (* holds one unit of the work count *)
  tick: nat;
  chk: bool;                   (* check for a share request before the next pop *)
}

noeq type mstate = {
  bs: Seq.seq U32.t;           (* the bitmap *)
  cnt: nat;                    (* work_in_flight *)
  flag: bool;                  (* share_wanted *)
  lk: bool;                    (* the pool lock *)
  pool: list (list entry);     (* the full packets (lock-protected) *)
  nfull: nat;                  (* their number, read without the lock *)
  ws: Seq.seq wst;             (* the workers *)
}

let idle_w : wst = {
  pc = Id1; inp = []; out = []; pend = []; pub = []; got = None; scan = no_entry;
  vis = CNone; active = false; tick = 0; chk = false
}

/// ---------------------------------------------------------------------------
/// Local computations
/// ---------------------------------------------------------------------------

/// The entries pushed for an object at `a` with `n` fields left: ranges of at
/// most `maxlen` fields, in address order (push_obj).
let rec push_obj (ml: pos) (a: nat) (n: nat) : Tot (list entry) (decreases n) =
  if n = 0 then []
  else if n <= ml then [{ es = a; el = n }]
  else { es = a; el = ml } :: push_obj ml (a + 8 * ml) (n - ml)

/// The entries pushed for a claimed object `y`.
let obj_entries (p: params) (y: nat) : list entry = push_obj p.maxlen y (p.nf y)

/// The rest of the entry after the first `c` words.
let rest_of (e: entry) (c: nat{c <= e.el}) : entry = { es = e.es + 8 * c; el = e.el - c }

/// The word after the first is visited.
let advance (e: entry{e.el > 0}) : entry = rest_of e 1

/// Sharing takes the older half (`h` entries from the bottom) of the larger
/// packet.
let share_src_inp (x: wst) : bool = L.length x.inp >= L.length x.out
let share_src (x: wst) : list entry = if share_src_inp x then x.inp else x.out

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

let upd (s: mstate) (w: nat{w < Seq.length s.ws}) (x: wst) : mstate =
  { s with ws = Seq.upd s.ws w x }

/// The claim of `y`: the bitmap word of its header's bit.
let ybit (y: nat) : nat = if y >= 8 then y - 8 else 0

/// A busy worker's step.
let run_step (p: params) (s: mstate) (w: nat{w < Seq.length s.ws}) (x: wst) : mstate =
  match x.vis with
  | CLoad y ->
    (* LOAD-BM: the word of y's bit *)
    if marked s.bs (ybit y) then upd s w { x with vis = CNone }
    else upd s w { x with vis = CCas (y, bword s.bs (ybit y)) }
  | CCas (y, old) ->
    (* CAS-BM: old -> old | bit *)
    if in_pages (ybit y) && Seq.length s.bs = bm_len && bword s.bs (ybit y) = old then
      upd ({ s with bs = set_bit s.bs (ybit y) }) w
          { x with vis = CNone; pend = obj_entries p y }
    else upd s w { x with vis = CLoad y }
  | CNone ->
    if Cons? x.pend then begin
      if L.length x.out < p.pkt then
        (* LOCAL: push the next pending entry *)
        upd s w { x with out = L.hd x.pend :: x.out; pend = L.tl x.pend }
      else
        (* LOCAL: the output packet is full; publish it *)
        upd s w { x with pub = x.out; out = []; pc = Lk }
    end
    else if x.scan.el > 0 then begin
      (* visit the word at x.scan.es *)
      let a = x.scan.es in
      let x' = { x with scan = advance x.scan } in
      match p.tst a with
      | None -> upd s w x'                                 (* LOCAL: not a pointer *)
      | Some t ->
        (* LOAD-BM if t is in the pages, else LOCAL *)
        if marked s.bs t then upd s w x'
        else (match p.tgt a with
              | None -> upd s w x'
              | Some y -> upd s w { x' with vis = CLoad y })
    end
    else if x.chk then
      (* LOCAL: time to check for a share request *)
      upd s w { x with chk = false; pc = Sh1 }
    else if Nil? x.inp && Nil? x.out then
      (* FAA-W cnt -1: no work left; give up the count *)
      upd ({ s with cnt = (if s.cnt > 0 then s.cnt - 1 else 0) }) w
          { x with active = false; pc = Id1 }
    else if Nil? x.inp then
      (* LOCAL: swap the packets *)
      upd s w { x with inp = x.out; out = x.inp }
    else begin
      (* LOCAL: pop an entry; push back all but the first `chunk` fields *)
      let e = L.hd x.inp in
      let x1 = { x with inp = L.tl x.inp; tick = x.tick + 1; chk = ((x.tick + 1) % p.tickp = 0) } in
      if e.el > p.chunk then
        upd s w { x1 with scan = { es = e.es; el = p.chunk }; pend = [rest_of e p.chunk] }
      else upd s w { x1 with scan = e }
    end

/// The share: the older half of the larger packet, to be published.
let share_step (s: mstate) (w: nat{w < Seq.length s.ws}) (x: wst) : mstate =
  let src = share_src x in
  let h = L.length src / 2 in
  if h = 0 then upd ({ s with flag = false }) w { x with pc = Run }
  else begin
    let (keep, give) = L.splitAt (L.length src - h) src in
    let x' = if share_src_inp x then { x with inp = keep } else { x with out = keep } in
    upd ({ s with flag = false }) w { x' with pub = give; pc = Lk }
  end

let wstep (p: params) (s: mstate) (w: nat{w < Seq.length s.ws}) : mstate =
  let x = Seq.index s.ws w in
  match x.pc with
  | Run -> run_step p s w x
  | Sh1 ->
    (* LOAD-W nfull: share only when the pool is empty *)
    if s.nfull <> 0 then upd s w { x with pc = Run } else upd s w { x with pc = Sh2 }
  | Sh2 ->
    (* LOAD-W share_wanted *)
    if not s.flag || L.length (share_src x) < p.smin then upd s w { x with pc = Run }
    else upd s w { x with pc = Sh3 }
  | Sh3 ->
    (* CAS-W share_wanted 1 -> 0; on success, share *)
    if s.flag then share_step s w x else upd s w { x with pc = Run }
  | Lk ->
    (* ACQ; on failure the state is unchanged *)
    if s.lk then s else upd ({ s with lk = true }) w { x with pc = Cs1 }
  | Cs1 ->
    (* FAA-W cnt +1, under the lock *)
    upd ({ s with cnt = s.cnt + 1 }) w { x with pc = Cs2 }
  | Cs2 ->
    (* pool push (lock-protected) and FAA-W nfull +1 *)
    upd ({ s with pool = x.pub :: s.pool; nfull = s.nfull + 1 }) w { x with pub = []; pc = Cs3 }
  | Cs3 ->
    (* REL *)
    upd ({ s with lk = false }) w { x with pc = Run }
  | Id1 ->
    (* LOAD-W nfull *)
    if s.nfull > 0 then upd s w { x with pc = Id2 } else upd s w { x with pc = Id3 }
  | Id2 ->
    (* ACQ, one try *)
    if s.lk then upd s w { x with pc = Id5 } else upd ({ s with lk = true }) w { x with pc = Tk1 }
  | Tk1 ->
    (* pool pop (lock-protected) and FAA-W nfull -1 *)
    (match s.pool with
     | [] -> upd s w { x with got = None; pc = Tk2 }
     | q :: rest ->
       upd ({ s with pool = rest; nfull = (if s.nfull > 0 then s.nfull - 1 else 0) }) w
           { x with got = Some q; pc = Tk2 })
  | Tk2 ->
    (* REL; the taken packet's count passes to the taker *)
    (match x.got with
     | Some q -> upd ({ s with lk = false }) w
                     { x with inp = q; got = None; active = true; chk = false; pc = Run }
     | None -> upd ({ s with lk = false }) w { x with pc = Id5 })
  | Id3 ->
    (* LOAD-W share_wanted *)
    if s.flag then upd s w { x with pc = Id5 } else upd s w { x with pc = Id4 }
  | Id4 ->
    (* CAS-W share_wanted 0 -> 1 *)
    upd ({ s with flag = true }) w { x with pc = Id5 }
  | Id5 ->
    (* LOAD-W cnt: 0 is final *)
    if s.cnt = 0 then upd s w { x with pc = Done } else upd s w { x with pc = Id1 }
  | Done -> s

/// ---------------------------------------------------------------------------
/// The start: the roots claimed and packed by the main thread
/// ---------------------------------------------------------------------------

/// Claim each root target in turn (sequential, before the workers start:
/// plain writes, or CAS-BM as the prototype does), collecting the entries
/// of those newly claimed.
let rec claim_roots (p: params) (bs: Seq.seq U32.t) (rts: list nat)
  : Tot (Seq.seq U32.t & list entry) (decreases rts) =
  match rts with
  | [] -> (bs, [])
  | y :: rest ->
    if marked bs (ybit y) then claim_roots p bs rest
    else begin
      let (bs', es) = claim_roots p (set_bit bs (ybit y)) rest in
      (bs', L.append (obj_entries p y) es)
    end

/// Pack entries into packets of `pkt`, each full packet put in front of the
/// pool, then the last partial one (`cur`, head = last added).
let rec pack (pkt: pos) (cur: list entry) (pool: list (list entry)) (es: list entry)
  : Tot (list (list entry)) (decreases es) =
  match es with
  | [] -> if Nil? cur then pool else cur :: pool
  | e :: rest ->
    let cur' = e :: cur in
    if L.length cur' = pkt then pack pkt [] (cur' :: pool) rest
    else pack pkt cur' pool rest

/// The state the workers start from, with `bs0` the bitmap (all zero) and
/// `rts` the roots' targets.
let init (p: params) (bs0: Seq.seq U32.t) (rts: list nat) : mstate =
  let (bs, es) = claim_roots p bs0 rts in
  let pool = pack p.pkt [] [] es in
  { bs = bs; cnt = L.length pool; flag = false; lk = false; pool = pool;
    nfull = L.length pool; ws = Seq.create p.k idle_w }

/// ---------------------------------------------------------------------------
/// Runs
/// ---------------------------------------------------------------------------

/// The state after the workers of `sched` have stepped, in order.
let rec run (p: params) (s: mstate) (sched: list nat) : Tot mstate (decreases sched) =
  match sched with
  | [] -> s
  | w :: rest -> if w < Seq.length s.ws then run p (wstep p s w) rest else run p s rest

let all_done (s: mstate) : prop =
  forall (w: nat). w < Seq.length s.ws ==> (Seq.index s.ws w).pc == Done
