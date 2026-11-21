/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Toy - a toy allocator and sweep meeting the contracts
/// ---------------------------------------------------------------------------
///
/// Satisfiability of the allocator and sweep contracts of GC.Spec.Top.Iface.
///
/// The allocator is a bump allocator: below the cursor `cur` the heap is
/// objects and dead blocks; from `cur` to the end it is one free block (the
/// tail).  A block is free when it is at or above `cur`, or dead (freed by
/// the sweep; the bump allocator never reuses it).
///
/// The sweep visits the blocks below the cursor taken at the hand-over,
/// `e`, from address 0 upwards; its progress is `(p, e)`, and an address is
/// unswept when `p <= o < e`.  Objects allocated during the sweep lie at or
/// above `e`, so they are swept memory and white, as the colour rule says.
///
/// Proved: `toy_allocator_ok`, `toy_nontrivial`, `toy_room_capacity` (room
/// holds exactly when the tail has `sz + 1` words), `toy_sweep_ok`.

module GC.Spec.Top.Toy

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.IdRep
open GC.Spec.Top.ToyRep
module L = FStar.List.Tot
module Seq = FStar.Seq

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

noeq type tstate = { cur: nat; dead: nat -> bool }

let tprog = nat & nat
let tunswept (pe: tprog) (o: nat) : bool = fst pe <= o && o < snd pe

let tk : sweep_kind = { progress = tprog; unswept = tunswept }

let tfree (st: tstate) (h: mheap) (o: nat) : bool = o >= st.cur || st.dead o

/// The tail: one free block from `cur` to the end.
let tail_ok (h: mheap) (cur: nat) : prop =
  cur <= h.size /\ (cur < h.size ==> is_block h cur /\ cur + wz_of h cur + 1 == h.size)

/// The invariant: the heap is tiled with the tail at `cur` (`tglob`), and
/// per block (`tlocal`): dead blocks lie below `cur`, free blocks are white,
/// and the phase's colours hold.
let tglob (ph: phase tprog) (h: mheap) (st: tstate) : prop =
  match ph with
  | Sweeping pe ->
    fst pe <= snd pe /\ snd pe <= st.cur /\
    (fst pe < snd pe ==> is_block h (fst pe)) /\
    (snd pe < h.size ==> is_block h (snd pe))
  | _ -> True

let tlocal (ph: phase tprog) (h: mheap) (st: tstate) (o: nat) : prop =
  (st.dead o ==> is_block h o /\ o < st.cur) /\
  (is_block h o /\ tfree st h o ==> col_of h o == White) /\
  (is_block h o ==> col_of h o <> Blue) /\
  (match ph with
   | Idle -> (is_block h o ==> col_of h o == White)
   | Marking -> True
   | Sweeping pe ->
     (is_block h o /\ not (tfree st h o) /\ o < fst pe ==> col_of h o == White) /\
     (is_block h o /\ not (tfree st h o) /\ o >= snd pe ==> col_of h o == White))

[@@"opaque_to_smt"]
let tinv (ph: phase tprog) (h: mheap) (st: tstate) : prop =
  tiled h /\ tail_ok h st.cur /\ tglob ph h st /\ (forall (o: nat). tlocal ph h st o)

let tinv_elim (ph: phase tprog) (h: mheap) (st: tstate) (o: nat)
  : Lemma (requires tinv ph h st)
          (ensures tiled h /\ tail_ok h st.cur /\ tglob ph h st /\ tlocal ph h st o)
  = reveal_opaque (`%tinv) (tinv ph h st)

let tinv_elim_all (ph: phase tprog) (h: mheap) (st: tstate)
  : Lemma (requires tinv ph h st)
          (ensures tiled h /\ tail_ok h st.cur /\ tglob ph h st /\ (forall (o: nat). tlocal ph h st o))
  = reveal_opaque (`%tinv) (tinv ph h st)

let tinv_intro (ph: phase tprog) (h: mheap) (st: tstate)
  : Lemma (requires tiled h /\ tail_ok h st.cur /\ tglob ph h st /\ (forall (o: nat). tlocal ph h st o))
          (ensures tinv ph h st)
  = reveal_opaque (`%tinv) (tinv ph h st)

let troom (ph: phase tprog) (st: tstate) (h: mheap) (sz: size_t) : GTot bool =
  st.cur + sz + 1 <= h.size

let talloc_heap (ph: phase tprog) (h: mheap) (cur: nat) (sz: size_t) (tag: tag_t) : mheap =
  let r = cur + sz + 1 in
  { h with hd = (fun (x: nat) ->
      if x = cur then Some ({ wz = sz; tag = tag; col = colour_at tk ph cur })
      else if x = r && r < h.size then Some ({ wz = h.size - r - 1; tag = 0; col = White })
      else h.hd x) }

let talloc (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
  : GTot (mheap & tstate & result) =
  if st.cur + sz + 1 <= h.size then
    (talloc_heap ph h st.cur sz tag, { st with cur = st.cur + sz + 1 }, Ok st.cur)
  else (h, st, NoRoom)

let tinit_heap (n: nat) : mheap =
  { size = n;
    hd = (fun (x: nat) -> if x = 0 && n > 0 then Some ({ wz = n - 1; tag = 0; col = White }) else None);
    body = (fun _ -> VInt 0) }

let tinit (n: nat) : GTot (mheap & tstate) =
  (tinit_heap n, { cur = 0; dead = (fun _ -> false) })

let toy : allocator mheap tk = {
  state = tstate;
  init = tinit;
  inv = tinv;
  free = tfree;
  room = troom;
  alloc = talloc;
}

/// ---------------------------------------------------------------------------
/// Tiling facts
/// ---------------------------------------------------------------------------

/// Below a tail at `cur`, every block ends before `cur`, and no block starts
/// strictly inside the tail.
let tail_facts (h: mheap) (cur: nat)
  : Lemma (requires tiled h /\ tail_ok h cur)
          (ensures (forall (x: nat). is_block h x /\ x <> cur ==> x + wz_of h x < cur) /\
                   (forall (x: nat). is_block h x ==> x <= cur))
  = let aux (x: nat) : Lemma (is_block h x /\ x <> cur ==> x + wz_of h x < cur /\ x <= cur)
      = if is_block h x && x <> cur then begin
          if x + wz_of h x >= cur then begin
            if x < cur then begin
              assert (covers h x cur);
              assert (cur < h.size);
              assert (covers h cur cur)
            end else begin
              assert (covers h x x);
              assert (cur < h.size);
              assert (covers h cur x)
            end
          end
        end
    in
    FStar.Classical.forall_intro aux

/// The block covering `w` starts at `w` when `w` is just past a block.
let next_block (h: mheap) (p: nat)
  : Lemma (requires tiled h /\ is_block h p /\ p + wz_of h p + 1 < h.size)
          (ensures is_block h (p + wz_of h p + 1))
  = let q = p + wz_of h p + 1 in
    assert (exists (b: nat). covers h b q);
    let aux (b: nat) : Lemma (covers h b q ==> b == q)
      = if covers h b q && b <> q then begin
          assert (covers h b q);
          assert (is_block h b /\ b <= q /\ q <= b + wz_of h b);
          assert (b < q /\ q - 1 <= b + wz_of h b);
          assert (covers h b (q - 1));
          assert (covers h p (q - 1))
        end
    in
    FStar.Classical.forall_intro aux

let tiled_intro (h: mheap)
  : Lemma (requires (forall (o: nat). is_block h o ==> o + wz_of h o < h.size /\ tag_of h o <> infix_tag) /\
                    (forall (w: nat). w < h.size ==> (exists (o: nat). covers h o w)) /\
                    (forall (o1 o2 w: nat). covers h o1 w /\ covers h o2 w ==> o1 == o2))
          (ensures well_formed h)
  = ()

/// Tiling reads the headers only.
let tiled_hd (h h': mheap)
  : Lemma (requires tiled h /\ h'.size == h.size /\
                    (forall (x: nat). is_block h' x == is_block h x /\ wz_of h' x == wz_of h x))
          (ensures tiled h')
  = let c (x w: nat) : Lemma (covers h' x w == covers h x w) = () in
    FStar.Classical.forall_intro_2 c;
    let b (o: nat) : Lemma (is_block h' o ==> o + wz_of h' o < h'.size) = () in
    FStar.Classical.forall_intro b;
    let e (w: nat) : Lemma (w < h'.size ==> (exists (o: nat). covers h' o w))
      = if w < h'.size then begin
          assert (exists (o: nat). covers h o w);
          let o = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o -> covers h o w) in
          assert (covers h' o w)
        end in
    FStar.Classical.forall_intro e;
    let u (o1 o2 w: nat) : Lemma (covers h' o1 w /\ covers h' o2 w ==> o1 == o2)
      = assert (covers h' o1 w == covers h o1 w); assert (covers h' o2 w == covers h o2 w) in
    FStar.Classical.forall_intro_3 u

let first_block (h: mheap)
  : Lemma (requires tiled h /\ 0 < h.size) (ensures is_block h 0)
  = assert (exists (b: nat). covers h b 0)

/// ---------------------------------------------------------------------------
/// The allocator meets its contract
/// ---------------------------------------------------------------------------

let talloc_tiled (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
  : Lemma (requires tail_ok h st.cur /\ well_formed h /\ tag <> infix_tag /\ st.cur + sz + 1 <= h.size)
          (ensures well_formed (talloc_heap ph h st.cur sz tag))
  = let cur = st.cur in
    let r = cur + sz + 1 in
    let h' = talloc_heap ph h cur sz tag in
    tail_facts h cur;
    let blk (x: nat) : Lemma (is_block h' x <==> (x = cur \/ (x = r /\ r < h.size) \/ (is_block h x /\ x < cur)))
      = () in
    FStar.Classical.forall_intro blk;
    let cov (w: nat) : Lemma (w < h.size ==> (exists (o: nat). covers h' o w))
      = if w < h.size then begin
          if w < cur then begin
            assert (exists (b: nat). covers h b w);
            let b = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun b -> covers h b w) in
            assert (covers h' b w)
          end else if w < r then assert (covers h' cur w)
          else assert (covers h' r w)
        end in
    FStar.Classical.forall_intro cov;
    let uniq (o1 o2 w: nat) : Lemma (covers h' o1 w /\ covers h' o2 w ==> o1 == o2)
      = if covers h' o1 w && covers h' o2 w then begin
          if o1 < cur && o2 < cur then assert (covers h o1 w /\ covers h o2 w)
        end in
    FStar.Classical.forall_intro_3 uniq;
    let bnd (x: nat) : Lemma (is_block h' x ==> x + wz_of h' x < h'.size /\ tag_of h' x <> infix_tag)
      = if is_block h' x then begin
          if x = cur then () else if x = r then () else assert (is_block h x)
        end in
    FStar.Classical.forall_intro bnd;
    tiled_intro h'

let tail_x (h: mheap) (cur: nat) (x: nat)
  : Lemma (requires tiled h /\ tail_ok h cur /\ is_block h x /\ x <> cur)
          (ensures x + wz_of h x < cur)
  = if x + wz_of h x >= cur then begin
      if x < cur then begin
        assert (covers h x cur);
        assert (covers h cur cur)
      end else begin
        assert (covers h x x);
        assert (covers h cur x)
      end
    end

let talloc_heap_hd (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t) (x: nat)
  : Lemma (requires tiled h /\ tail_ok h st.cur /\ st.cur + sz + 1 <= h.size)
          (ensures (let cur = st.cur in
                    let r = cur + sz + 1 in
                    let h0 = talloc_heap ph h cur sz tag in
                    is_block h0 x == (x = cur || (x = r && r < h.size) || (is_block h x && x < cur)) /\
                    (is_block h x && x < cur ==> hdr_of h0 x == hdr_of h x) /\
                    (x = cur ==> col_of h0 x == colour_at tk ph cur /\ wz_of h0 x == sz) /\
                    (x = r /\ r < h.size ==> col_of h0 x == White /\ wz_of h0 x == h.size - r - 1)))
  = let cur = st.cur in
    let r = cur + sz + 1 in
    if x = cur then ()
    else if x = r then (if is_block h x then tail_x h cur x)
    else if is_block h x then tail_x h cur x
    else ()

/// The invariant reads the headers only.
let tinv_hd (ph: phase tprog) (h h': mheap) (st: tstate)
  : Lemma (requires tinv ph h st /\ h'.size == h.size /\ h'.hd == h.hd)
          (ensures tinv ph h' st)
  = tinv_elim_all ph h st;
    assert (forall (x: nat). is_block h' x == is_block h x /\ hdr_of h' x == hdr_of h x);
    tiled_hd h h';
    let l (o: nat) : Lemma (tlocal ph h' st o) = assert (tlocal ph h st o) in
    FStar.Classical.forall_intro l;
    tinv_intro ph h' st

let talloc_local (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t) (o: nat)
  : Lemma (requires tiled h /\ tail_ok h st.cur /\ tglob ph h st /\ tlocal ph h st o /\
                    st.cur + sz + 1 <= h.size)
          (ensures tlocal ph (talloc_heap ph h st.cur sz tag) ({ st with cur = st.cur + sz + 1 }) o)
  = talloc_heap_hd ph h st sz tag o;
    if is_block h o && o <> st.cur then tail_x h st.cur o

let talloc_rem (ph: phase tprog) (h: mheap) (cur: nat) (sz: size_t) (tag: tag_t)
  : Lemma (requires cur + sz + 1 < h.size)
          (ensures (let r = cur + sz + 1 in
                    let h0 = talloc_heap ph h cur sz tag in
                    is_block h0 r /\ r + wz_of h0 r + 1 == h0.size))
  = ()

let talloc_tail (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
  : Lemma (requires st.cur + sz + 1 <= h.size)
          (ensures tail_ok (talloc_heap ph h st.cur sz tag) (st.cur + sz + 1))
  = if st.cur + sz + 1 < h.size then talloc_rem ph h st.cur sz tag

let talloc_inv0 (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
  : Lemma (requires tinv ph h st /\ well_formed h /\ tag <> infix_tag /\ st.cur + sz + 1 <= h.size)
          (ensures tinv ph (talloc_heap ph h st.cur sz tag) ({ st with cur = st.cur + sz + 1 }))
  = let cur = st.cur in
    let r = cur + sz + 1 in
    let h0 = talloc_heap ph h cur sz tag in
    let st' = { st with cur = r } in
    tinv_elim ph h st cur;
    talloc_tiled ph h st sz tag;
    talloc_tail ph h st sz tag;
    (match ph with
     | Sweeping pe ->
       talloc_heap_hd ph h st sz tag (fst pe);
       talloc_heap_hd ph h st sz tag (snd pe);
       assert (tglob ph h0 st')
     | _ -> ());
    let l (o: nat) : Lemma (tlocal ph h0 st' o) = tinv_elim ph h st o; talloc_local ph h st sz tag o in
    FStar.Classical.forall_intro l;
    tinv_intro ph h0 st'

let talloc_inv (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires tinv ph h st /\ well_formed h /\ tag <> infix_tag /\ st.cur + sz + 1 <= h.size)
          (ensures tinv ph (fill (talloc_heap ph h st.cur sz tag) st.cur vs) ({ st with cur = st.cur + sz + 1 }))
  = talloc_inv0 ph h st sz tag;
    let h0 = talloc_heap ph h st.cur sz tag in
    tinv_hd ph h0 (fill h0 st.cur vs) ({ st with cur = st.cur + sz + 1 })

let talloc_use (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t) (x: nat)
  : Lemma (requires tinv ph h st /\ st.cur + sz + 1 <= h.size)
          (ensures in_use toy ({ st with cur = st.cur + sz + 1 }) (talloc_heap ph h st.cur sz tag) (talloc_heap ph h st.cur sz tag) x <==>
                   (in_use toy st h h x \/ x == st.cur))
  = tinv_elim ph h st x;
    tinv_elim ph h st st.cur;
    talloc_heap_hd ph h st sz tag x;
    if is_block h x && x <> st.cur then tail_x h st.cur x

let talloc_ok_m (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
  : Lemma (alloc_pre toy ph h st tag h ==>
           (let (h', st', r) = toy.alloc ph h st sz tag in alloc_post toy_rep toy ph h st sz tag h' st' r h h'))
  = if st.cur + sz + 1 <= h.size then begin
      let introduce_pre () : Lemma (requires toy.inv ph h st /\ well_formed h /\ tag <> infix_tag)
                                   (ensures (let (h', st', r) = toy.alloc ph h st sz tag in
                                             alloc_post toy_rep toy ph h st sz tag h' st' r h h'))
        = let cur = st.cur in
          let r = cur + sz + 1 in
          let h' = talloc_heap ph h cur sz tag in
          let st' = { st with cur = r } in
          tinv_elim ph h st cur;
          talloc_tiled ph h st sz tag;
          let words (w: nat) : Lemma (covers h' cur w ==> free_word toy st h h w)
            = if covers h' cur w then assert (covers h cur w) in
          FStar.Classical.forall_intro words;
          FStar.Classical.forall_intro (talloc_use ph h st sz tag);
          let same (x: nat) : Lemma (in_use toy st h h x ==> same_block h h' x)
            = talloc_heap_hd ph h st sz tag x;
              if is_block h x && x <> cur then tail_x h cur x in
          FStar.Classical.forall_intro same;
          let fill_inv (vs: list value) (h'': mheap)
            : Lemma (L.length vs == sz /\ toy_rep.repr (fill h' cur vs) h'' ==> toy.inv ph h'' st')
            = talloc_inv ph h st sz tag vs in
          FStar.Classical.forall_intro_2 fill_inv
      in
      FStar.Classical.move_requires introduce_pre ()
    end

let talloc_ok (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
  : Lemma (alloc_at toy_rep toy ph h st sz tag)
  = talloc_ok_m ph h st sz tag;
    toy_rep_id ();
    let (h', st', r) = toy.alloc ph h st sz tag in
    lifted_id toy_rep (alloc_pre toy ph h st tag) h h' (alloc_post toy_rep toy ph h st sz tag h' st' r)

let tinit_ok (n: nat) : Lemma (init_at toy_rep toy n)
  = toy_rep_id ();
    let h = tinit_heap n in
    let st = { cur = 0; dead = (fun (_: nat) -> false) } in
    let cov (w: nat) : Lemma (w < n ==> covers h 0 w) = () in
    FStar.Classical.forall_intro cov;
    assert (tiled h);
    let l (o: nat) : Lemma (tlocal Idle h st o) = () in
    FStar.Classical.forall_intro l;
    tinv_intro Idle h st;
    some_repr_id toy_rep h (init_post toy n h st)

let tframe_m (ph: phase tprog) (h: mheap) (st: tstate) (h': mheap)
  : Lemma (inv_frame_m toy ph h st h' h h')
  = let pre () : Lemma (requires toy.inv ph h st /\ inv_frame_rel toy ph st h h h')
                       (ensures toy.inv ph h' st)
      = tinv_elim_all ph h st;
        tiled_hd h h';
        let l (o: nat) : Lemma (tlocal ph h' st o)
          = assert (tlocal ph h st o);
            if col_of h' o = col_of h o then ()
            else assert (in_use toy st h h o /\ Marking? ph /\ dark (col_of h' o)) in
        FStar.Classical.forall_intro l;
        tinv_intro ph h' st
    in
    FStar.Classical.move_requires pre ()

let tframe_ok (ph: phase tprog) (h: mheap) (st: tstate) (h': mheap)
  : Lemma (inv_frame_at toy_rep toy ph h st h')
  = tframe_m ph h st h';
    toy_rep_id ();
    forall_repr2_id toy_rep h h' (inv_frame_m toy ph h st h')

let toy_free_white_o (ph: phase tprog) (h: mheap) (st: tstate) (o: nat)
  : Lemma (requires tinv ph h st)
          (ensures is_block h o ==>
                   (tfree st h o == true ==> not (dark (col_of h o))) /\
                   (col_of h o == Blue ==> tfree st h o == true))
  = tinv_elim ph h st o;
    assert (dark White == false)

let toy_allocator_ok () : Lemma (allocator_ok toy_rep toy)
  = toy_rep_id ();
    FStar.Classical.forall_intro tinit_ok;
    let a1 (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t)
      : Lemma (alloc_at toy_rep toy ph h st sz tag) = talloc_ok ph h st sz tag in
    let a1' (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t)
      : Lemma (forall tag. alloc_at toy_rep toy ph h st sz tag) = FStar.Classical.forall_intro (a1 ph h st sz) in
    let a1'' (ph: phase tprog) (h: mheap) (st: tstate)
      : Lemma (forall sz tag. alloc_at toy_rep toy ph h st sz tag) = FStar.Classical.forall_intro (a1' ph h st) in
    FStar.Classical.forall_intro_3 a1'';
    let f (ph: phase tprog) (h: mheap) (st: tstate) : Lemma (forall h'. inv_frame_at toy_rep toy ph h st h')
      = FStar.Classical.forall_intro (tframe_ok ph h st) in
    FStar.Classical.forall_intro_3 f;
    let ist (h: mheap) (st: tstate) : Lemma (inv_start_at toy h st)
      = let pre () : Lemma (requires tinv Idle h st) (ensures tinv Marking h st)
          = tinv_elim_all Idle h st;
            let l (o: nat) : Lemma (tlocal Marking h st o) = assert (tlocal Idle h st o) in
            FStar.Classical.forall_intro l;
            tinv_intro Marking h st in
        FStar.Classical.move_requires pre () in
    FStar.Classical.forall_intro_2 ist;
    let fw (ph: phase tprog) (h: mheap) (st: tstate) : Lemma (free_white_at toy_rep toy ph h st)
      = let pre2 () : Lemma (requires tinv ph h st)
                            (ensures forall (o: nat). is_block h o ==>
                                       (tfree st h o == true ==> not (dark (col_of h o))) /\
                                       (col_of h o == Blue ==> tfree st h o == true))
          = FStar.Classical.forall_intro (FStar.Classical.move_requires (toy_free_white_o ph h st)) in
        FStar.Classical.move_requires pre2 ();
        forall_repr_id toy_rep h (free_white_m toy ph h st) in
    FStar.Classical.forall_intro_3 fw;
    let fh (st: tstate) (h h': mheap) : Lemma (free_hd_at toy_rep toy st h h')
      = assert (free_hd_m toy st h h' h h');
        forall_repr2_id toy_rep h h' (free_hd_m toy st h h') in
    FStar.Classical.forall_intro_3 fh

/// The toy's capacity condition: a free block at the cursor that reaches the
/// end of the heap (the tail), with at least `sz + 1` words.
let toy_fits : capacity mheap tk tstate = fun ph st h sz ->
  st.cur < h.size /\ is_block h st.cur /\ st.cur + wz_of h st.cur + 1 == h.size /\ wz_of h st.cur + 1 >= sz + 1

/// Room holds whenever the condition does, in every state (a fortiori in
/// every state a run reaches).
let toy_fits_room (ph: phase tprog) (st: tstate) (h: mheap) (sz: size_t)
  : Lemma (toy_fits ph st h sz ==> toy.room ph st h sz == true)
  = ()

let toy_fits_init () : Lemma (fits_init toy_rep toy toy_fits)
  = assert (toy_rep.size_ok 2);
    assert (let (h, st) = toy.init 2 in toy_fits Idle st h 1)

/// Capacity: room holds exactly when the free tail has at least `sz + 1`
/// words.
let toy_room_capacity (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t)
  : Lemma (requires tinv ph h st)
          (ensures toy.room ph st h sz == true <==>
                   (st.cur < h.size /\ toy.free st h st.cur == true /\ wz_of h st.cur + 1 >= sz + 1))
  = tinv_elim ph h st 0

/// ---------------------------------------------------------------------------
/// The sweep
/// ---------------------------------------------------------------------------

let tstart (h: mheap) (st: tstate) : GTot (tprog & tstate) = ((0, st.cur), st)

let tdone (pe: tprog) : bool = fst pe >= snd pe

let tstep (pe: tprog) (h: mheap) (st: tstate) : GTot (tprog & mheap & tstate & step_result) =
  let p = fst pe in
  let e = snd pe in
  if p < e then begin
    let p' = p + wz_of h p + 1 in
    if st.dead p then ((p', e), h, st, { units = 1; freed_words = 0 })
    else if col_of h p = White then
      ((p', e), h, { st with dead = (fun (x: nat) -> x = p || st.dead x) },
       { units = 1; freed_words = wz_of h p + 1 })
    else ((p', e), set_col h p White, st, { units = 1; freed_words = 0 })
  end
  else (pe, h, st, { units = 0; freed_words = 0 })

let tsweep : sweep mheap tk toy = { start = tstart; step = tstep; done = tdone }

let rec sum_single (n: nat) (f: nat -> GTot nat) (p: nat)
  : Lemma (requires forall (o: nat). o <> p ==> f o == 0)
          (ensures sum n f == (if p < n then f p else 0))
          (decreases n)
  = if n = 0 then () else sum_single (n - 1) f p

let tstart_ok (h: mheap) (st: tstate) : Lemma (sweep_start_at toy_rep tsweep h st)
  = toy_rep_id ();
    forall_repr_id toy_rep h (sweep_start_m tsweep h st);
    let pre () : Lemma (requires toy.inv Marking h st /\ well_formed h /\ no_grey h)
                       (ensures (let (p, st') = tsweep.start h st in
                                 toy.inv (Sweeping p) h st' /\
                                 (forall (o: nat). toy.free st' h o == toy.free st h o) /\
                                 (forall (o: nat). in_use toy st h h o ==> tk.unswept p o == true)))
      = tinv_elim_all Marking h st;
        if 0 < st.cur then first_block h;
        let l (o: nat) : Lemma (tlocal (Sweeping (0, st.cur)) h st o) = assert (tlocal Marking h st o) in
        FStar.Classical.forall_intro l;
        tinv_intro (Sweeping (0, st.cur)) h st;
        let u (o: nat) : Lemma (in_use toy st h h o ==> tk.unswept (0, st.cur) o == true) = () in
        FStar.Classical.forall_intro u
    in
    FStar.Classical.move_requires pre ()

/// The step's region holds one block, the one at `p`.
let region_one (h: mheap) (st: tstate) (pe: tprog) (o: nat)
  : Lemma (requires tiled h /\ is_block h (fst pe) /\ fst pe < snd pe /\ is_block h o /\
                    region tk pe (fst pe + wz_of h (fst pe) + 1, snd pe) o)
          (ensures o == fst pe)
  = let p = fst pe in
    if o <> p then begin
      assert (covers h p o);
      assert (covers h o o)
    end

let tstep_local (pe: tprog) (h: mheap) (st: tstate) (o: nat)
  : Lemma (requires tiled h /\ tglob (Sweeping pe) h st /\ tlocal (Sweeping pe) h st o /\ fst pe < snd pe /\
                    (forall (x: nat). is_block h x /\ region tk pe (fst pe + wz_of h (fst pe) + 1, snd pe) x ==> x == fst pe))
          (ensures (let (pe', h', st', _) = tstep pe h st in tlocal (Sweeping pe') h' st' o))
  = ()

/// The step's context: the region holds one block, the one at `p`.
let sctx (pe: tprog) (h: mheap) : prop =
  tiled h /\ fst pe < snd pe /\ is_block h (fst pe) /\
  (forall (x: nat). is_block h x /\ region tk pe (fst pe + wz_of h (fst pe) + 1, snd pe) x ==> x == fst pe)

let s_next (pe: tprog) (h: mheap) : tprog = (fst pe + wz_of h (fst pe) + 1, snd pe)

let s_heap (pe: tprog) (h: mheap) (st: tstate) : GTot mheap = let (_, h', _, _) = tstep pe h st in h'
let s_st (pe: tprog) (h: mheap) (st: tstate) : GTot tstate = let (_, _, st', _) = tstep pe h st in st'

let step_shape (pe: tprog) (h: mheap) (st: tstate) (o: nat)
  : Lemma (requires fst pe < snd pe)
          (ensures (let p = fst pe in
                    let h' = s_heap pe h st in
                    let st' = s_st pe h st in
                    h'.size == h.size /\ h'.body == h.body /\
                    is_block h' o == is_block h o /\ wz_of h' o == wz_of h o /\ tag_of h' o == tag_of h o /\
                    (o <> p ==> h'.hd o == h.hd o /\ st'.dead o == st.dead o) /\
                    in_use toy st' h' h' o == (in_use toy st h h o && not (o = p && col_of h o = White)) /\
                    (in_use toy st h h o /\ o = p /\ col_of h o == Black ==> col_of h' o == White) /\
                    (o = p ==> (tfree st' h' p == (tfree st h p || col_of h p = White)))))
  = ()

let step_words (pe: tprog) (h: mheap) (st: tstate) (w: nat)
  : Lemma (requires sctx pe h)
          (ensures (let h' = s_heap pe h st in
                    let st' = s_st pe h st in
                    let pe' = s_next pe h in
                    (free_word toy st h h w ==> free_word toy st' h' h' w) /\
                    (free_word toy st' h' h' w ==>
                       free_word toy st h h w \/ (exists (o: nat). covers h o w /\ swept_white toy st h h pe pe' o))))
  = let p = fst pe in
    let h' = s_heap pe h st in
    let st' = s_st pe h st in
    let c (b: nat) : Lemma ((covers h b w /\ toy.free st h b ==> covers h' b w /\ toy.free st' h' b) /\
                            (covers h' b w /\ toy.free st' h' b ==>
                               (covers h b w /\ toy.free st h b) \/ (covers h b w /\ swept_white toy st h h pe (s_next pe h) b)))
      = step_shape pe h st b;
        if b = p then assert (region tk pe (s_next pe h) p) in
    FStar.Classical.forall_intro c

let step_blocks (pe: tprog) (h: mheap) (st: tstate) (o: nat)
  : Lemma (requires sctx pe h)
          (ensures (let h' = s_heap pe h st in
                    let st' = s_st pe h st in
                    let pe' = s_next pe h in
                    (swept_white toy st h h pe pe' o ==>
                       in_use toy st' h' h' o == false /\ (forall (w: nat). covers h o w ==> free_word toy st' h' h' w)) /\
                    (in_use toy st h h o /\ region tk pe pe' o /\ col_of h o == Black ==>
                       in_use toy st' h' h' o /\ col_of h' o == White /\ same_contents h h' o) /\
                    (in_use toy st h h o /\ not (region tk pe pe' o) ==> in_use toy st' h' h' o /\ same_block h h' o) /\
                    (in_use toy st' h' h' o ==> in_use toy st h h o) /\
                    swept_words toy st h h pe pe' o == (if o = fst pe then swept_words toy st h h pe pe' (fst pe) else 0)))
  = step_shape pe h st o;
    let p = fst pe in
    let h' = s_heap pe h st in
    let st' = s_st pe h st in
    if o = p then begin
      let ww (w: nat) : Lemma (covers h o w /\ swept_white toy st h h pe (s_next pe h) o ==> free_word toy st' h' h' w)
        = step_shape pe h st o in
      FStar.Classical.forall_intro ww
    end
    else assert (region tk pe (s_next pe h) p)

/// The step's guarantee, at the model heap itself.
let tstep_post (pe: tprog) (h: mheap) (st: tstate) : prop =
  let (pe', h', st', r) = tsweep.step pe h st in
  sweep_step_post toy pe h st pe' h' st' r h h'

let step_post_intro (pe: tprog) (h: mheap) (st: tstate)
  : Lemma (requires (let (pe', h', st', r) = tsweep.step pe h st in
                     (forall (o: nat). tk.unswept pe' o ==> tk.unswept pe o) /\
                     (exists (o: nat). o < h.size /\ region tk pe pe' o) /\
                     h'.size == h.size /\
                     (forall (o: nat). swept_white toy st h h pe pe' o ==>
                        in_use toy st' h' h' o == false /\ (forall (w: nat). covers h o w ==> free_word toy st' h' h' w)) /\
                     (forall (o: nat). in_use toy st h h o /\ region tk pe pe' o /\ col_of h o == Black ==>
                        in_use toy st' h' h' o /\ col_of h' o == White /\ same_contents h h' o) /\
                     (forall (o: nat). in_use toy st h h o /\ not (region tk pe pe' o) ==>
                        in_use toy st' h' h' o /\ same_block h h' o) /\
                     (forall (o: nat). in_use toy st' h' h' o ==> in_use toy st h h o) /\
                     (forall (w: nat). free_word toy st h h w ==> free_word toy st' h' h' w) /\
                     (forall (w: nat). free_word toy st' h' h' w ==>
                        free_word toy st h h w \/ (exists (o: nat). covers h o w /\ swept_white toy st h h pe pe' o)) /\
                     r.freed_words == sum h.size (swept_words toy st h h pe pe') /\
                     toy.inv (Sweeping pe') h' st' /\ well_formed h'))
          (ensures tstep_post pe h st)
  = ()

#push-options "--z3rlimit 40"
let tstep_m (pe: tprog) (h: mheap) (st: tstate)
  : Lemma (toy.inv (Sweeping pe) h st /\ well_formed h /\ no_grey h /\ tsweep.done pe == false ==> tstep_post pe h st)
  = let pre () : Lemma (requires toy.inv (Sweeping pe) h st /\ well_formed h /\ no_grey h /\ tsweep.done pe == false)
                       (ensures tstep_post pe h st)
      = let p = fst pe in
        let e = snd pe in
        let p' = p + wz_of h p + 1 in
        let pe' = (p', e) in
        let (_, h', st', r) = tstep pe h st in
        assert (h' == s_heap pe h st /\ st' == s_st pe h st /\ pe' == s_next pe h);
        tinv_elim (Sweeping pe) h st p;
        assert (p < st.cur);
        if p' > e && e < h.size then begin assert (covers h p e); assert (covers h e e) end;
        assert (p' <= e);
        let one (o: nat) : Lemma (is_block h o /\ region tk pe pe' o ==> o == p)
          = if is_block h o && region tk pe pe' o then region_one h st pe o in
        FStar.Classical.forall_intro one;
        assert (sctx pe h);
        FStar.Classical.forall_intro (step_shape pe h st);
        tiled_hd h h';
        if p' < e then next_block h p;
        tinv_elim_all (Sweeping pe) h st;
        assert (tglob (Sweeping pe') h' st');
        let l (o: nat) : Lemma (tlocal (Sweeping pe') h' st' o) = tstep_local pe h st o in
        FStar.Classical.forall_intro l;
        tinv_intro (Sweeping pe') h' st';
        FStar.Classical.forall_intro (step_words pe h st);
        FStar.Classical.forall_intro (step_blocks pe h st);
        sum_single h.size (swept_words toy st h h pe pe') p;
        assert (region tk pe pe' p);
        assert (r.freed_words == swept_words toy st h h pe pe' p);
        step_post_intro pe h st
    in
    FStar.Classical.move_requires pre ()
#pop-options

let tstep_ok (pe: tprog) (h: mheap) (st: tstate) : Lemma (sweep_step_at toy_rep tsweep pe h st)
  = tstep_m pe h st;
    toy_rep_id ();
    let (pe', h', st', r) = tsweep.step pe h st in
    lifted_id toy_rep (sweep_step_pre tsweep pe h st) h h' (sweep_step_post toy pe h st pe' h' st' r)

let tdone_ok (pe: tprog) (h: mheap) (st: tstate) : Lemma (sweep_done_at toy_rep tsweep pe h st)
  = toy_rep_id ();
    forall_repr_id toy_rep h (sweep_done_m tsweep pe h st);
    let pre () : Lemma (requires toy.inv (Sweeping pe) h st /\ well_formed h /\ tsweep.done pe == true)
                       (ensures toy.inv Idle h st /\
                                (forall (o: nat). in_use toy st h h o ==> tk.unswept pe o == false) /\
                                (forall (o: nat). is_block h o ==> col_of h o == White))
      = tinv_elim_all (Sweeping pe) h st;
        let l (o: nat) : Lemma (tlocal Idle h st o) = assert (tlocal (Sweeping pe) h st o) in
        FStar.Classical.forall_intro l;
        tinv_intro Idle h st
    in
    FStar.Classical.move_requires pre ()

let toy_sweep_ok () : Lemma (sweep_ok toy_rep tsweep)
  = FStar.Classical.forall_intro_2 tstart_ok;
    FStar.Classical.forall_intro_3 tstep_ok;
    FStar.Classical.forall_intro_3 tdone_ok
