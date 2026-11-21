/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ToyMinor - a toy minor collection meeting `minor_ok`
/// ---------------------------------------------------------------------------
///
/// Satisfiability of `minor_ok` (GC.Spec.Top.Iface), over the toy allocator.
///
/// The collection promotes the live young objects (reachable from the roots
/// and the remembered slots through young fields; the set is taken
/// classically, the ghost model of Cheney's scan) one by one through
/// `toy.alloc`, each copy filled with its young fields.  Then every pointer
/// field of every block in use is forwarded, and so are the roots.  If the
/// allocator refuses one copy, the result is OutOfRoom, and the refusal is
/// the justification `oor_justified` asks for.
///
/// Proved: `toy_minor_ok`.

module GC.Spec.Top.ToyMinor

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.IdRep
open GC.Spec.Top.ToyRep
open GC.Spec.Top.Toy
module L = FStar.List.Tot
module Seq = FStar.Seq

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let live_g (w: world) (y: nat) : GTot bool =
  is_block w.yng y && FStar.IndefiniteDescription.strong_excluded_middle (minor_live w y)

/// The live young blocks below `n`.
let rec live_list (w: world) (n: nat) : GTot (list nat) (decreases n) =
  if n = 0 then []
  else (let tl = live_list w (n - 1) in if live_g w (n - 1) then (n - 1) :: tl else tl)

let rec live_list_spec (w: world) (n: nat)
  : Lemma (L.noRepeats (live_list w n) /\
           (forall (o: nat). L.memP o (live_list w n) <==> (o < n /\ live_g w o == true)))
          (decreases n)
  = if n = 0 then () else live_list_spec w (n - 1)

let upd_fwd (fwd: nat -> option nat) (o c: nat) (x: nat) : option nat =
  if x = o then Some c else fwd x

/// Promotion through the allocator, keeping the forwarding map.
let rec pfold (ph: phase tprog) (h: mheap) (st: tstate) (y: mheap) (fwd: nat -> option nat) (ys: list nat)
  : GTot (option (mheap & tstate & (nat -> option nat))) (decreases ys) =
  match ys with
  | [] -> Some (h, st, fwd)
  | o :: tl ->
    if wz_of y o >= 1 && tag_of y o <> infix_tag then
      (let (h', st', r) = toy.alloc ph h st (wz_of y o) (tag_of y o) in
       match r with
       | NoRoom -> None
       | Ok c -> pfold ph (fill h' c (fields_of y o)) st' y (upd_fwd fwd o c) tl)
    else None

let rec pfold_none (ph: phase tprog) (h: mheap) (st: tstate) (y: mheap) (fwd: nat -> option nat) (ys: list nat)
  : Lemma (ensures None? (pfold ph h st y fwd ys) <==> plain_fold toy ph h st y ys == None)
          (decreases ys)
  = match ys with
    | [] -> ()
    | o :: tl ->
      if wz_of y o >= 1 && tag_of y o <> infix_tag then begin
        let (h', st', r) = toy.alloc ph h st (wz_of y o) (tag_of y o) in
        match r with
        | NoRoom -> ()
        | Ok c ->
          let fwd' = (upd_fwd fwd o c) in
          assert (pfold ph h st y fwd ys == pfold ph (fill h' c (fields_of y o)) st' y fwd' tl);
          assert (plain_fold toy ph h st y ys == plain_fold toy ph (fill h' c (fields_of y o)) st' y tl);
          pfold_none ph (fill h' c (fields_of y o)) st' y fwd' tl
      end

/// The block covering a word.
let rec last_block (h: mheap) (n: nat) : option nat =
  if n = 0 then None else if is_block h (n - 1) then Some (n - 1) else last_block h (n - 1)

let rec last_block_spec (h: mheap) (n: nat)
  : Lemma (match last_block h n with
           | Some b -> is_block h b /\ b < n /\ (forall (x: nat). b < x /\ x < n ==> not (is_block h x))
           | None -> (forall (x: nat). x < n ==> not (is_block h x)))
  = if n = 0 then () else last_block_spec h (n - 1)

let owner (h: mheap) (w: nat) : option nat =
  match last_block h (w + 1) with
  | Some o -> if w <= o + wz_of h o then Some o else None
  | None -> None

let owner_spec (h: mheap) (o w: nat)
  : Lemma (requires tiled h)
          (ensures owner h w == Some o <==> covers h o w)
  = last_block_spec h (w + 1);
    match last_block h (w + 1) with
    | Some b -> if covers h o w && b <> o then begin assert (covers h o b); assert (covers h b b) end
    | None -> ()

/// Forward every pointer field of every block in use.
let forward (st: tstate) (h: mheap) (y: mheap) (fwd: nat -> option nat) : mheap =
  { h with body = (fun (w: nat) ->
      match owner h w with
      | Some o ->
        if is_block h o && not (tfree st h o) && scannable (tag_of h o) && o < w
        then fwdv y fwd (h.body w) else h.body w
      | None -> h.body w) }

let tcollect (ph: phase tprog) (st: tstate) (w: world) : GTot (minor_result mheap tk toy) =
  let ys = live_list w w.yng.size in
  match pfold ph w.maj st w.yng (fun _ -> None) ys with
  | None -> OutOfRoom
  | Some (h1, st1, fwd) -> Done (forward st1 h1 w.yng fwd) st1 (L.map (fwdv w.yng fwd) w.roots) fwd

let tcollect_c (ph: phase tprog) (st: tstate) (cw: cworld mheap mheap) : GTot (minor_result mheap tk toy) =
  tcollect ph st (tview cw)

let tminor : minor mheap mheap tk toy = { collect = tcollect_c }

/// ---------------------------------------------------------------------------
/// The promotion loop's invariant
/// ---------------------------------------------------------------------------

let wf_same_hd (h h': mheap)
  : Lemma (requires well_formed h /\ h'.size == h.size /\ h'.hd == h.hd)
          (ensures well_formed h')
  = tiled_hd h h'

/// Filling block `c` leaves the fields of every other block.
let fill_other (h: mheap) (c: nat) (vs: list value) (x: nat)
  : Lemma (requires tiled h /\ is_block h c /\ is_block h x /\ x <> c /\ L.length vs == wz_of h c)
          (ensures (forall (i: nat). i < wz_of h x ==> field (fill h c vs) x i == field h x i))
  = let aux (i: nat) : Lemma (i < wz_of h x ==> field (fill h c vs) x i == field h x i)
      = let w = x + 1 + i in
        if i < wz_of h x && c < w && w - c - 1 < L.length vs then begin
          assert (covers h c w); assert (covers h x w)
        end in
    FStar.Classical.forall_intro aux

/// Membership in the list of promoted objects, opaque to the solver.
[@@"opaque_to_smt"]
let inl (o: nat) (dn: list nat) : prop = L.memP o dn

let inl_reveal (o: nat) (dn: list nat) : Lemma (inl o dn <==> L.memP o dn)
  = reveal_opaque (`%inl) (inl o dn)

let inl_cons (o' o: nat) (dn: list nat)
  : Lemma (inl o' (o :: dn) <==> (o' == o \/ inl o' dn)) [SMTPat (inl o' (o :: dn))]
  = inl_reveal o' (o :: dn); inl_reveal o' dn

let inl_nil (o: nat) : Lemma (~(inl o [])) [SMTPat (inl o [])]
  = inl_reveal o []

/// The facts about one promoted copy (opaque: its quantifiers are only
/// opened where needed).
[@@"opaque_to_smt"]
let copy_ok (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap) (h: mheap) (o c: nat) : prop =
  (forall (w: nat). covers h c w ==> free_word toy st0 h0 h0 w) /\
  h.hd c == Some ({ wz = wz_of y o; tag = tag_of y o; col = colour_at tk ph c }) /\
  (forall (i: nat). i < wz_of y o ==> field h c i == field y o i)

let copy_ok_reveal (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap) (h: mheap) (o c: nat)
  : Lemma (copy_ok ph h0 st0 y h o c <==>
           ((forall (w: nat). covers h c w ==> free_word toy st0 h0 h0 w) /\
            h.hd c == Some ({ wz = wz_of y o; tag = tag_of y o; col = colour_at tk ph c }) /\
            (forall (i: nat). i < wz_of y o ==> field h c i == field y o i)))
  = reveal_opaque (`%copy_ok) (copy_ok ph h0 st0 y h o c)

/// The promotion loop's invariant, in parts with explicit patterns.
let pv_use (h0: mheap) (st0: tstate) (h: mheap) (st: tstate) (fwd: nat -> option nat) : prop =
  forall (x: nat).{:pattern (in_use toy st h h x)}
    in_use toy st h h x <==> (in_use toy st0 h0 h0 x \/ (exists (o: nat). fwd o == Some x))

let pv_same (h0: mheap) (st0: tstate) (h: mheap) : prop =
  forall (x: nat).{:pattern (in_use toy st0 h0 h0 x)} in_use toy st0 h0 h0 x ==> same_block h0 h x

let pv_copies (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap) (h: mheap) (fwd: nat -> option nat) (dn: list nat) : prop =
  forall (o: nat).{:pattern (fwd o)}
    (match fwd o with Some c -> inl o dn /\ copy_ok ph h0 st0 y h o c | None -> True)

let pv_done (fwd: nat -> option nat) (dn: list nat) : prop =
  forall (o: nat).{:pattern (inl o dn)} inl o dn ==> Some? (fwd o)

let pv_inj (fwd: nat -> option nat) : prop =
  forall (o1 o2: nat).{:pattern (fwd o1); (fwd o2)} Some? (fwd o1) /\ fwd o1 == fwd o2 ==> o1 == o2

let pinv (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) : prop =
  toy.inv ph h st /\ well_formed h /\ well_formed h0 /\ h.size == h0.size /\
  pv_use h0 st0 h st fwd /\ pv_same h0 st0 h /\ pv_copies ph h0 st0 y h fwd dn /\ pv_done fwd dn /\ pv_inj fwd

let pinv_base (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn)
          (ensures toy.inv ph h st /\ well_formed h /\ well_formed h0 /\ h.size == h0.size)
  = ()

let pinv_use (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (x: nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn)
          (ensures (in_use toy st h h x <==> (in_use toy st0 h0 h0 x \/ (exists (o: nat). fwd o == Some x))) /\
                   (in_use toy st0 h0 h0 x ==> same_block h0 h x))
  = ()

let copies_elim (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap) (h: mheap) (fwd: nat -> option nat)
    (dn: list nat) (o c: nat)
  : Lemma (requires pv_copies ph h0 st0 y h fwd dn /\ fwd o == Some c)
          (ensures inl o dn /\ copy_ok ph h0 st0 y h o c)
  = ()

let pinv_copy (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o c: nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn /\ fwd o == Some c)
          (ensures inl o dn /\ copy_ok ph h0 st0 y h o c /\ in_use toy st h h c /\
                   (forall (o2: nat). fwd o2 == Some c ==> o2 == o))
  = copies_elim ph h0 st0 y h fwd dn o c;
    assert (exists (o1: nat). fwd o1 == Some c)

let pinv_done (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn)
          (ensures (inl o dn ==> Some? (fwd o)) /\ (~(inl o dn) ==> fwd o == None))
  = match fwd o with Some c -> pinv_copy ph h0 st0 y h st fwd dn o c | None -> ()

let pinv_intro (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat)
  : Lemma (requires
             toy.inv ph h st /\ well_formed h /\ well_formed h0 /\ h.size == h0.size /\
             pv_use h0 st0 h st fwd /\ pv_same h0 st0 h /\ pv_copies ph h0 st0 y h fwd dn /\
             pv_done fwd dn /\ pv_inj fwd)
          (ensures pinv ph h0 st0 y h st fwd dn)
  = ()

/// A word free now was free at the start.
let free_back (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (w: nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn /\ free_word toy st h h w)
          (ensures free_word toy st0 h0 h0 w)
  = pinv_base ph h0 st0 y h st fwd dn;
    let b = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun b -> covers h b w /\ toy.free st h b == true) in
    assert (w < h0.size);
    assert (exists (b0: nat). covers h0 b0 w);
    let b0 = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun b0 -> covers h0 b0 w) in
    pinv_use ph h0 st0 y h st fwd dn b0;
    if in_use toy st0 h0 h0 b0 then begin
      assert (same_block h0 h b0);
      assert (covers h b0 w);
      assert (in_use toy st h h b0)
    end

let ex_upd (fwd: nat -> option nat) (o c x: nat)
  : Lemma (requires fwd o == None)
          (ensures (exists (o': nat). upd_fwd fwd o c o' == Some x) <==> ((exists (o': nat). fwd o' == Some x) \/ x == c))
  = let l2r () : Lemma (requires exists (o': nat). upd_fwd fwd o c o' == Some x)
                       (ensures (exists (o': nat). fwd o' == Some x) \/ x == c)
      = let o' = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o' -> upd_fwd fwd o c o' == Some x) in
        if o' = o then () else assert (fwd o' == Some x) in
    let r2l () : Lemma (requires (exists (o': nat). fwd o' == Some x) \/ x == c)
                       (ensures exists (o': nat). upd_fwd fwd o c o' == Some x)
      = if x = c then assert (upd_fwd fwd o c o == Some x)
        else begin
          let o' = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun o' -> fwd o' == Some x) in
          assert (upd_fwd fwd o c o' == Some x)
        end in
    FStar.Classical.move_requires l2r ();
    FStar.Classical.move_requires r2l ()

/// The toy allocation, pointwise.
let talloc_point (ph: phase tprog) (h: mheap) (st: tstate) (sz: size_t) (tag: tag_t) (x: nat)
  : Lemma (requires tinv ph h st /\ st.cur + sz + 1 <= h.size)
          (ensures (let h' = talloc_heap ph h st.cur sz tag in
                    let st' = { st with cur = st.cur + sz + 1 } in
                    (in_use toy st' h' h' x <==> (in_use toy st h h x \/ x == st.cur)) /\
                    (in_use toy st h h x ==> h'.hd x == h.hd x) /\
                    (covers h' st.cur x ==> free_word toy st h h x) /\
                    in_use toy st h h st.cur == false /\
                    h'.hd st.cur == Some ({ wz = sz; tag = tag; col = colour_at tk ph st.cur }) /\
                    h'.body == h.body /\ h'.size == h.size))
  = talloc_use ph h st sz tag x;
    tinv_elim ph h st x;
    tinv_elim ph h st st.cur;
    talloc_heap_hd ph h st sz tag x;
    if is_block h x && x <> st.cur then tail_x h st.cur x;
    if covers (talloc_heap ph h st.cur sz tag) st.cur x then assert (covers h st.cur x)

let pstep_old (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t)
    (o' c': nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn /\ st.cur + sz + 1 <= h.size /\
                    L.length (fields_of y o) == sz /\ fwd o' == Some c' /\ tag <> infix_tag)
          (ensures (let h'' = fill (talloc_heap ph h st.cur sz tag) st.cur (fields_of y o) in
                    copy_ok ph h0 st0 y h'' o' c' /\ c' <> st.cur))
  = let h' = talloc_heap ph h st.cur sz tag in
    let h'' = fill h' st.cur (fields_of y o) in
    pinv_copy ph h0 st0 y h st fwd dn o' c';
    copy_ok_reveal ph h0 st0 y h o' c';
    copy_ok_reveal ph h0 st0 y h'' o' c';
    pinv_base ph h0 st0 y h st fwd dn;
    talloc_point ph h st sz tag c';
    tinv_elim ph h st st.cur;
    talloc_tiled ph h st sz tag;
    fill_other h' st.cur (fields_of y o) c';
    assert (h''.hd c' == h.hd c');
    let cv (w: nat) : Lemma (covers h'' c' w == covers h c' w) = () in
    FStar.Classical.forall_intro cv

let pstep_new (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn /\ st.cur + sz + 1 <= h.size /\
                    sz == wz_of y o /\ tag == tag_of y o)
          (ensures copy_ok ph h0 st0 y (fill (talloc_heap ph h st.cur sz tag) st.cur (fields_of y o)) o st.cur)
  = let c = st.cur in
    let h' = talloc_heap ph h c sz tag in
    let vs = fields_of y o in
    let h'' = fill h' c vs in
    fields_of_spec y o;
    pinv_base ph h0 st0 y h st fwd dn;
    let ww (w: nat) : Lemma (covers h'' c w ==> free_word toy st0 h0 h0 w)
      = talloc_point ph h st sz tag w;
        if covers h'' c w then begin
          assert (covers h' c w);
          free_back ph h0 st0 y h st fwd dn w
        end in
    FStar.Classical.forall_intro ww;
    talloc_point ph h st sz tag c;
    let ff (i: nat) : Lemma (i < wz_of y o ==> field h'' c i == field y o i)
      = if i < wz_of y o then begin
          assert (field h'' c i == h''.body (c + 1 + i));
          assert ((c + 1 + i) - c - 1 == i);
          assert (field h'' c i == L.index vs i)
        end in
    FStar.Classical.forall_intro ff;
    copy_ok_reveal ph h0 st0 y h'' o c

let ps_pre (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t) : prop =
  pinv ph h0 st0 y h st fwd dn /\ ~(inl o dn) /\ st.cur + sz + 1 <= h.size /\
  sz == wz_of y o /\ tag == tag_of y o /\ tag <> infix_tag

let ps_heap (ph: phase tprog) (h: mheap) (st: tstate) (y: mheap) (o: nat) (sz: size_t) (tag: tag_t) : mheap =
  fill (talloc_heap ph h st.cur sz tag) st.cur (fields_of y o)

let ps_st (st: tstate) (sz: size_t) : tstate = { st with cur = st.cur + sz + 1 }

let ps_use (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t) (x: nat)
  : Lemma (requires ps_pre ph h0 st0 y h st fwd dn o sz tag)
          (ensures (let h'' = ps_heap ph h st y o sz tag in
                    let st' = ps_st st sz in
                    (in_use toy st' h'' h'' x <==> (in_use toy st0 h0 h0 x \/ (exists (o': nat). upd_fwd fwd o st.cur o' == Some x))) /\
                    (in_use toy st0 h0 h0 x ==> same_block h0 h'' x)))
  = let c = st.cur in
    let h' = talloc_heap ph h c sz tag in
    let vs = fields_of y o in
    fields_of_spec y o;
    pinv_base ph h0 st0 y h st fwd dn;
    pinv_done ph h0 st0 y h st fwd dn o;
    tinv_elim ph h st c;
    talloc_tiled ph h st sz tag;
    talloc_point ph h st sz tag c;
    talloc_point ph h st sz tag x;
    pinv_use ph h0 st0 y h st fwd dn x;
    assert (in_use toy (ps_st st sz) (ps_heap ph h st y o sz tag) (ps_heap ph h st y o sz tag) x == in_use toy (ps_st st sz) h' h' x);
    ex_upd fwd o c x;
    let p_new = in_use toy (ps_st st sz) h' h' x in
    let p_mid = in_use toy st h h x in
    let p_old = in_use toy st0 h0 h0 x in
    let e_fwd = exists (o': nat). fwd o' == Some x in
    let e_upd = exists (o': nat). upd_fwd fwd o c o' == Some x in
    assert (p_new <==> (p_mid \/ x == c));
    assert (p_mid <==> (p_old \/ e_fwd));
    assert (e_upd <==> (e_fwd \/ x == c));
    assert (p_new <==> (p_old \/ e_upd));
    if in_use toy st0 h0 h0 x then begin
      assert (in_use toy st h h x);
      fill_other h' c vs x
    end

let ps_copy (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t) (o': nat)
  : Lemma (requires ps_pre ph h0 st0 y h st fwd dn o sz tag)
          (ensures (match upd_fwd fwd o st.cur o' with
                    | Some c' -> inl o' (o :: dn) /\ copy_ok ph h0 st0 y (ps_heap ph h st y o sz tag) o' c'
                    | None -> True))
  = fields_of_spec y o;
    if o' = o then pstep_new ph h0 st0 y h st fwd dn o sz tag
    else match fwd o' with
      | Some c' -> pinv_copy ph h0 st0 y h st fwd dn o' c'; pstep_old ph h0 st0 y h st fwd dn o sz tag o' c'
      | None -> ()

let ps_inj (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t) (o1 o2: nat)
  : Lemma (requires ps_pre ph h0 st0 y h st fwd dn o sz tag)
          (ensures (let fwd' = upd_fwd fwd o st.cur in Some? (fwd' o1) /\ fwd' o1 == fwd' o2 ==> o1 == o2))
  = fields_of_spec y o;
    pinv_done ph h0 st0 y h st fwd dn o;
    (match fwd o1 with
     | Some c1 -> pinv_copy ph h0 st0 y h st fwd dn o1 c1; pstep_old ph h0 st0 y h st fwd dn o sz tag o1 c1
     | None -> ());
    (match fwd o2 with
     | Some c2 -> pinv_copy ph h0 st0 y h st fwd dn o2 c2; pstep_old ph h0 st0 y h st fwd dn o sz tag o2 c2
     | None -> ())

let ps_done (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t) (o': nat)
  : Lemma (requires ps_pre ph h0 st0 y h st fwd dn o sz tag)
          (ensures inl o' (o :: dn) ==> Some? (upd_fwd fwd o st.cur o'))
  = pinv_done ph h0 st0 y h st fwd dn o'

let ps_all (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t)
  : Lemma (requires ps_pre ph h0 st0 y h st fwd dn o sz tag)
          (ensures (let h'' = ps_heap ph h st y o sz tag in
                    let fwd' = upd_fwd fwd o st.cur in
                    pv_use h0 st0 h'' (ps_st st sz) fwd' /\ pv_same h0 st0 h'' /\
                    pv_copies ph h0 st0 y h'' fwd' (o :: dn) /\ pv_done fwd' (o :: dn) /\ pv_inj fwd'))
  = let h'' = ps_heap ph h st y o sz tag in
    let fwd' = upd_fwd fwd o st.cur in
    let u () : Lemma (pv_use h0 st0 h'' (ps_st st sz) fwd' /\ pv_same h0 st0 h'')
      = FStar.Classical.forall_intro (ps_use ph h0 st0 y h st fwd dn o sz tag) in
    u ();
    let c () : Lemma (pv_copies ph h0 st0 y h'' fwd' (o :: dn))
      = FStar.Classical.forall_intro (ps_copy ph h0 st0 y h st fwd dn o sz tag) in
    c ();
    let d () : Lemma (pv_done fwd' (o :: dn))
      = FStar.Classical.forall_intro (ps_done ph h0 st0 y h st fwd dn o sz tag) in
    d ();
    let i () : Lemma (pv_inj fwd')
      = FStar.Classical.forall_intro_2 (ps_inj ph h0 st0 y h st fwd dn o sz tag) in
    i ()

let pstep_some (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat) (sz: size_t) (tag: tag_t)
  : Lemma (requires ps_pre ph h0 st0 y h st fwd dn o sz tag)
          (ensures pinv ph h0 st0 y (ps_heap ph h st y o sz tag) (ps_st st sz) (upd_fwd fwd o st.cur) (o :: dn))
  = let c = st.cur in
    let h' = talloc_heap ph h c sz tag in
    let h'' = ps_heap ph h st y o sz tag in
    let fwd' = upd_fwd fwd o c in
    fields_of_spec y o;
    pinv_base ph h0 st0 y h st fwd dn;
    tinv_elim ph h st c;
    talloc_inv ph h st sz tag (fields_of y o);
    talloc_tiled ph h st sz tag;
    wf_same_hd h' h'';
    ps_all ph h0 st0 y h st fwd dn o sz tag;
    pinv_intro ph h0 st0 y h'' (ps_st st sz) fwd' (o :: dn)

let pstep (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (o: nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn /\ ~(inl o dn) /\ is_block y o /\
                    wz_of y o >= 1 /\ tag_of y o <> infix_tag)
          (ensures (let (h', st', r) = toy.alloc ph h st (wz_of y o) (tag_of y o) in
                    match r with
                    | NoRoom -> True
                    | Ok c -> pinv ph h0 st0 y (fill h' c (fields_of y o)) st'
                               (upd_fwd fwd o c) (o :: dn)))
  = let sz : size_t = wz_of y o in
    let tag = tag_of y o in
    if st.cur + sz + 1 <= h.size then pstep_some ph h0 st0 y h st fwd dn o sz tag

let pinv_congr (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn1 dn2: list nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn1 /\ (forall (x: nat). inl x dn1 <==> inl x dn2))
          (ensures pinv ph h0 st0 y h st fwd dn2)
  = let c (o: nat) : Lemma (match fwd o with Some c -> inl o dn2 /\ copy_ok ph h0 st0 y h o c | None -> True)
      = match fwd o with Some c -> pinv_copy ph h0 st0 y h st fwd dn1 o c | None -> () in
    FStar.Classical.forall_intro c;
    let d (o: nat) : Lemma (inl o dn2 ==> Some? (fwd o)) = pinv_done ph h0 st0 y h st fwd dn1 o in
    FStar.Classical.forall_intro d;
    assert (pv_copies ph h0 st0 y h fwd dn2);
    assert (pv_done fwd dn2)

let rec pfold_inv (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h: mheap) (st: tstate) (fwd: nat -> option nat) (dn: list nat) (ys: list nat)
  : Lemma (requires pinv ph h0 st0 y h st fwd dn /\ young_ok y /\ L.noRepeats ys /\
                    (forall (o: nat). L.memP o ys ==> is_block y o /\ ~(inl o dn)))
          (ensures (match pfold ph h st y fwd ys with
                    | Some (h1, st1, fwd1) ->
                      pinv ph h0 st0 y h1 st1 fwd1 (L.append ys dn) /\
                      (forall (o: nat). Some? (fwd1 o) ==> inl o (L.append ys dn))
                    | None -> True))
          (decreases ys)
  = match ys with
    | [] ->
      let f (o: nat) : Lemma (Some? (fwd o) ==> inl o dn)
        = match fwd o with Some c -> pinv_copy ph h0 st0 y h st fwd dn o c | None -> () in
      FStar.Classical.forall_intro f
    | o :: tl ->
      let sz : size_t = wz_of y o in
      pstep ph h0 st0 y h st fwd dn o;
      let (h', st', r) = toy.alloc ph h st sz (tag_of y o) in
      match r with
      | NoRoom -> ()
      | Ok c ->
        let fwd' = upd_fwd fwd o c in
        let h'' = fill h' c (fields_of y o) in
        assert (pfold ph h st y fwd ys == pfold ph h'' st' y fwd' tl);
        pfold_inv ph h0 st0 y h'' st' fwd' (o :: dn) tl;
        let m (x: nat) : Lemma (inl x (L.append tl (o :: dn)) <==> inl x (L.append ys dn))
          = inl_reveal x (L.append tl (o :: dn)); inl_reveal x (L.append ys dn);
            inl_reveal x (o :: dn); inl_reveal x dn;
            L.append_memP tl (o :: dn) x; L.append_memP ys dn x in
        FStar.Classical.forall_intro m;
        match pfold ph h'' st' y fwd' tl with
        | Some (h1, st1, fwd1) -> pinv_congr ph h0 st0 y h1 st1 fwd1 (L.append tl (o :: dn)) (L.append ys dn)
        | None -> ()

/// ---------------------------------------------------------------------------
/// Forwarding
/// ---------------------------------------------------------------------------

let forward_facts (ph: phase tprog) (st: tstate) (h: mheap) (y: mheap) (fwd: nat -> option nat)
  : Lemma (requires toy.inv ph h st /\ well_formed h)
          (ensures (let h2 = forward st h y fwd in
                    h2.hd == h.hd /\ h2.size == h.size /\ toy.inv ph h2 st /\ well_formed h2 /\
                    (forall (x i: nat). in_use toy st h h x /\ i < wz_of h x ==> field h2 x i == fwd_field h x i y fwd)))
  = let h2 = forward st h y fwd in
    wf_same_hd h h2;
    let f (x i: nat) : Lemma (in_use toy st h h x /\ i < wz_of h x ==> field h2 x i == fwd_field h x i y fwd)
      = if in_use toy st h h x && i < wz_of h x then owner_spec h x (x + 1 + i) in
    FStar.Classical.forall_intro_2 f;
    let b (w: nat) : Lemma (h2.body w =!= h.body w ==>
                            (exists (o: nat). in_use toy st h h o /\ o < w /\ w <= o + wz_of h o))
      = match owner h w with
        | Some o -> owner_spec h o w
        | None -> () in
    FStar.Classical.forall_intro b;
    assert (inv_frame_rel toy ph st h h h2);
    tframe_m ph h st h2

/// ---------------------------------------------------------------------------
/// The contract
/// ---------------------------------------------------------------------------

let fwd_field_congr (h1: mheap) (c: nat) (y: mheap) (o i: nat) (yy: mheap) (fwd: nat -> option nat)
  : Lemma (requires tag_of h1 c == tag_of y o /\ field h1 c i == field y o i)
          (ensures fwd_field h1 c i yy fwd == fwd_field y o i yy fwd)
  = ()

let copy_fwd (ph: phase tprog) (h0: mheap) (st0: tstate) (y: mheap)
    (h1: mheap) (st1: tstate) (fwd: nat -> option nat) (ys: list nat) (o c: nat)
  : Lemma (requires pinv ph h0 st0 y h1 st1 fwd ys /\ fwd o == Some c)
          (ensures (let h2 = forward st1 h1 y fwd in
                    (forall (w': nat). covers h2 c w' ==> free_word toy st0 h0 h0 w') /\
                    h2.hd c == Some ({ wz = wz_of y o; tag = tag_of y o; col = colour_at tk ph c }) /\
                    (forall (i: nat). i < wz_of y o ==> field h2 c i == fwd_field y o i y fwd)))
  = let h2 = forward st1 h1 y fwd in
    pinv_base ph h0 st0 y h1 st1 fwd ys;
    pinv_copy ph h0 st0 y h1 st1 fwd ys o c;
    copy_ok_reveal ph h0 st0 y h1 o c;
    forward_facts ph st1 h1 y fwd;
    assert (tag_of h1 c == tag_of y o /\ wz_of h1 c == wz_of y o);
    let fi (i: nat) : Lemma (i < wz_of y o ==> field h2 c i == fwd_field y o i y fwd)
      = if i < wz_of y o then begin
          assert (field h2 c i == fwd_field h1 c i y fwd);
          fwd_field_congr h1 c y o i y fwd
        end in
    FStar.Classical.forall_intro fi;
    let cv (w': nat) : Lemma (covers h2 c w' == covers h1 c w') = () in
    FStar.Classical.forall_intro cv

#push-options "--z3rlimit 40"
/// The guarantee on the model, at the world itself.
let tminor_post (ph: phase tprog) (st: tstate) (w: world) : prop =
  match tcollect ph st w with
  | OutOfRoom ->
    exists (ys: list nat). L.noRepeats ys /\
      (forall (o: nat). L.memP o ys ==> is_block w.yng o /\ minor_live w o) /\
      plain_fold toy ph w.maj st w.yng ys == None
  | Done h2 st' roots' fwd -> minor_post_done toy ph st w.maj w h2 st' roots' fwd h2

let tminor_m (ph: phase tprog) (st: tstate) (w: world) : Lemma (minor_pre toy ph st w.maj w ==> tminor_post ph st w)
  = let pre () : Lemma (requires minor_pre toy ph st w.maj w)
                       (ensures tminor_post ph st w)
      = let y = w.yng in
        let ys = live_list w y.size in
        live_list_spec w y.size;
        let fwd0 : nat -> option nat = fun _ -> None in
        let same0 (x: nat) : Lemma (same_block w.maj w.maj x) = () in
        FStar.Classical.forall_intro same0;
        assert (pv_use w.maj st w.maj st fwd0);
        assert (pv_same w.maj st w.maj);
        assert (pv_copies ph w.maj st y w.maj fwd0 []);
        assert (pv_done fwd0 []);
        assert (pv_inj fwd0);
        pinv_intro ph w.maj st y w.maj st fwd0 [];
        pfold_inv ph w.maj st y w.maj st fwd0 [] ys;
        pfold_none ph w.maj st y fwd0 ys;
        L.append_l_nil ys;
        match pfold ph w.maj st y fwd0 ys with
        | None ->
          assert (tcollect ph st w == OutOfRoom);
          assert (plain_fold toy ph w.maj st y ys == None)
        | Some (h1, st1, fwd) ->
          let h2 = forward st1 h1 y fwd in
          pinv_base ph w.maj st y h1 st1 fwd ys;
          assert (tcollect ph st w == Done h2 st1 (L.map (fwdv y fwd) w.roots) fwd);
          forward_facts ph st1 h1 y fwd;
          let n1 (o: nat) : Lemma (Some? (fwd o) <==> (is_block y o /\ minor_live w o))
            = pinv_done ph w.maj st y h1 st1 fwd ys o;
              inl_reveal o ys;
              assert (o < y.size \/ ~(is_block y o)) in
          FStar.Classical.forall_intro n1;
          let n3 (o c: nat) : Lemma (fwd o == Some c ==>
                                     (forall (w': nat). covers h2 c w' ==> free_word toy st w.maj w.maj w') /\
                                     h2.hd c == Some ({ wz = wz_of y o; tag = tag_of y o; col = colour_at tk ph c }) /\
                                     (forall (i: nat). i < wz_of y o ==> field h2 c i == fwd_field y o i y fwd))
            = if fwd o = Some c then copy_fwd ph w.maj st y h1 st1 fwd ys o c in
          FStar.Classical.forall_intro_2 n3;
          let n5 (x: nat) : Lemma (in_use toy st w.maj w.maj x ==>
                                   h2.hd x == w.maj.hd x /\
                                   (forall (i: nat). i < wz_of w.maj x ==> field h2 x i == fwd_field w.maj x i y fwd))
            = pinv_use ph w.maj st y h1 st1 fwd ys x;
              if in_use toy st w.maj w.maj x then assert (in_use toy st1 h1 h1 x /\ same_block w.maj h1 x) in
          FStar.Classical.forall_intro n5;
          let n4 (x: nat) : Lemma (in_use toy st1 h2 h2 x <==> (in_use toy st w.maj w.maj x \/ (exists (o: nat). fwd o == Some x)))
            = pinv_use ph w.maj st y h1 st1 fwd ys x;
              assert (in_use toy st1 h2 h2 x == in_use toy st1 h1 h1 x) in
          FStar.Classical.forall_intro n4;
          let n2 (o1 o2 c: nat) : Lemma (fwd o1 == Some c /\ fwd o2 == Some c ==> o1 == o2)
            = if fwd o1 = Some c then pinv_copy ph w.maj st y h1 st1 fwd ys o1 c in
          FStar.Classical.forall_intro_3 n2;
          assert (h2.size == w.maj.size);
          assert (toy.inv ph h2 st1 /\ well_formed h2);
          assert (minor_post_done toy ph st w.maj w h2 st1 (L.map (fwdv y fwd) w.roots) fwd h2)
    in
    FStar.Classical.move_requires pre ()
#pop-options

let tminor_at (ph: phase tprog) (st: tstate) (cw: cworld mheap mheap) : Lemma (minor_at toy_rep tminor ph st cw)
  = toy_rep_id ();
    let w = tview cw in
    tminor_m ph st w;
    FStar.Classical.forall_intro (alloc_fold_id toy_rep toy ph cw.cmaj st w.yng);
    (match tcollect ph st w with
     | OutOfRoom -> ()
     | Done h2 _ _ _ -> id_repr toy_rep h2 h2);
    assert (minor_m toy_rep tminor ph st cw w);
    forall_views_id toy_rep cw (minor_m toy_rep tminor ph st cw)

let toy_minor_ok () : Lemma (minor_ok toy_rep tminor)
  = FStar.Classical.forall_intro_3 tminor_at
