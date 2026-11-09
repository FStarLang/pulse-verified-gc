/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Blk - a stretch of the heap as a list of blocks
/// ---------------------------------------------------------------------------
///
/// The run sweep (`GC.Spec.Pages.SweepRun`) works on lists of blocks: the
/// blocks the walk finds in a run, the run after dead blocks are merged, and
/// after whole free pages are split off.  A block is a start, a size in
/// words and a tag: a survivor (`Live`), a free block (`Dead`) or a free page
/// (`Page`).
///
/// `contig bs a e`: the blocks `bs` lie end to end from `a` to `e`.  The
/// lemmas here read facts off such a list by membership: blocks are
/// disjoint and ordered, a block is found by its start (`blk_at`), every
/// block that ends before `e` is followed by another, and a list cut at two
/// of its starts (`slice`) is again end to end.
///
/// `tiles_steps` ties a list to the heap: when every block's header gives its
/// size, the walk from `a` steps to `e` and stops exactly at the starts.

module GC.Spec.Pages.Blk

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape

module U64 = FStar.UInt64
module L = FStar.List.Tot
module R = GC.Spec.Pages.Replace
module B = GC.Spec.Pages.Blocks

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

type tag = | Live | Dead | Page

type blk = { at: nat; w: pos; t: tag }

/// The end of a block, in bytes.
let bend (b: blk) : nat = b.at + b.w * 8

let rec contig (bs: list blk) (a e: nat) : Tot prop (decreases bs) =
  match bs with
  | [] -> a == e
  | b :: bs' -> b.at == a /\ contig bs' (bend b) e

/// The block that starts at `x`, if any.
let rec blk_at (bs: list blk) (x: nat) : Tot (option blk) (decreases bs) =
  match bs with
  | [] -> None
  | b :: bs' -> if b.at = x then Some b else blk_at bs' x

/// The blocks from the one starting at `x` on, and those before it.
let rec from_ (bs: list blk) (x: nat) : Tot (list blk) (decreases bs) =
  match bs with
  | [] -> []
  | b :: bs' -> if b.at < x then from_ bs' x else bs

let rec upto (bs: list blk) (x: nat) : Tot (list blk) (decreases bs) =
  match bs with
  | [] -> []
  | b :: bs' -> if b.at < x then b :: upto bs' x else []

/// The blocks between two starts.
let slice (bs: list blk) (x y: nat) : list blk = upto (from_ bs x) y

/// ---------------------------------------------------------------------------
/// End to end
/// ---------------------------------------------------------------------------

let rec contig_le (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e)
          (ensures a <= e /\ (Cons? bs ==> a + 8 <= e) /\ (a == e ==> bs == []))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' -> contig_le bs' (bend b) e

let rec contig_mem (bs: list blk) (a e: nat) (b: blk)
  : Lemma (requires contig bs a e /\ L.mem b bs)
          (ensures a <= b.at /\ bend b <= e)
          (decreases bs)
  = match bs with
    | c :: bs' ->
      contig_le bs' (bend c) e;
      if c = b then () else contig_mem bs' (bend c) e b

let rec contig_append (bs1 bs2: list blk) (a m e: nat)
  : Lemma (requires contig bs1 a m /\ contig bs2 m e)
          (ensures contig (L.append bs1 bs2) a e)
          (decreases bs1)
  = match bs1 with
    | [] -> ()
    | b :: bs' -> contig_append bs' bs2 (bend b) m e

let rec contig_aligned (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e /\ a % 8 == 0)
          (ensures e % 8 == 0 /\ (forall (b: blk). L.mem b bs ==> b.at % 8 == 0))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      FStar.Math.Lemmas.lemma_mod_plus a b.w 8;
      contig_aligned bs' (bend b) e

/// Two blocks of the list are the same or apart, in order.
let rec contig_order (bs: list blk) (a e: nat) (b1 b2: blk)
  : Lemma (requires contig bs a e /\ L.mem b1 bs /\ L.mem b2 bs)
          (ensures (b1.at == b2.at ==> b1 == b2) /\
                   (b1.at < b2.at ==> bend b1 <= b2.at))
          (decreases bs)
  = match bs with
    | c :: bs' ->
      if c = b1 && c = b2 then ()
      else if c = b1 then contig_mem bs' (bend c) e b2
      else if c = b2 then contig_mem bs' (bend c) e b1
      else contig_order bs' (bend c) e b1 b2

let rec blk_at_spec (bs: list blk) (a e: nat) (x: nat)
  : Lemma (requires contig bs a e)
          (ensures (match blk_at bs x with
                    | Some b -> L.mem b bs /\ b.at == x
                    | None -> forall (b: blk). L.mem b bs ==> b.at =!= x))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' -> blk_at_spec bs' (bend b) e x

/// A block is found by its start.
let blk_at_mem (bs: list blk) (a e: nat) (b: blk)
  : Lemma (requires contig bs a e /\ L.mem b bs)
          (ensures blk_at bs b.at == Some b)
  = blk_at_spec bs a e b.at;
    match blk_at bs b.at with
    | Some c -> contig_order bs a e b c
    | None -> ()

/// A block that ends before `e` is followed by another.
#push-options "--fuel 2"
let rec contig_next (bs: list blk) (a e: nat) (b: blk)
  : Lemma (requires contig bs a e /\ L.mem b bs /\ bend b < e)
          (ensures Some? (blk_at bs (bend b)))
          (decreases bs)
  = match bs with
    | c :: bs' ->
      if c = b then begin
        contig_le bs' (bend c) e;
        match bs' with
        | d :: _ -> ()
      end else begin
        contig_mem bs' (bend c) e b;
        contig_next bs' (bend c) e b
      end
#pop-options

/// The first block starts at `a`.
let contig_first (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e /\ a < e)
          (ensures Some? (blk_at bs a))
  = match bs with
    | [] -> ()
    | b :: _ -> ()

/// Every byte of `[a, e)` lies in a block.
let rec contig_cover (bs: list blk) (a e: nat) (x: nat)
  : Lemma (requires contig bs a e /\ a <= x /\ x < e)
          (ensures (exists (b: blk). L.mem b bs /\ b.at <= x /\ x < bend b))
          (decreases bs)
  = match bs with
    | b :: bs' -> if x < bend b then () else contig_cover bs' (bend b) e x

/// ---------------------------------------------------------------------------
/// Cutting at a start
/// ---------------------------------------------------------------------------

/// A start, or the end.
let cut (bs: list blk) (e: nat) (x: nat) : prop = x == e \/ Some? (blk_at bs x)

let rec from_spec (bs: list blk) (a e: nat) (x: nat)
  : Lemma (requires contig bs a e /\ cut bs e x /\ a <= x)
          (ensures contig (from_ bs x) x e /\
                   (forall (b: blk). L.mem b (from_ bs x) <==> L.mem b bs /\ b.at >= x))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      if b.at < x then begin
        if x = e then contig_le bs' (bend b) e;
        if x <> e then begin
          blk_at_spec bs a e x;
          let c = Some?.v (blk_at bs x) in
          contig_order bs a e b c
        end;
        contig_le bs' (bend b) e;
        blk_at_spec bs' (bend b) e x;
        from_spec bs' (bend b) e x;
        let aux (c: blk) : Lemma (L.mem c bs' ==> c.at > b.at)
          = if L.mem c bs' then contig_mem bs' (bend b) e c
        in
        FStar.Classical.forall_intro aux
      end else begin
        let aux (c: blk) : Lemma (L.mem c bs' ==> c.at > b.at)
          = if L.mem c bs' then contig_mem bs' (bend b) e c
        in
        FStar.Classical.forall_intro aux
      end

let rec upto_spec (bs: list blk) (a e: nat) (x: nat)
  : Lemma (requires contig bs a e /\ cut bs e x /\ a <= x)
          (ensures contig (upto bs x) a x /\
                   (forall (b: blk). L.mem b (upto bs x) <==> L.mem b bs /\ b.at < x))
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      let later (c: blk) : Lemma (L.mem c bs' ==> c.at > b.at)
        = if L.mem c bs' then contig_mem bs' (bend b) e c
      in
      FStar.Classical.forall_intro later;
      if b.at < x then begin
        contig_le bs' (bend b) e;
        if x <> e then begin
          blk_at_spec bs a e x;
          let c = Some?.v (blk_at bs x) in
          contig_order bs a e b c
        end;
        blk_at_spec bs' (bend b) e x;
        upto_spec bs' (bend b) e x
      end else ()

/// **The blocks between two cuts lie end to end between them.**
let slice_spec (bs: list blk) (a e: nat) (x y: nat)
  : Lemma (requires contig bs a e /\ cut bs e x /\ cut bs e y /\ a <= x /\ x <= y)
          (ensures contig (slice bs x y) x y /\
                   (forall (b: blk). L.mem b (slice bs x y) <==> L.mem b bs /\ x <= b.at /\ b.at < y))
  = from_spec bs a e x;
    let fs = from_ bs x in
    blk_at_spec bs a e y;
    blk_at_spec fs x e y;
    if y <> e then begin
      let c = Some?.v (blk_at bs y) in
      assert (L.mem c fs)
    end;
    upto_spec fs x e y

/// ---------------------------------------------------------------------------
/// The walk over a list
/// ---------------------------------------------------------------------------

/// Every block's header gives its size.
let hdrs_ok (g: heap) (bs: list blk) : prop =
  forall (b: blk). L.mem b bs ==> b.at % 8 == 0 /\ b.at < heap_size /\ words_at g b.at == b.w

/// **The walk over a list of blocks** steps from its start to its end and
/// stops exactly at the blocks' starts.
let rec tiles_steps (g: heap) (bs: list blk) (a e: nat)
  : Lemma (requires contig bs a e /\ e <= heap_size /\ hdrs_ok g bs)
          (ensures steps_to g a e /\
                   (forall (x: nat). (steps_to g a x /\ x < e) <==> Some? (blk_at bs x)))
          (decreases bs)
  = match bs with
    | [] ->
      steps_to_refl g a;
      let aux (x: nat) : Lemma (~(steps_to g a x /\ x < e))
        = if steps_to g a x then steps_to_le g a x
      in
      FStar.Classical.forall_intro aux
    | b :: bs' ->
      let m = bend b in
      contig_le bs' m e;
      block_steps g a b.w;
      tiles_steps g bs' m e;
      steps_to_trans g a m e;
      let aux (x: nat) : Lemma ((steps_to g a x /\ x < e) <==> Some? (blk_at bs x))
        = blk_at_spec bs' m e x;
          if x = a then steps_to_refl g a
          else begin
            if steps_to g a x && x < e then begin
              steps_to_le g a x;
              if x < m then B.one_block_pos g a x
              else R.steps_to_det g a m x
            end;
            if Some? (blk_at bs' x) then begin
              let c = Some?.v (blk_at bs' x) in
              contig_mem bs' m e c;
              steps_to_trans g a m x
            end
          end
      in
      FStar.Classical.forall_intro aux
