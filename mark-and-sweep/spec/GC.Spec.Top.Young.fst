/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Young - the nursery of GC.Gen.MinorHeap, read as the model
/// ---------------------------------------------------------------------------
///
/// The nursery is GC.Gen.MinorHeap's `minor_state`: bytes and a bump pointer,
/// its objects laid out from offset 0 to the bump pointer.  `yabs ms` reads it
/// as a model nursery: model word `j` is the word at offset `8 j`; a block
/// starts at `j` exactly when the walk from 0 to the bump pointer lands on
/// `8 j` (`yat`); headers and words are read as in the major heap
/// (GC.Spec.Top.Word).  The representation relation is `yrepr m ms`: the
/// walk runs from 0 to the bump pointer (`yok`) and `m` is, word by word, the
/// canonical reading `ycabs ms` (`yabs ms` with the words outside fields read
/// as 0); the bytes past the bump pointer are not read.
///
/// The program's operations: `yinit` and `yreset` are GC.Gen.MinorHeap's
/// `minor_init` (of a zeroed nursery) and `minor_reset`; `ywrite` is
/// `minor_write_word` at a field; `yalloc` bump-allocates (a white header,
/// then the fields), as `minor_alloc_spec` does for objects up to
/// `max_young_wosize`.
///
/// Proved:
///   - the reads are the model's (`yrepr_reads`);
///   - the operations are the model's, lifted (`yinit_ok'`, `yreset_ok'`,
///     `ywrite_ok'`, `yalloc_ok'`), and allocation fails only when the object
///     is too big or the nursery has no room;
///   - blocks are GC.Gen.MinorHeap's objects: `Seq.mem x (minor_objects ms)`
///     exactly when the walk lands on `x - 8` (`young_objects`), and the walk
///     makes the state `minor_wf`;
///   - young pointers resolve as `resolve_minor` does, through infix headers
///     included (`young_resolve`).

module GC.Spec.Top.Young

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module U64 = FStar.UInt64
module U8 = FStar.UInt8
module Seq = FStar.Seq
module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let msz () : Lemma (minor_heap_size < pow2 64) = assert_norm (pow2 57 < pow2 64)

/// A word offset of the nursery.
let ok_pos (p: nat) : bool = p % 8 = 0 && p + 8 <= minor_heap_size

[@@"opaque_to_smt"]
let yw (d: minor_heap) (p: nat) : U64.t =
  if ok_pos p then (msz (); minor_read_word d (U64.uint_to_t p)) else 0UL

let wz_at (d: minor_heap) (p: nat) : nat = U64.v (getWosize (yw d p))

/// ---------------------------------------------------------------------------
/// Words: reading after writing
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let mwrite (d: minor_heap) (p: nat) (v: U64.t) : minor_heap =
  if ok_pos p then (msz (); minor_write_word d (U64.uint_to_t p) v) else d

let minor_combine_eq (b0 b1 b2 b3 b4 b5 b6 b7: U8.t)
  : Lemma (minor_combine_bytes b0 b1 b2 b3 b4 b5 b6 b7 == combine_bytes b0 b1 b2 b3 b4 b5 b6 b7) = ()

#push-options "--z3rlimit 40"
let mrw_same (d: minor_heap) (p: nat) (v: U64.t)
  : Lemma (requires ok_pos p) (ensures yw (mwrite d p v) p == v)
  = msz ();
    reveal_opaque (`%yw) yw;
    reveal_opaque (`%mwrite) mwrite;
    let d' = mwrite d p v in
    minor_combine_eq (Seq.index d' p) (Seq.index d' (p + 1)) (Seq.index d' (p + 2)) (Seq.index d' (p + 3))
                     (Seq.index d' (p + 4)) (Seq.index d' (p + 5)) (Seq.index d' (p + 6)) (Seq.index d' (p + 7));
    combine_decompose_identity v

#pop-options

/// A write changes only its own eight bytes.
let byte_frame (d: minor_heap) (p: nat) (v: U64.t) (i: nat)
  : Lemma (requires ok_pos p /\ i < minor_heap_size /\ (i < p \/ i >= p + 8))
          (ensures Seq.index (mwrite d p v) i == Seq.index d i)
  = msz ();
    reveal_opaque (`%mwrite) mwrite

#push-options "--z3rlimit 40"
let mrw_other (d: minor_heap) (p q: nat) (v: U64.t)
  : Lemma (requires ok_pos p /\ p <> q) (ensures yw (mwrite d p v) q == yw d q)
  = msz ();
    reveal_opaque (`%yw) yw;
    if ok_pos q then begin
      let f (k: nat{k < 8}) : Lemma (Seq.index (mwrite d p v) (q + k) == Seq.index d (q + k))
        = byte_frame d p v (q + k) in
      f 0; f 1; f 2; f 3; f 4; f 5; f 6; f 7
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The walk
/// ---------------------------------------------------------------------------

let next (d: minor_heap) (p: nat) : nat = p + 8 * (wz_at d p + 1)

let next_facts (d: minor_heap) (p: nat)
  : Lemma (next d p >= p + 8 /\ (p % 8 == 0 ==> next d p % 8 == 0)) [SMTPat (next d p)]
  = ()

/// The walk from `p` lands exactly on `b`, every block with a field and none
/// with the infix tag.
let rec ychain (d: minor_heap) (p b: nat) : Tot bool (decreases (if p < b then b - p else 0)) =
  if p = b then true
  else if p > b || not (ok_pos p) then false
  else wz_at d p > 0 && U64.v (getTag (yw d p)) <> 249 && ychain d (next d p) b

/// The walk from `p` to `b` lands on `q`.
let rec yat (d: minor_heap) (p b q: nat) : Tot bool (decreases (if p < b then b - p else 0)) =
  if p >= b || not (ok_pos p) then false
  else if p = q then true
  else wz_at d p > 0 && yat d (next d p) b q

let yat_unfold (d: minor_heap) (p b q: nat)
  : Lemma (requires p < b /\ ok_pos p /\ p <> q) (ensures yat d p b q == (wz_at d p > 0 && yat d (next d p) b q))
  = ()

let chain_unfold (d: minor_heap) (p b: nat)
  : Lemma (requires ychain d p b /\ p <> b)
          (ensures p < b /\ ok_pos p /\ wz_at d p > 0 /\ U64.v (getTag (yw d p)) <> 249 /\ ychain d (next d p) b)
  = ()

let rec chain_le (d: minor_heap) (p b: nat)
  : Lemma (requires ychain d p b) (ensures p <= b) (decreases (if p < b then b - p else 0))
  = if p < b then chain_le d (next d p) b

let rec yat_facts (d: minor_heap) (p b q: nat)
  : Lemma (requires ychain d p b /\ yat d p b q)
          (ensures p <= q /\ q < b /\ ok_pos q /\ wz_at d q > 0 /\ U64.v (getTag (yw d q)) <> 249 /\
                   next d q <= b /\ (p % 8 == 0 ==> q % 8 == 0))
          (decreases (if p < b then b - p else 0))
  = if p = q then chain_le d (next d p) b
    else begin
      assert (next d p > p /\ (p % 8 == 0 ==> next d p % 8 == 0));
      assert (ychain d (next d p) b /\ yat d (next d p) b q);
      yat_facts d (next d p) b q
    end

let rec yat_before (d: minor_heap) (p b q1 q2: nat)
  : Lemma (requires ychain d p b /\ yat d p b q1 /\ yat d p b q2 /\ q1 < q2)
          (ensures next d q1 <= q2)
          (decreases (if p < b then b - p else 0))
  = chain_unfold d p b;
    yat_facts d p b q1;
    if p = q1 then begin
      yat_unfold d p b q2;
      yat_facts d (next d p) b q2
    end
    else begin
      yat_unfold d p b q1;
      yat_facts d p b q2;
      if p = q2 then () else yat_unfold d p b q2;
      yat_before d (next d p) b q1 q2
    end

let rec yat_cover (d: minor_heap) (p b r: nat)
  : Lemma (requires ychain d p b /\ p <= r /\ r < b)
          (ensures exists (q: nat). yat d p b q /\ q <= r /\ r < next d q)
          (decreases (if p < b then b - p else 0))
  = if r < next d p then assert (yat d p b p)
    else begin
      yat_cover d (next d p) b r;
      let q = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun q -> yat d (next d p) b q /\ q <= r /\ r < next d q) in
      assert (yat d p b q)
    end

/// Two nurseries that agree on the walk's words have the same walk.
let rec chain_frame (d d': minor_heap) (p b: nat)
  : Lemma (requires ychain d p b /\ (forall (q: nat). yat d p b q ==> yw d' q == yw d q))
          (ensures ychain d' p b /\ (forall (q: nat). yat d' p b q == yat d p b q))
          (decreases (if p < b then b - p else 0))
  = if p < b then begin
      assert (yat d p b p);
      let aux (q: nat) : Lemma (yat d (next d p) b q ==> yat d p b q) = () in
      FStar.Classical.forall_intro aux;
      chain_frame d d' (next d p) b
    end

let chain_cons (d: minor_heap) (p b: nat)
  : Lemma (requires p < b /\ ok_pos p /\ wz_at d p > 0 /\ U64.v (getTag (yw d p)) <> 249 /\ ychain d (next d p) b)
          (ensures ychain d p b)
  = ()

let yat_here (d: minor_heap) (p b: nat) : Lemma (requires p < b /\ ok_pos p) (ensures yat d p b p) = ()

let yat_empty (d: minor_heap) (p q: nat) : Lemma (yat d p p q == false) = ()

let chain_refl (d: minor_heap) (p: nat) : Lemma (ychain d p p) = ()

/// Extending the walk by the block at its end.
let rec chain_snoc (d: minor_heap) (p b: nat)
  : Lemma (requires ychain d p b /\ ok_pos b /\ wz_at d b > 0 /\ U64.v (getTag (yw d b)) <> 249)
          (ensures ychain d p (next d b) /\ (forall (q: nat). yat d p (next d b) q == (yat d p b q || q = b)))
          (decreases (if p < b then b - p else 0))
  = let b' = next d b in
    if p = b then begin
      chain_cons d b b';
      let aux (q: nat) : Lemma (yat d p b' q == (yat d p b q || q = b))
        = yat_empty d b q;
          if q <> b then (yat_unfold d b b' q; yat_empty d b' q) in
      FStar.Classical.forall_intro aux
    end
    else begin
      chain_unfold d p b;
      chain_snoc d (next d p) b;
      chain_cons d p b';
      let aux (q: nat) : Lemma (yat d p b' q == (yat d p b q || q = b))
        = if q = p then (yat_here d p b; yat_here d p b')
          else (yat_unfold d p b q; yat_unfold d p b' q) in
      FStar.Classical.forall_intro aux
    end

/// ---------------------------------------------------------------------------
/// The nursery, read as the model
/// ---------------------------------------------------------------------------

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let ymw (ms: minor_state) (j: nat) : U64.t = yw ms.data (8 * j)

let yhd_of (ms: minor_state) (j: nat) : option M.header =
  if yat ms.data 0 (U64.v ms.bump) (8 * j) then Some (abs_hdr (ymw ms j)) else None

let ybody (ms: minor_state) (j: nat) : M.value = absv (ymw ms j)

let yabs (ms: minor_state) : M.mheap = { M.size = ywords; M.hd = yhd_of ms; M.body = ybody ms }

/// The words at and past `b` are zero (G38: the nursery is cleared when
/// reset, and allocation and writes stay below the bump pointer).
[@@"opaque_to_smt"]
let zero_past (d: minor_heap) (b: nat) : prop = forall (q: nat). ok_pos q /\ b <= q ==> yw d q == 0UL

let zero_past_def (d: minor_heap) (b: nat)
  : Lemma (zero_past d b <==> (forall (q: nat). ok_pos q /\ b <= q ==> yw d q == 0UL))
  = reveal_opaque (`%zero_past) (zero_past d b)

[@@"opaque_to_smt"]
let yok (ms: minor_state) : prop =
  U64.v ms.bump % 8 == 0 /\ U64.v ms.bump <= minor_heap_size /\ ychain ms.data 0 (U64.v ms.bump) /\
  zero_past ms.data (U64.v ms.bump)

let yok_elim (ms: minor_state)
  : Lemma (requires yok ms)
          (ensures U64.v ms.bump % 8 == 0 /\ U64.v ms.bump <= minor_heap_size /\ ychain ms.data 0 (U64.v ms.bump) /\
                   zero_past ms.data (U64.v ms.bump))
  = reveal_opaque (`%yok) (yok ms)

let yok_intro (ms: minor_state)
  : Lemma (requires U64.v ms.bump % 8 == 0 /\ U64.v ms.bump <= minor_heap_size /\ ychain ms.data 0 (U64.v ms.bump) /\
                    zero_past ms.data (U64.v ms.bump))
          (ensures yok ms)
  = reveal_opaque (`%yok) (yok ms)

/// A nursery of zero bytes.
let zero_data (q: nat)
  : Lemma (yw (Seq.create minor_heap_size 0uy) q == 0UL)
  = reveal_opaque (`%yw) yw;
    if ok_pos q then begin msz (); minor_read_word_zero_heap (U64.uint_to_t q) end

/// The canonical reading: the words outside fields read as 0.
let rec yfw_below (ms: minor_state) (w n: nat) : bool =
  if n = 0 then false
  else (let x = n - 1 in
        x < w && x < ywords && yat ms.data 0 (U64.v ms.bump) (8 * x) && w <= x + wz_at ms.data (8 * x)) ||
       yfw_below ms w (n - 1)

let ycabs_body (ms: minor_state) (w: nat) : M.value = if yfw_below ms w w then ybody ms w else M.VInt 0

let ycabs_hd (ms: minor_state) (j: nat) : option M.header = if j < ywords then yhd_of ms j else None

let ycabs (ms: minor_state) : M.mheap = { M.size = ywords; M.hd = ycabs_hd ms; M.body = ycabs_body ms }

let yfw_one (ms: minor_state) (w x: nat)
  : Lemma ((x < w && x < ywords && yat ms.data 0 (U64.v ms.bump) (8 * x) && w <= x + wz_at ms.data (8 * x)) <==>
           (x < w /\ M.covers (yabs ms) x w))
  = ()

#push-options "--fuel 1"
let rec yfw_intro (ms: minor_state) (w n x: nat)
  : Lemma (requires x < n /\ x < w /\ M.covers (yabs ms) x w) (ensures yfw_below ms w n) (decreases n)
  = yfw_one ms w x;
    if x = n - 1 then () else yfw_intro ms w (n - 1) x

let rec yfw_elim (ms: minor_state) (w n: nat)
  : Lemma (requires yfw_below ms w n) (ensures exists (x: nat). x < n /\ x < w /\ M.covers (yabs ms) x w)
          (decreases n)
  = let x = n - 1 in
    yfw_one ms w x;
    if x < w && x < ywords && yat ms.data 0 (U64.v ms.bump) (8 * x) && w <= x + wz_at ms.data (8 * x) then ()
    else yfw_elim ms w (n - 1)

#pop-options

let yfw_iff (ms: minor_state) (w: nat) : Lemma (yfw_below ms w w <==> R.field_word (yabs ms) w)
  = FStar.Classical.move_requires (yfw_elim ms w) w;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (yfw_intro ms w w))

let ycabs_facts (ms: minor_state)
  : Lemma (R.agree (ycabs ms) (yabs ms) /\ R.agree (yabs ms) (ycabs ms) /\ R.canonical (ycabs ms))
  = FStar.Classical.forall_intro (yfw_iff ms);
    R.agree_sym (ycabs ms) (yabs ms);
    let bd (w: nat) : Lemma (~(R.field_word (ycabs ms) w) ==> ycabs_body ms w == M.VInt 0)
      = R.agree_field_word (ycabs ms) (yabs ms) w in
    FStar.Classical.forall_intro bd

/// The representation: the walk runs from 0 to the bump pointer, and `m` is
/// the canonical reading, word by word.
[@@"opaque_to_smt"]
let yrepr (m: M.mheap) (ms: minor_state) : prop = yok ms /\ R.heq m (ycabs ms)

let yrepr_elim (m: M.mheap) (ms: minor_state)
  : Lemma (requires yrepr m ms) (ensures yok ms /\ R.agree m (yabs ms) /\ R.canonical m)
  = reveal_opaque (`%yrepr) (yrepr m ms);
    ycabs_facts ms;
    R.heq_agree m (ycabs ms);
    R.agree_trans m (ycabs ms) (yabs ms);
    R.heq_sym m (ycabs ms);
    R.canonical_heq (ycabs ms) m

let yrepr_intro (m: M.mheap) (ms: minor_state)
  : Lemma (requires yok ms /\ R.agree m (yabs ms) /\ R.canonical m) (ensures yrepr m ms)
  = ycabs_facts ms;
    R.agree_trans m (yabs ms) (ycabs ms);
    R.agree_canonical m (ycabs ms);
    reveal_opaque (`%yrepr) (yrepr m ms)

let yread (ms: minor_state) (o i: nat) : GTot M.value = absv (ymw ms (o + 1 + i))

let yhd (ms: minor_state) (o: nat) : GTot (option M.header) = yhd_of ms o

let ysz (ms: minor_state) : GTot nat = ywords

let mul8 (o wz: nat) : Lemma (8 * o + 8 * (wz + 1) == 8 * (o + wz + 1)) = ()

/// A block of the model nursery is a block of the walk.
#push-options "--z3rlimit 40"
let yblock (ms: minor_state) (o: nat)
  : Lemma (requires yok ms /\ M.is_block (yabs ms) o)
          (ensures (let d = ms.data in let b = U64.v ms.bump in
                    yat d 0 b (8 * o) /\ M.wz_of (yabs ms) o == wz_at d (8 * o) /\
                    next d (8 * o) == 8 * (o + M.wz_of (yabs ms) o + 1) /\ next d (8 * o) <= b /\
                    M.wz_of (yabs ms) o > 0 /\ M.tag_of (yabs ms) o <> M.infix_tag))
  = let d = ms.data in
    let b = U64.v ms.bump in
    yok_elim ms;
    assert ((yabs ms).M.hd o == yhd_of ms o);
    assert (Some? (yhd_of ms o));
    assert (yat d 0 b (8 * o));
    yat_facts d 0 b (8 * o);
    assert (M.hdr_of (yabs ms) o == abs_hdr (yw d (8 * o)));
    let wz = wz_at d (8 * o) in
    assert (M.wz_of (yabs ms) o == wz);
    assert (next d (8 * o) == 8 * o + 8 * (wz + 1));
    mul8 o wz;
    assert (next d (8 * o) == 8 * (o + M.wz_of (yabs ms) o + 1))
#pop-options

let yrepr_field (m: M.mheap) (ms: minor_state) (o i: nat)
  : Lemma (requires R.agree m (yabs ms) /\ M.is_block m o /\ i < M.wz_of m o)
          (ensures yread ms o i == M.field m o i)
  = let w = o + 1 + i in
    assert (m.M.hd o == (yabs ms).M.hd o);
    assert (M.is_block (yabs ms) o /\ M.wz_of (yabs ms) o == M.wz_of m o);
    assert (M.covers (yabs ms) o w);
    assert (R.field_word (yabs ms) w);
    assert (m.M.body w == ybody ms w)

let yrepr_reads (m: M.mheap) (ms: minor_state)
  : Lemma (requires yrepr m ms) (ensures R.reads_model (ysz ms) (yhd ms) (yread ms) m)
  = yrepr_elim m ms;
    let f (o i: nat) : Lemma (M.is_block m o /\ i < M.wz_of m o ==> yread ms o i == M.field m o i)
      = if M.is_block m o && i < M.wz_of m o then yrepr_field m ms o i in
    FStar.Classical.forall_intro_2 f

/// ---------------------------------------------------------------------------
/// The empty nursery
/// ---------------------------------------------------------------------------

let empty_agree (ms: minor_state) (n: nat)
  : Lemma (requires U64.v ms.bump == 0 /\ n == ywords /\ ms.data == Seq.create minor_heap_size 0uy)
          (ensures yrepr (M.empty_heap n) ms)
  = chain_refl ms.data 0;
    FStar.Classical.forall_intro zero_data;
    zero_past_def ms.data 0;
    yok_intro ms;
    FStar.Classical.forall_intro (yat_empty ms.data 0);
    let nb (x: nat) : Lemma (~(M.is_block (yabs ms) x)) = yat_empty ms.data 0 (8 * x) in
    FStar.Classical.forall_intro nb;
    let f (w: nat) : Lemma (~(R.field_word (yabs ms) w)) = () in
    FStar.Classical.forall_intro f;
    R.canonical_empty n;
    yrepr_intro (M.empty_heap n) ms

let yinit (n: nat) : GTot minor_state = minor_init (Seq.create minor_heap_size 0uy)

let yinit_ok' (n: nat) : Lemma (requires n == ywords) (ensures yrepr (M.empty_heap n) (yinit n))
  = empty_agree (yinit n) n

let yreset (ms: minor_state) : GTot minor_state = minor_reset ms

let yreset_ok' (m: M.mheap) (ms: minor_state)
  : Lemma (requires yrepr m ms) (ensures yrepr (M.empty_heap m.M.size) (yreset ms))
  = yrepr_elim m ms;
    empty_agree (yreset ms) m.M.size

/// ---------------------------------------------------------------------------
/// A write to a field
/// ---------------------------------------------------------------------------

let ywrite (ms: minor_state) (o i: nat) (v: M.value) : GTot minor_state =
  { ms with data = mwrite ms.data (8 * (o + 1 + i)) (concv v) }

let field_pos (o i wz: nat)
  : Lemma (requires i < wz)
          (ensures 8 * o < 8 * (o + 1 + i) /\ 8 * (o + 1 + i) + 8 <= 8 * (o + wz + 1) /\ (8 * (o + 1 + i)) % 8 == 0)
  = ()

let mul8_inj (a b: nat) : Lemma (requires a <> b) (ensures 8 * a <> 8 * b) = ()

let fld_bump (d: minor_heap) (b o wz i: nat)
  : Lemma (requires i < wz /\ 8 * o + 8 * (wz + 1) <= b) (ensures 8 * (o + 1 + i) + 8 <= b) = ()

let write_zero_past (d: minor_heap) (p: nat) (v: U64.t) (b: nat)
  : Lemma (requires zero_past d b /\ ok_pos p /\ p + 8 <= b) (ensures zero_past (mwrite d p v) b)
  = zero_past_def d b;
    zero_past_def (mwrite d p v) b;
    let zp (q: nat) : Lemma (ok_pos q /\ b <= q ==> yw (mwrite d p v) q == yw d q)
      = if ok_pos q && b <= q then mrw_other d p q v in
    FStar.Classical.forall_intro zp

let frame_zero_past (d d2: minor_heap) (b b': nat)
  : Lemma (requires zero_past d b /\ b <= b' /\ (forall (q: nat). ok_pos q /\ b' <= q ==> yw d2 q == yw d q))
          (ensures zero_past d2 b')
  = zero_past_def d b;
    zero_past_def d2 b'

/// The write, on the nursery's own reading: a store into the field.
#push-options "--z3rlimit 40"
let ywrite_abs (ms: minor_state) (o i: nat) (v: M.value)
  : Lemma (requires yok ms /\ M.is_block (yabs ms) o /\ i < M.wz_of (yabs ms) o /\ storable_w v)
          (ensures yok (ywrite ms o i v) /\ R.agree (M.set_field (yabs ms) o i v) (yabs (ywrite ms o i v)))
  = let d = ms.data in
    let b = U64.v ms.bump in
    let p = 8 * (o + 1 + i) in
    let ms' = ywrite ms o i v in
    let d' = ms'.data in
    yok_elim ms;
    yblock ms o;
    field_pos o i (M.wz_of (yabs ms) o);
    assert (ok_pos p);
    let fr (q: nat) : Lemma (yat d 0 b q ==> yw d' q == yw d q)
      = if yat d 0 b q then begin
          if q = p then yat_before d 0 b (8 * o) p
          else mrw_other d p q (concv v)
        end in
    FStar.Classical.forall_intro fr;
    chain_frame d d' 0 b;
    fld_bump d b o (M.wz_of (yabs ms) o) i;
    write_zero_past d p (concv v) b;
    yok_intro ms';
    mrw_same d p (concv v);
    absv_concv v;
    let hd (j: nat) : Lemma (yhd_of ms' j == yhd_of ms j) = () in
    FStar.Classical.forall_intro hd;
    let bd (w: nat) : Lemma (ybody ms' w == (if w = o + 1 + i then v else ybody ms w))
      = if w <> o + 1 + i then (mul8_inj w (o + 1 + i); mrw_other d p (8 * w) (concv v)) in
    FStar.Classical.forall_intro bd
#pop-options

let ywrite_ok' (m: M.mheap) (ms: minor_state) (o i: nat) (v: M.value)
  : Lemma (requires yrepr m ms /\ M.is_block m o /\ i < M.wz_of m o /\ storable_w v)
          (ensures yrepr (M.set_field m o i v) (ywrite ms o i v))
  = yrepr_elim m ms;
    R.agree_blocks m (yabs ms) o;
    ywrite_abs ms o i v;
    R.agree_set_field m (yabs ms) o i v;
    R.agree_trans (M.set_field m o i v) (M.set_field (yabs ms) o i v) (yabs (ywrite ms o i v));
    R.canonical_set_field m o i v;
    yrepr_intro (M.set_field m o i v) (ywrite ms o i v)

/// ---------------------------------------------------------------------------
/// Allocation
/// ---------------------------------------------------------------------------

let rec write_fields (d: minor_heap) (p: nat) (vs: list M.value) : Tot minor_heap (decreases vs) =
  match vs with
  | [] -> d
  | v :: tl -> write_fields (mwrite d p (concv v)) (p + 8) tl

let aligned_gap (p q: nat) : Lemma (requires p % 8 == 0 /\ q % 8 == 0 /\ p < q) (ensures p + 8 <= q) = ()

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec write_fields_read (d: minor_heap) (p: nat) (vs: list M.value) (q: nat)
  : Lemma (requires p % 8 == 0 /\ p + 8 * L.length vs <= minor_heap_size /\ ok_pos q)
          (ensures yw (write_fields d p vs) q ==
                   (if p <= q && q < p + 8 * L.length vs then concv (L.index vs ((q - p) / 8)) else yw d q))
          (decreases vs)
  = match vs with
    | [] -> ()
    | v :: tl ->
      let d1 = mwrite d p (concv v) in
      assert (write_fields d p vs == write_fields d1 (p + 8) tl);
      assert (L.length vs == L.length tl + 1);
      write_fields_read d1 (p + 8) tl q;
      if q = p then begin
        mrw_same d p (concv v);
        assert (L.index vs 0 == v)
      end
      else begin
        mrw_other d p q (concv v);
        if p < q then aligned_gap p q;
        if p + 8 <= q && q < p + 8 * L.length vs then begin
          FStar.Math.Lemmas.lemma_div_plus (q - (p + 8)) 1 8;
          assert ((q - p) / 8 == (q - (p + 8)) / 8 + 1);
          assert (L.index vs ((q - p) / 8) == L.index tl ((q - (p + 8)) / 8))
        end
      end
#pop-options

let white_hdr (sz: M.size_t) (tag: M.tag_t) : M.header = { M.wz = sz; M.tag = tag; M.col = M.White }

let yalloc (ms: minor_state) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) : GTot (option (nat & minor_state)) =
  let b = U64.v ms.bump in
  if sz <= max_young_wosize && b % 8 = 0 && b + 8 * (sz + 1) <= minor_heap_size then begin
    msz ();
    let d1 = mwrite ms.data b (enc_hdr (white_hdr sz tag)) in
    let d2 = write_fields d1 (b + 8) vs in
    Some (b / 8, { data = d2; bump = U64.uint_to_t (b + 8 * (sz + 1)) })
  end
  else None

/// No block of the nursery covers a word at or past its bump pointer; every
/// word below it is covered.
let past_bump (ms: minor_state) (x w: nat)
  : Lemma (requires yok ms /\ M.covers (yabs ms) x w) (ensures 8 * w < U64.v ms.bump)
  = yblock ms x

let below_bump (ms: minor_state) (w: nat)
  : Lemma (requires yok ms /\ 8 * w < U64.v ms.bump) (ensures exists (x: nat). M.covers (yabs ms) x w)
  = let d = ms.data in
    let b = U64.v ms.bump in
    yok_elim ms;
    yat_cover d 0 b (8 * w);
    let q = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun q -> yat d 0 b q /\ q <= 8 * w /\ 8 * w < next d q) in
    yat_facts d 0 b q;
    let x = q / 8 in
    assert (q == 8 * x);
    yblock ms x;
    assert (M.covers (yabs ms) x w)

let no_room_arith (b o: nat) (sz: M.size_t)
  : Lemma (requires b <= 8 * o /\ b + 8 * (sz + 1) > minor_heap_size /\ 8 * ywords == minor_heap_size)
          (ensures ~(o + sz < ywords))
  = ()

let yalloc_none (m: M.mheap) (ms: minor_state) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires yrepr m ms /\ yalloc ms sz tag vs == None)
          (ensures sz > max_young_wosize \/ ~(exists (o: nat). M.young_free m o sz))
  = yrepr_elim m ms;
    yok_elim ms;
    if sz <= max_young_wosize then begin
      let b = U64.v ms.bump in
      assert (b + 8 * (sz + 1) > minor_heap_size);
      base_facts ();
      let aux (o: nat) : Lemma (~(M.young_free m o sz))
        = if 8 * o < b then begin
            below_bump ms o;
            let x = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun x -> M.covers (yabs ms) x o) in
            R.agree_covers m (yabs ms) x o
          end
          else no_room_arith b o sz in
      FStar.Classical.forall_intro aux
    end

let below_arith (w o b: nat) : Lemma (requires 8 * w < b /\ b == 8 * o) (ensures w < o) = ()

let fits_arith (b o: nat) (sz: M.size_t)
  : Lemma (requires b == 8 * o /\ b + 8 * (sz + 1) <= minor_heap_size /\ 8 * ywords == minor_heap_size)
          (ensures o + sz < ywords)
  = ()

let yalloc_free (m: M.mheap) (ms: minor_state) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires yrepr m ms /\ Some? (yalloc ms sz tag vs))
          (ensures M.young_free m (fst (Some?.v (yalloc ms sz tag vs))) sz)
  = yrepr_elim m ms;
    yok_elim ms;
    base_facts ();
    let b = U64.v ms.bump in
    let o = b / 8 in
    assert (fst (Some?.v (yalloc ms sz tag vs)) == o);
    FStar.Math.Lemmas.lemma_div_exact b 8;
    fits_arith b o sz;
    let aux (x w: nat) : Lemma (M.covers m x w ==> ~(o <= w /\ w <= o + sz))
      = R.agree_covers m (yabs ms) x w;
        if M.covers m x w then (past_bump ms x w; below_arith w o b) in
    FStar.Classical.forall_intro_2 aux

let sz_bound (sz: nat) : Lemma (requires 8 * (sz + 1) <= minor_heap_size) (ensures sz < pow2 54)
  = assert_norm (pow2 57 == 8 * pow2 54)

let fld_arith (w x wz b: nat)
  : Lemma (requires w <= x + wz /\ 8 * x + 8 * (wz + 1) <= b /\ b <= minor_heap_size)
          (ensures 8 * w + 8 <= b /\ ok_pos (8 * w))
  = ()

/// The allocation, on the nursery's own reading: a young allocation.
#push-options "--z3rlimit 40"
let yalloc_abs (ms: minor_state) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires yok ms /\ Some? (yalloc ms sz tag vs) /\ tag <> M.infix_tag /\ L.length vs == sz /\
                    (forall (v: M.value). L.memP v vs ==> storable_w v))
          (ensures (let Some (o, ms') = yalloc ms sz tag vs in
                    yok ms' /\ R.agree (M.young_alloc (yabs ms) o sz tag vs) (yabs ms')))
  = let d = ms.data in
    let b = U64.v ms.bump in
    yok_elim ms;
    let o = b / 8 in
    let Some (_, ms') = yalloc ms sz tag vs in
    let d1 = mwrite d b (enc_hdr (white_hdr sz tag)) in
    let d2 = ms'.data in
    let b' = b + 8 * (sz + 1) in
    FStar.Math.Lemmas.lemma_div_exact b 8;
    assert (U64.v ms'.bump == b' /\ b == 8 * o);
    sz_bound sz;
    abs_hdr_enc (white_hdr sz tag);
    let rd (q: nat) : Lemma (ok_pos q ==>
                             yw d2 q == (if q < b then yw d q
                                         else if q = b then enc_hdr (white_hdr sz tag)
                                         else if q < b' then concv (L.index vs ((q - b - 8) / 8))
                                         else yw d q))
      = if ok_pos q then begin
          write_fields_read d1 (b + 8) vs q;
          if q = b then mrw_same d b (enc_hdr (white_hdr sz tag))
          else mrw_other d b q (enc_hdr (white_hdr sz tag))
        end in
    FStar.Classical.forall_intro rd;
    let fr (q: nat) : Lemma (yat d 0 b q ==> yw d2 q == yw d q)
      = if yat d 0 b q then yat_facts d 0 b q in
    FStar.Classical.forall_intro fr;
    chain_frame d d2 0 b;
    assert (wz_at d2 b == sz /\ next d2 b == b');
    chain_snoc d2 0 b;
    frame_zero_past d d2 b b';
    yok_intro ms';
    let ya = M.young_alloc (yabs ms) o sz tag vs in
    let hd (j: nat) : Lemma (ya.M.hd j == yhd_of ms' j)
      = if 8 * j < b && yat d 0 b (8 * j) then yat_facts d 0 b (8 * j);
        if j = o then () else mul8_inj j o in
    FStar.Classical.forall_intro hd;
    let bd (w x: nat) : Lemma (requires M.covers (yabs ms') x w /\ x < w) (ensures ya.M.body w == ybody ms' w)
      = yblock ms' x;
        if x = o then begin
          L.lemma_index_memP vs (w - o - 1);
          absv_concv (L.index vs (w - o - 1));
          assert ((8 * w - b - 8) / 8 == w - o - 1)
        end
        else begin
          mul8_inj x o;
          assert (yat d2 0 b (8 * x));
          assert (yat d 0 b (8 * x));
          yat_facts d 0 b (8 * x);
          assert (yw d2 (8 * x) == yw d (8 * x));
          fld_arith w x (wz_at d (8 * x)) b;
          assert (yw d2 (8 * w) == yw d (8 * w))
        end in
    let bd' (w: nat) : Lemma (R.field_word (yabs ms') w ==> ya.M.body w == ybody ms' w)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (bd w)) in
    FStar.Classical.forall_intro bd'
#pop-options

let yalloc_repr (m: M.mheap) (ms: minor_state) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (requires yrepr m ms /\ Some? (yalloc ms sz tag vs) /\ tag <> M.infix_tag /\ L.length vs == sz /\
                    (forall (v: M.value). L.memP v vs ==> storable_w v))
          (ensures (let Some (o, ms') = yalloc ms sz tag vs in yrepr (M.young_alloc m o sz tag vs) ms'))
  = yrepr_elim m ms;
    yok_elim ms;
    base_facts ();
    let Some (o, ms') = yalloc ms sz tag vs in
    FStar.Math.Lemmas.lemma_div_exact (U64.v ms.bump) 8;
    fits_arith (U64.v ms.bump) o sz;
    yalloc_abs ms sz tag vs;
    R.agree_young_alloc m (yabs ms) o sz tag vs;
    R.agree_trans (M.young_alloc m o sz tag vs) (M.young_alloc (yabs ms) o sz tag vs) (yabs ms');
    yalloc_free m ms sz tag vs;
    R.canonical_young_alloc m o sz tag vs;
    yrepr_intro (M.young_alloc m o sz tag vs) ms'

/// ---------------------------------------------------------------------------
/// The nursery's blocks are GC.Gen.MinorHeap's objects
/// ---------------------------------------------------------------------------

let yw_read (d: minor_heap) (p: nat)
  : Lemma (requires ok_pos p)
          (ensures (msz (); yw d p == minor_read_word d (U64.uint_to_t p)))
  = reveal_opaque (`%yw) yw

let step_shape (d: minor_heap) (p: nat)
  : Lemma (requires ok_pos p)
          (ensures (msz ();
                    let hdr = minor_read_word d (U64.uint_to_t p) in
                    U64.v (U64.shift_right hdr 10ul) == wz_at d p /\
                    next d p == p + (U64.v (U64.shift_right hdr 10ul) + 1) * 8 /\
                    U64.v (U64.logand hdr 0xFFUL) == U64.v (getTag (yw d p))))
  = yw_read d p;
    getWosize_spec (yw d p);
    getTag_spec (yw d p)

#push-options "--z3rlimit 40"
let rec objects_from_walk (d: minor_heap) (p: nat) (b: nat) (x: U64.t)
  : Lemma (requires ychain d p b /\ p % 8 == 0 /\ b <= minor_heap_size /\ b % 8 == 0)
          (ensures (Seq.mem x (minor_objects_from d p b) <==> (U64.v x >= 8 /\ yat d p b (U64.v x - 8))) /\
                   minor_chain_valid d p b == true /\ minor_chain_no_infix d p b == true)
          (decreases (if p < b then b - p else 0))
  = chain_le d p b;
    if p + 8 > b then begin
      minor_chain_walk_stop d p b;
      if p < b then aligned_gap p b;
      assert (p == b);
      if U64.v x >= 8 then yat_empty d p (U64.v x - 8);
      FStar.Classical.move_requires (Seq.mem_index x) (Seq.empty #U64.t);
      assert (Seq.length (Seq.empty #U64.t) == 0);
      assert (~(Seq.mem x (Seq.empty #U64.t)))
    end
    else begin
      msz ();
      chain_unfold d p b;
      let n = next d p in
      chain_le d n b;
      objects_from_walk d n b x;
      step_shape d p;
      minor_chain_walk_step d p b n;
      Seq.mem_cons (U64.uint_to_t (p + 8)) (minor_objects_from d n b);
      if U64.v x >= 8 && U64.v x - 8 <> p then yat_unfold d p b (U64.v x - 8)
      else if U64.v x >= 8 then yat_here d p b
    end
#pop-options

let young_objects (ms: minor_state) (x: U64.t)
  : Lemma (requires yok ms)
          (ensures (Seq.mem x (minor_objects ms) <==> (U64.v x >= 8 /\ yat ms.data 0 (U64.v ms.bump) (U64.v x - 8))) /\
                   minor_wf ms)
  = yok_elim ms;
    objects_from_walk ms.data 0 (U64.v ms.bump) x;
    minor_objects_from_zero ms

/// ---------------------------------------------------------------------------
/// Young pointers resolve as resolve_minor does
/// ---------------------------------------------------------------------------

let hdr_bits (hdr: U64.t)
  : Lemma (U64.v (U64.logand hdr 0xFFUL) == U64.v hdr % 256 /\ U64.v (U64.shift_right hdr 10ul) == U64.v hdr / 1024 /\
           U64.v (getTag hdr) == U64.v hdr % 256 /\ U64.v (getWosize hdr) == U64.v hdr / 1024)
  = getTag_spec hdr;
    getWosize_spec hdr;
    FStar.UInt.logand_mask #64 (U64.v hdr) 8;
    assert_norm (pow2 8 - 1 == 255);
    assert_norm (pow2 10 == 1024)

/// The header word below a young pointer, as GC.Gen.MinorHeap reads it.
let minor_reads (ms: minor_state) (a: nat)
  : Lemma (requires 8 * a + 16 <= minor_heap_size)
          (ensures (msz ();
                    let v = U64.uint_to_t (8 * a + 8) in
                    let hdr = yw ms.data (8 * a) in
                    minor_tag ms v == U64.v hdr % 256 /\ minor_wosize ms v == U64.v hdr / 1024))
  = msz ();
    yw_read ms.data (8 * a);
    hdr_bits (yw ms.data (8 * a))

let vpos (a: nat)
  : Lemma (requires a + 1 < ywords)
          (ensures 8 * a + 8 < minor_heap_size /\ (8 * a + 8) % 8 == 0 /\ 8 * a + 16 <= minor_heap_size /\
                   8 * a + 8 < pow2 64)
  = base_facts (); msz ()

let par_arith (a o k: nat)
  : Lemma (requires k == a - o /\ o < a) (ensures k * 8 <= 8 * a + 8 /\ (8 * a + 8) - k * 8 == 8 * o + 8)
  = ()

#push-options "--z3rlimit 40"
let young_resolve (m: M.mheap) (ms: minor_state) (a o: nat)
  : Lemma (requires yrepr m ms /\ a + 1 < ywords /\ M.resolve m a == Some o)
          (ensures (msz (); resolve_minor ms (U64.uint_to_t (8 * a + 8)) == U64.uint_to_t (8 * o + 8)))
  = msz ();
    vpos a;
    yrepr_elim m ms;
    let v = U64.uint_to_t (8 * a + 8) in
    assert (U64.v v == 8 * a + 8);
    let hdr = yw ms.data (8 * a) in
    minor_reads ms a;
    hdr_bits hdr;
    R.agree_blocks m (yabs ms) a;
    if M.is_block m a then begin
      yblock ms a;
      assert (M.tag_of (yabs ms) a == U64.v (getTag hdr));
      assert (minor_tag ms v <> 249);
      resolve_minor_non_infix ms v
    end
    else begin
      let k = a - o in
      assert (M.covers m o a /\ o < a);
      assert (R.field_word m a);
      R.agree_field_word m (yabs ms) a;
      assert (m.M.body a == absv hdr);
      assert (M.infix_hdr (absv hdr) == Some k);
      assert (minor_tag ms v == 249);
      assert (minor_wosize ms v == k);
      assert (is_infix_in_minor ms v);
      par_arith a o k;
      assert (minor_wosize ms v * 8 <= U64.v v);
      assert (U64.v (infix_parent ms v) == 8 * o + 8);
      U64.v_inj (infix_parent ms v) (U64.uint_to_t (8 * o + 8))
    end
#pop-options
