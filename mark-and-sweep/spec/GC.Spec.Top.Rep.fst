/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Rep - a collector's own heap, its representation relation, and
/// faithfulness
/// ---------------------------------------------------------------------------
///
/// The specification is generic in the heap: each collector brings its own
/// major heap type `t` and nursery type `yt` (the byte heap of GC.Spec.Base
/// and the nursery of GC.Gen.MinorHeap for the collectors of this
/// repository; the model itself for the toy) and a representation `rep t yt`.
///
/// As in McCreight, Shao, Lin and Li ("A General Framework for Certifying
/// Garbage Collectors and Their Mutators", PLDI 2007), the link between the
/// model (GC.Spec.Top.Heap) and a concrete heap is a representation
/// relation `repr m h`, not a function: it need not be invertible (bytes the
/// model does not describe, and later the renaming of promoted copies, are
/// left free).  Contracts are stated on the model and lifted through `repr`
/// (`lifted`): a precondition holds of `h` when some represented model heap
/// satisfies it, and a guarantee holds when every represented model heap that
/// satisfies the precondition has a represented successor related to it by
/// the guarantee.
///
/// A relation that hid things would make the lifted contracts say less than
/// they seem to.  So every instance proves `faithful`:
///   - what the program and the collector read is the model: the instance's
///     own reads of a header (`rhd`) and of a field (`read`) are those of
///     every represented model heap; so two model heaps representing one
///     concrete heap have the same blocks, headers and fields;
///   - nothing missing: every well-formed model heap of the instance's size
///     whose words it can store (`representable`) represents one of its heaps;
///   - the nursery likewise, and the program's operations on it (allocate,
///     write, reset after a minor collection) are the model's, lifted; an
///     allocation fails only when the nursery has no room (or the object is
///     bigger than its largest);
///   - the instance stores at least every word OCaml puts in a field (`rich`):
///     odd words (immediates, infix headers), and pointers to every block of
///     the major heap and of the nursery.
/// How the instance's reads are its real ones (blocks, headers, fields,
/// pointers, infix and young ones included) is the instance's to show; for
/// the byte heap see GC.Spec.Top.Abs and GC.Spec.Top.Young.

module GC.Spec.Top.Rep

open GC.Spec.Top.Heap
module L = FStar.List.Tot

/// `w` is a field word of some block.
let field_word (m: mheap) (w: nat) : prop = exists (o: nat). covers m o w /\ o < w

/// Same size, same blocks and headers, same fields.
let agree (m m': mheap) : prop =
  m.size == m'.size /\
  (forall (o: nat). o < m'.size ==> m.hd o == m'.hd o) /\
  (forall (w: nat). field_word m' w ==> m.body w == m'.body w)

noeq type rep (t yt: Type0) = {
  (* the major heap *)
  repr     : mheap -> t -> prop;              (* model heap m represents h *)
  size_ok  : nat -> bool;                     (* its sizes, in words *)
  storable : value -> bool;                   (* the words a field can hold *)
  rsize    : t -> GTot nat;                   (* its size, in words *)
  rhd      : t -> nat -> GTot (option header); (* the header read at o, if a block starts there *)
  read     : t -> nat -> nat -> GTot value;   (* the read of field i of the block at o *)
  (* the nursery, and the program's operations on it *)
  yrepr    : mheap -> yt -> prop;
  ysize_ok : nat -> bool;
  ymax     : nat;                             (* the largest young object *)
  ysize    : yt -> GTot nat;
  yhd      : yt -> nat -> GTot (option header);
  yread    : yt -> nat -> nat -> GTot value;
  yinit    : nat -> GTot yt;
  yalloc   : yt -> size_t -> tag_t -> list value -> GTot (option (nat & yt));
  ywrite   : yt -> nat -> nat -> value -> GTot yt;
  yreset   : yt -> GTot yt;
}

/// A model contract (`pre`, `post`) lifted to a concrete step from `h` to `h'`.
let lifted (#t #yt: Type0) (r: rep t yt) (pre: mheap -> prop) (h h': t) (post: mheap -> mheap -> prop)
  : prop =
  forall (m: mheap). r.repr m h /\ pre m ==> (exists (m': mheap). r.repr m' h' /\ post m m')

/// A model statement about the input, for every model heap representing it.
let forall_repr (#t #yt: Type0) (r: rep t yt) (h: t) (f: mheap -> prop) : prop =
  forall (m: mheap). r.repr m h ==> f m

/// A model statement about two heaps, for every pair of model heaps representing them.
let forall_repr2 (#t #yt: Type0) (r: rep t yt) (h h': t) (f: mheap -> mheap -> prop) : prop =
  forall (m m': mheap). r.repr m h /\ r.repr m' h' ==> f m m'

/// A model precondition, lifted: some represented model heap satisfies it.
let some_repr (#t #yt: Type0) (r: rep t yt) (h: t) (pre: mheap -> prop) : prop =
  exists (m: mheap). r.repr m h /\ pre m

/// ---------------------------------------------------------------------------
/// Faithfulness
/// ---------------------------------------------------------------------------

/// The instance can hold at least what OCaml puts in a field.
let rich (#t #yt: Type0) (r: rep t yt) : prop =
  (exists (n: nat). n >= 2 /\ r.size_ok n) /\
  (exists (n: nat). n >= 2 /\ r.ysize_ok n) /\
  r.ymax >= 1 /\
  (forall (n: nat). n < pow2 64 /\ n % 2 == 1 ==> r.storable (VInt n)) /\
  (forall (n a: nat). r.size_ok n /\ a + 1 < n ==> r.storable (VPtr (Major a))) /\
  (forall (n a: nat). r.ysize_ok n /\ a + 1 < n ==> r.storable (VPtr (Young a)))

/// A model heap whose words outside fields are 0 and with no header past
/// its end.  Every model heap agrees with a canonical one (`agree`): only the
/// fields and headers carry meaning.
let canonical (m: mheap) : prop =
  (forall (o: nat). o >= m.size ==> m.hd o == None) /\
  (forall (w: nat). ~(field_word m w) ==> m.body w == VInt 0)

/// The model heaps an instance must be able to represent: well formed, of
/// one of its sizes, every block with a field, every field storable,
/// canonical.
let representable (#t #yt: Type0) (r: rep t yt) (m: mheap) : prop =
  well_formed m /\ r.size_ok m.size /\
  (forall (o: nat). is_block m o ==> wz_of m o >= 1) /\
  (forall (w: nat). field_word m w ==> r.storable (m.body w)) /\
  canonical m

/// The reads of a concrete heap are those of every model heap it represents.
let reads_model (sz: nat) (rhd: nat -> GTot (option header)) (read: nat -> nat -> GTot value) (m: mheap) : prop =
  m.size == sz /\
  (forall (o: nat). o < m.size ==> rhd o == m.hd o) /\
  (forall (o i: nat). is_block m o /\ i < wz_of m o ==> read o i == field m o i)

let faithful_major (#t #yt: Type0) (r: rep t yt) : prop =
  (forall (m: mheap) (h: t). r.repr m h ==>
     r.size_ok m.size /\ reads_model (r.rsize h) (r.rhd h) (r.read h) m) /\
  (forall (m: mheap). representable r m ==> (exists (h: t). r.repr m h))

let storable_all (#t #yt: Type0) (r: rep t yt) (vs: list value) : prop =
  forall (v: value). L.memP v vs ==> r.storable v

let yinit_ok (#t #yt: Type0) (r: rep t yt) (n: nat) : prop =
  r.ysize_ok n ==> r.yrepr (empty_heap n) (r.yinit n)

let yalloc_ok (#t #yt: Type0) (r: rep t yt) (y: yt) (sz: size_t) (tag: tag_t) (vs: list value) : prop =
  forall (m: mheap). r.yrepr m y /\ tag <> infix_tag /\ L.length vs == sz /\ storable_all r vs ==>
  (match r.yalloc y sz tag vs with
   | Some (o, y') -> young_free m o sz /\ r.yrepr (young_alloc m o sz tag vs) y'
   | None -> sz > r.ymax \/ ~(exists (o: nat). young_free m o sz))

let ywrite_ok (#t #yt: Type0) (r: rep t yt) (y: yt) (o i: nat) (v: value) : prop =
  forall (m: mheap). r.yrepr m y /\ is_block m o /\ i < wz_of m o /\ r.storable v ==>
  r.yrepr (set_field m o i v) (r.ywrite y o i v)

let yreset_ok (#t #yt: Type0) (r: rep t yt) (y: yt) : prop =
  forall (m: mheap). r.yrepr m y ==> r.yrepr (empty_heap m.size) (r.yreset y)

let faithful_young (#t #yt: Type0) (r: rep t yt) : prop =
  (forall (m: mheap) (y: yt). r.yrepr m y ==>
     r.ysize_ok m.size /\ reads_model (r.ysize y) (r.yhd y) (r.yread y) m) /\
  (forall (n: nat). yinit_ok r n) /\
  (forall (y: yt) (sz: size_t) (tag: tag_t) (vs: list value). yalloc_ok r y sz tag vs) /\
  (forall (y: yt) (o i: nat) (v: value). ywrite_ok r y o i v) /\
  (forall (y: yt). yreset_ok r y)

let faithful (#t #yt: Type0) (r: rep t yt) : prop =
  rich r /\ faithful_major r /\ faithful_young r

/// ---------------------------------------------------------------------------
/// What faithfulness gives
/// ---------------------------------------------------------------------------

/// Two model heaps representing one concrete heap agree: same blocks,
/// headers and fields.
let repr_agree (#t #yt: Type0) (r: rep t yt) (m1 m2: mheap) (h: t)
  : Lemma (requires faithful_major r /\ r.repr m1 h /\ r.repr m2 h)
          (ensures agree m1 m2)
  = let aux (w: nat) (o: nat)
      : Lemma (requires covers m2 o w /\ o < w) (ensures m1.body w == m2.body w)
      = assert (r.read h o (w - o - 1) == field m2 o (w - o - 1));
        assert (r.rhd h o == m1.hd o);
        assert (r.read h o (w - o - 1) == field m1 o (w - o - 1)) in
    let aux' (w: nat) : Lemma (field_word m2 w ==> m1.body w == m2.body w)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (aux w)) in
    FStar.Classical.forall_intro aux'

let agree_refl (m: mheap) : Lemma (agree m m) = ()

/// Agreeing heaps have the same blocks, so the same field words.
let agree_covers (m m': mheap) (o w: nat)
  : Lemma (requires agree m m') (ensures covers m o w == covers m' o w)
  = ()

let agree_field_word (m m': mheap) (w: nat)
  : Lemma (requires agree m m') (ensures field_word m w <==> field_word m' w)
  = FStar.Classical.forall_intro (fun (o: nat) -> agree_covers m m' o w)

let agree_sym (m m': mheap) : Lemma (requires agree m m') (ensures agree m' m)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (agree_field_word m m'))

let agree_trans (m1 m2 m3: mheap)
  : Lemma (requires agree m1 m2 /\ agree m2 m3) (ensures agree m1 m3)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (agree_field_word m2 m3))

/// A store into a field of agreeing heaps.
let agree_set_field (m m': mheap) (o i: nat) (v: value)
  : Lemma (requires agree m m' /\ is_block m' o /\ i < wz_of m' o)
          (ensures agree (set_field m o i v) (set_field m' o i v))
  = ()

/// A young allocation into agreeing heaps.
let agree_young_alloc (m m': mheap) (o: nat) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires agree m m' /\ o < m'.size /\ L.length vs == sz)
          (ensures agree (young_alloc m o sz tag vs) (young_alloc m' o sz tag vs))
  = let ma = young_alloc m o sz tag vs in
    let ma' = young_alloc m' o sz tag vs in
    let bd (w x: nat) : Lemma (requires covers ma' x w /\ x < w) (ensures ma.body w == ma'.body w)
      = if o < w && w - o - 1 < L.length vs then ()
        else begin
          assert (x <> o);
          assert (covers m' x w);
          assert (field_word m' w)
        end in
    let bd' (w: nat) : Lemma (field_word ma' w ==> ma.body w == ma'.body w)
      = FStar.Classical.forall_intro (FStar.Classical.move_requires (bd w)) in
    FStar.Classical.forall_intro bd'

/// ---------------------------------------------------------------------------
/// Pointwise equality
/// ---------------------------------------------------------------------------

/// The same heap, word by word (F* cannot equate two records of functions
/// from pointwise equality; every model statement reads a heap through `hd`
/// and `body`).
let heq (m m': mheap) : prop =
  m.size == m'.size /\ (forall (o: nat). m.hd o == m'.hd o) /\ (forall (w: nat). m.body w == m'.body w)

let heq_refl (m: mheap) : Lemma (heq m m) = ()

let heq_sym (m m': mheap) : Lemma (requires heq m m') (ensures heq m' m) = ()

let heq_trans (m1 m2 m3: mheap) : Lemma (requires heq m1 m2 /\ heq m2 m3) (ensures heq m1 m3) = ()

let heq_agree (m m': mheap) : Lemma (requires heq m m') (ensures agree m m') = ()

/// Agreeing canonical heaps are the same heap.
let agree_canonical (m m': mheap)
  : Lemma (requires agree m m' /\ canonical m /\ canonical m') (ensures heq m m')
  = let bd (w: nat) : Lemma (m.body w == m'.body w)
      = agree_field_word m m' w in
    FStar.Classical.forall_intro bd

let canonical_heq (m m': mheap) : Lemma (requires heq m m' /\ canonical m) (ensures canonical m')
  = let bd (w: nat) : Lemma (~(field_word m' w) ==> m'.body w == VInt 0)
      = assert (forall (o: nat). covers m o w == covers m' o w) in
    FStar.Classical.forall_intro bd

let agree_blocks (m m': mheap) (o: nat)
  : Lemma (requires agree m m')
          (ensures is_block m o == is_block m' o /\ (is_block m o ==> hdr_of m o == hdr_of m' o))
  = ()

/// The program's operations keep a heap canonical.
let canonical_empty (n: nat) : Lemma (canonical (empty_heap n)) = ()

let canonical_set_field (m: mheap) (o i: nat) (v: value)
  : Lemma (requires canonical m /\ is_block m o /\ i < wz_of m o) (ensures canonical (set_field m o i v))
  = let m' = set_field m o i v in
    let bd (w: nat) : Lemma (~(field_word m' w) ==> m'.body w == VInt 0)
      = assert (forall (x: nat). covers m' x w == covers m x w);
        if w = o + 1 + i then assert (covers m o w) in
    FStar.Classical.forall_intro bd

#push-options "--z3rlimit 40"
let canonical_young_alloc (m: mheap) (o: nat) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires canonical m /\ young_free m o sz /\ L.length vs == sz)
          (ensures canonical (young_alloc m o sz tag vs))
  = let m' = young_alloc m o sz tag vs in
    let bd (w: nat) : Lemma (~(field_word m' w) ==> m'.body w == VInt 0)
      = if o < w && w <= o + sz then assert (covers m' o w)
        else begin
          let cv (x: nat) : Lemma (covers m x w ==> covers m' x w)
            = if covers m x w && x = o then assert (covers m o o) in
          FStar.Classical.forall_intro cv;
          if w = o then assert (forall (x: nat). ~(covers m x o))
        end in
    FStar.Classical.forall_intro bd
#pop-options
