/// ---------------------------------------------------------------------------
/// GC.Spec.Top.YoungInfix - the nursery's infix headers
/// ---------------------------------------------------------------------------
///
/// The promotion of GC.Spec.Pages.Promote reads the word below an address
/// it follows, and takes it, if its tag is the infix tag, for the infix
/// header of a closure (`Promote.Follow.follow_ok`, design doc §12).  It
/// follows the nursery's fields and the roots.  `follow_one`: the bytes
/// satisfy that at an address the model follows safely (`Iface.follow_at`:
/// a word below it reading as an infix header is one the model resolves
/// through).  The words past the bump pointer are zero (`Young.yok`, G38),
/// so no tag there is the infix tag; a header word is a block's, never
/// infix; a field word is the model's.  Ordinary data that looks like an
/// infix header is never below a followed address.

module GC.Spec.Top.YoungInfix

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
open GC.Spec.Top.Young
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module F = GC.Spec.Pages.Promote.Follow

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let okpos8 (a: nat) : Lemma (requires 8 * a + 8 <= minor_heap_size) (ensures ok_pos (8 * a))
  = FStar.Math.Lemmas.multiple_modulo_lemma a 8

let zero_at (ms: minor_state) (a: nat)
  : Lemma (requires zero_past ms.data (U64.v ms.bump) /\ 8 * a >= U64.v ms.bump /\ 8 * a + 8 <= minor_heap_size)
          (ensures yw ms.data (8 * a) == 0UL)
  = okpos8 a;
    zero_past_def ms.data (U64.v ms.bump)

/// The word below an aligned nursery address is past the bump pointer: zero.
let past_zero (ms: minor_state) (a: nat)
  : Lemma (requires yok ms /\ 8 * a >= U64.v ms.bump /\ 8 * a + 16 <= minor_heap_size)
          (ensures (msz (); minor_tag ms (U64.uint_to_t (8 * a + 8)) == 0))
  = yok_elim ms;
    zero_at ms a;
    minor_reads ms a

/// The word below is a block's header: its tag is not the infix tag.
#push-options "--z3rlimit 40"
let header_not_infix (ms: minor_state) (a: nat)
  : Lemma (requires yok ms /\ M.is_block (yabs ms) a /\ 8 * a + 16 <= minor_heap_size)
          (ensures (msz (); minor_tag ms (U64.uint_to_t (8 * a + 8)) <> 249))
  = yblock ms a;
    minor_reads ms a;
    hdr_bits (yw ms.data (8 * a))
#pop-options

/// A word with the infix tag reads as an infix header.
let absv_infix (hdr: U64.t)
  : Lemma (requires U64.v hdr % 256 == 249)
          (ensures absv hdr == M.VInt (U64.v hdr) /\ M.infix_hdr (absv hdr) == Some (U64.v hdr / 1024))
  = FStar.Math.Lemmas.modulo_modulo_lemma (U64.v hdr) 8 32;
    assert (U64.v hdr % 8 == 1)

let field_at (m: M.mheap) (x a: nat)
  : Lemma (requires x < a) (ensures M.field m x (a - x - 1) == m.M.body a)
  = assert (x + 1 + (a - x - 1) == a)

/// The model's side: a field word with the infix tag, below an address
/// followed safely, is an infix header of its closure, which the model
/// resolves the address to.
#push-options "--z3rlimit 40"
let field_model (m: M.mheap) (y: M.mheap) (x a: nat) (n: nat)
  : Lemma (requires R.agree m y /\ T.follow_at m a /\ M.young_ok m /\ M.covers y x a /\ x < a /\
                    y.M.body a == M.VInt n /\ n % 256 == 249)
          (ensures n / 1024 == a - x /\ n / 1024 >= 2 /\ M.tag_of y x == 247 /\ n / 1024 < M.wz_of y x /\
                   M.resolve m a == Some x)
  = R.agree_blocks m y x;
    assert (M.covers m x a);
    assert (exists (o: nat). M.covers m o a /\ o < a);
    assert (R.field_word y a);
    R.agree_field_word m y a;
    assert (m.M.body a == M.VInt n);
    (if M.is_block m a then assert (M.covers m a a));
    assert (M.infix_hdr (m.M.body a) == Some (n / 1024));
    assert (Some? (M.resolve m a));
    let k = n / 1024 in
    assert (M.covers m (a - k) a)
#pop-options

/// A field word with the infix tag: the infix header of its closure.
#push-options "--z3rlimit 40"
let field_infix (m: M.mheap) (ms: minor_state) (x a: nat)
  : Lemma (requires yrepr m ms /\ T.follow_at m a /\ M.young_ok m /\ M.covers (yabs ms) x a /\ x < a /\
                    8 * a + 16 <= minor_heap_size /\
                    (msz (); minor_tag ms (U64.uint_to_t (8 * a + 8)) == 249))
          (ensures (msz ();
                    let addr = U64.uint_to_t (8 * a + 8) in
                    let k = minor_wosize ms addr in
                    k == a - x /\ k >= 2 /\ M.tag_of (yabs ms) x == 247 /\ k < M.wz_of (yabs ms) x))
  = msz ();
    yrepr_elim m ms;
    let hdr = yw ms.data (8 * a) in
    minor_reads ms a;
    absv_infix hdr;
    assert ((yabs ms).M.body a == absv hdr);
    field_model m (yabs ms) x a (U64.v hdr)
#pop-options

/// The closure of an infix word is a nursery object of the closure tag.
#push-options "--z3rlimit 40"
let parent_obj (ms: minor_state) (x: nat)
  : Lemma (requires yok ms /\ M.is_block (yabs ms) x /\ 8 * x + 16 <= minor_heap_size)
          (ensures (msz ();
                    let p = U64.uint_to_t (8 * x + 8) in
                    Seq.mem p (minor_objects ms) /\ minor_tag ms p == M.tag_of (yabs ms) x /\
                    minor_wosize ms p == M.wz_of (yabs ms) x))
  = msz ();
    yblock ms x;
    let p = U64.uint_to_t (8 * x + 8) in
    young_objects ms p;
    minor_reads ms x;
    hdr_bits (yw ms.data (8 * x))
#pop-options

/// The address of an infix-looking word, as a model word.
let addr_facts (ms: minor_state) (addr: U64.t)
  : Lemma (requires is_infix_in_minor ms addr)
          (ensures (let a = (U64.v addr - 8) / 8 in
                    U64.v addr == 8 * a + 8 /\ 8 * a + 16 <= minor_heap_size /\ 8 * a + 8 < pow2 64 /\
                    addr == U64.uint_to_t (8 * a + 8)))
  = msz ();
    let a = (U64.v addr - 8) / 8 in
    FStar.Math.Lemmas.lemma_div_exact (U64.v addr - 8) 8;
    assert_norm (minor_heap_size % 8 == 0);
    U64.v_inj addr (U64.uint_to_t (8 * a + 8))

let cases_at (ms: minor_state) (a: nat)
  : Lemma (requires yok ms /\ 8 * a + 8 <= minor_heap_size)
          (ensures 8 * a >= U64.v ms.bump \/ (exists (x: nat). M.covers (yabs ms) x a))
  = if 8 * a < U64.v ms.bump then below_bump ms a

let mul_sub (k a x: nat) : Lemma (requires k == a - x /\ x < a) (ensures k * 8 == 8 * a - 8 * x) = ()

let parent_val (ms: minor_state) (addr: U64.t) (k: nat)
  : Lemma (requires minor_wosize ms addr == k /\ k * 8 <= U64.v addr)
          (ensures U64.v (infix_parent ms addr) == U64.v addr - k * 8)
  = ()

/// The conclusion at an infix address, from its closure.
#push-options "--z3rlimit 40"
let infix_concl (ms: minor_state) (addr: U64.t) (a x: nat)
  : Lemma (requires U64.v addr == 8 * a + 8 /\ 8 * a + 16 <= minor_heap_size /\ x < a /\
                    minor_wosize ms addr == a - x /\ a - x >= 2 /\
                    (msz (); let p = U64.uint_to_t (8 * x + 8) in
                     Seq.mem p (minor_objects ms) /\ minor_tag ms p == 247 /\ a - x < minor_wosize ms p))
          (ensures (let wz = minor_wosize ms addr in
                    let parent = infix_parent ms addr in
                    wz >= 2 /\ wz * 8 <= U64.v addr - 8 /\ U64.v parent >= 8 /\ U64.v parent % 8 == 0 /\
                    Seq.mem parent (minor_objects ms) /\ minor_tag ms parent == 247 /\
                    U64.v addr - U64.v parent < minor_wosize ms parent * 8 /\
                    U64.v parent == 8 * x + 8))
  = msz ();
    mul_sub (a - x) a x;
    parent_val ms addr (a - x);
    U64.v_inj (infix_parent ms addr) (U64.uint_to_t (8 * x + 8))
#pop-options

let lt_bound (x a: nat) : Lemma (requires x < a /\ 8 * a + 16 <= minor_heap_size) (ensures 8 * x + 16 <= minor_heap_size)
  = ()

/// A field word with the infix tag, all the way.
let field_case (m: M.mheap) (ms: minor_state) (addr: U64.t) (a x: nat)
  : Lemma (requires yrepr m ms /\ T.follow_at m a /\ M.young_ok m /\ M.covers (yabs ms) x a /\ x < a /\
                    U64.v addr == 8 * a + 8 /\ 8 * a + 16 <= minor_heap_size /\
                    addr == U64.uint_to_t (8 * a + 8) /\ is_infix_in_minor ms addr)
          (ensures (let wz = minor_wosize ms addr in
                    let parent = infix_parent ms addr in
                    wz >= 2 /\ wz * 8 <= U64.v addr - 8 /\ U64.v parent >= 8 /\ U64.v parent % 8 == 0 /\
                    Seq.mem parent (minor_objects ms) /\ minor_tag ms parent == 247 /\
                    U64.v addr - U64.v parent < minor_wosize ms parent * 8))
  = lt_bound x a;
    field_infix m ms x a;
    yrepr_elim m ms;
    yblock ms x;
    parent_obj ms x;
    infix_concl ms addr a x

let covers_below (y: M.mheap) (x a: nat) : Lemma (requires M.covers y x a /\ x <> a) (ensures x < a) = ()

/// One infix address.
let infix_one (m: M.mheap) (ms: minor_state) (addr: U64.t)
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ is_infix_in_minor ms addr /\
                    T.follow_at m ((U64.v addr - 8) / 8))
          (ensures (let wz = minor_wosize ms addr in
                    let parent = infix_parent ms addr in
                    wz >= 2 /\ wz * 8 <= U64.v addr - 8 /\ U64.v parent >= 8 /\ U64.v parent % 8 == 0 /\
                    Seq.mem parent (minor_objects ms) /\ minor_tag ms parent == 247 /\
                    U64.v addr - U64.v parent < minor_wosize ms parent * 8))
  = addr_facts ms addr;
    let a = (U64.v addr - 8) / 8 in
    yrepr_elim m ms;
    cases_at ms a;
    if 8 * a >= U64.v ms.bump then past_zero ms a
    else begin
      let x = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun x -> M.covers (yabs ms) x a) in
      if x = a then header_not_infix ms a
      else begin
        covers_below (yabs ms) x a;
        field_case m ms addr a x
      end
    end

/// The nursery's shape.
let young_minor_wf (m: M.mheap) (ms: minor_state)
  : Lemma (requires yrepr m ms) (ensures minor_wf ms)
  = yrepr_elim m ms;
    young_objects ms 0UL

/// **An address the model follows safely, the promotion follows safely.**
let follow_one (m: M.mheap) (ms: minor_state) (addr: U64.t)
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ (U64.v addr >= 8 ==> T.follow_at m ((U64.v addr - 8) / 8)))
          (ensures F.follow_ok ms addr)
  = if is_infix_in_minor ms addr then infix_one m ms addr

/// ---------------------------------------------------------------------------
/// What the bytes resolve, the model resolves
/// ---------------------------------------------------------------------------

let covers_lt (y: M.mheap) (x a: nat) : Lemma (requires M.covers y x a /\ x <> a) (ensures x < a) = ()

/// The field case: the closure's block.
#push-options "--z3rlimit 40"
let back_field (m: M.mheap) (ms: minor_state) (v: U64.t) (a x: nat)
  : Lemma (requires yrepr m ms /\ T.follow_at m a /\ M.young_ok m /\ M.covers (yabs ms) x a /\ x < a /\
                    U64.v v == 8 * a + 8 /\ 8 * a + 16 <= minor_heap_size /\ v == U64.uint_to_t (8 * a + 8) /\
                    is_infix_in_minor ms v)
          (ensures M.resolve m a == Some x /\ U64.v (infix_parent ms v) == 8 * x + 8)
  = field_case m ms v a x;
    let hdr = yw ms.data (8 * a) in
    minor_reads ms a;
    absv_infix hdr;
    yrepr_elim m ms;
    assert ((yabs ms).M.body a == absv hdr);
    field_model m (yabs ms) x a (U64.v hdr);
    lt_bound x a;
    yblock ms x;
    parent_obj ms x;
    infix_concl ms v a x
#pop-options

/// The infix case.
let back_infix (m: M.mheap) (ms: minor_state) (a: nat)
  : Lemma (requires yrepr m ms /\ T.follow_at m a /\ M.young_ok m /\ 8 * a + 16 <= minor_heap_size /\
                    (msz (); is_infix_in_minor ms (U64.uint_to_t (8 * a + 8))))
          (ensures (msz ();
                    let v = U64.uint_to_t (8 * a + 8) in
                    exists (x: nat). M.resolve m a == Some x /\ U64.v (infix_parent ms v) == 8 * x + 8))
  = msz ();
    let v = U64.uint_to_t (8 * a + 8) in
    addr_facts ms v;
    yrepr_elim m ms;
    cases_at ms a;
    if 8 * a >= U64.v ms.bump then past_zero ms a
    else begin
      let x = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun x -> M.covers (yabs ms) x a) in
      if x = a then header_not_infix ms a
      else begin
        covers_lt (yabs ms) x a;
        back_field m ms v a x
      end
    end

let a_lt (a: nat) : Lemma (requires 8 * a + 16 <= minor_heap_size) (ensures a < ywords)
  = FStar.Math.Lemmas.lemma_div_le (8 * a + 8) minor_heap_size 8;
    FStar.Math.Lemmas.cancel_mul_div (a + 1) 8

/// The plain case.
#push-options "--z3rlimit 40"
let back_plain (m: M.mheap) (ms: minor_state) (a: nat)
  : Lemma (requires yrepr m ms /\ 8 * a + 16 <= minor_heap_size /\
                    (msz (); Seq.mem (U64.uint_to_t (8 * a + 8)) (minor_objects ms)))
          (ensures M.resolve m a == Some a)
  = msz ();
    a_lt a;
    let b : nat = U64.v ms.bump in
    let v = U64.uint_to_t (8 * a + 8) in
    yrepr_elim m ms;
    young_objects ms v;
    yok_elim ms;
    yat_facts ms.data 0 b (8 * a);
    assert (Some? (yhd_of ms a));
    R.agree_blocks m (yabs ms) a
#pop-options

/// The arithmetic of an infix address `8 * a + 8` at offset `k` in the
/// object at `p`.
let closure_arith (a k p wz: nat)
  : Lemma (requires p == 8 * a + 8 - k * 8 /\ k >= 2 /\ p >= 8 /\ p % 8 == 0 /\ 8 * a + 8 - p < wz * 8)
          (ensures (let xp = (p - 8) / 8 in p == 8 * xp + 8 /\ k == a - xp /\ xp < a /\ k < wz /\ a <= xp + wz))
  = FStar.Math.Lemmas.lemma_div_exact (p - 8) 8

/// The closure the bytes read an infix address into: a block of the model,
/// with the address among its fields.
#push-options "--z3rlimit 40"
let infix_closure (m: M.mheap) (ms: minor_state) (a: nat)
  : Lemma (requires yrepr m ms /\ 8 * a + 16 <= minor_heap_size /\
                    (msz (); let v = U64.uint_to_t (8 * a + 8) in is_infix_in_minor ms v /\ F.infix_at ms v))
          (ensures (msz ();
                    let v = U64.uint_to_t (8 * a + 8) in
                    let k = minor_wosize ms v in
                    let xp = (U64.v (infix_parent ms v) - 8) / 8 in
                    U64.v (infix_parent ms v) >= 8 /\ xp >= 0 /\
                    U64.v (infix_parent ms v) == 8 * xp + 8 /\ k == a - xp /\ k >= 2 /\
                    M.is_block m xp /\ M.tag_of m xp == 247 /\ k < M.wz_of m xp /\ M.covers m xp a))
  = msz ();
    let v = U64.uint_to_t (8 * a + 8) in
    F.infix_parent_value_at ms v;
    let p = infix_parent ms v in
    let k = minor_wosize ms v in
    let wz = minor_wosize ms p in
    closure_arith a k (U64.v p) wz;
    let xp = (U64.v p - 8) / 8 in
    U64.v_inj p (U64.uint_to_t (8 * xp + 8));
    assert (Seq.mem (U64.uint_to_t (8 * xp + 8)) (minor_objects ms));
    back_plain m ms xp;
    assert (M.is_block m xp);
    yrepr_elim m ms;
    R.agree_blocks m (yabs ms) xp;
    assert (M.is_block (yabs ms) xp);
    parent_obj ms xp;
    assert (M.tag_of m xp == M.tag_of (yabs ms) xp);
    assert (M.wz_of m xp == M.wz_of (yabs ms) xp);
    assert (M.tag_of m xp == 247);
    assert (k < M.wz_of m xp)
#pop-options

let cover_uniq (m: M.mheap) (o1 o2 w: nat)
  : Lemma (requires M.young_ok m /\ M.covers m o1 w /\ M.covers m o2 w) (ensures o1 == o2)
  = ()

/// An infix header at offset `k` in a closure: the model resolves through it.
let resolve_infix_model (m: M.mheap) (a x n: nat)
  : Lemma (requires ~(M.is_block m a) /\ m.M.body a == M.VInt n /\ n % 256 == 249 /\ n / 1024 == a - x /\
                    x < a /\ a - x >= 2 /\ M.is_block m x /\ M.tag_of m x == 247 /\ a - x < M.wz_of m x)
          (ensures M.resolve m a == Some x)
  = ()

/// The model's side of an address the bytes read as a genuine infix one.
#push-options "--z3rlimit 40"
let infix_model (m: M.mheap) (ms: minor_state) (a x: nat)
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ 8 * a + 16 <= minor_heap_size /\
                    M.covers (yabs ms) x a /\ x < a /\
                    (msz (); let v = U64.uint_to_t (8 * a + 8) in is_infix_in_minor ms v /\ F.infix_at ms v))
          (ensures (msz (); M.resolve m a == Some x /\
                    U64.v (infix_parent ms (U64.uint_to_t (8 * a + 8))) == 8 * x + 8))
  = msz ();
    let v = U64.uint_to_t (8 * a + 8) in
    infix_closure m ms a;
    let xp : nat = (U64.v (infix_parent ms v) - 8) / 8 in
    yrepr_elim m ms;
    R.agree_blocks m (yabs ms) x;
    assert (M.covers m x a);
    cover_uniq m x xp a;
    let hdr = yw ms.data (8 * a) in
    minor_reads ms a;
    absv_infix hdr;
    assert ((yabs ms).M.body a == absv hdr);
    assert (R.field_word (yabs ms) a);
    R.agree_field_word m (yabs ms) a;
    assert (m.M.body a == M.VInt (U64.v hdr));
    (if M.is_block m a then begin assert (M.covers m a a); cover_uniq m x a a end);
    resolve_infix_model m a x (U64.v hdr)
#pop-options

/// **An address the bytes read as a genuine infix one is one the model
/// resolves**, to the block of its closure.
let infix_back (m: M.mheap) (ms: minor_state) (a: nat)
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ 8 * a + 16 <= minor_heap_size /\
                    (msz (); let v = U64.uint_to_t (8 * a + 8) in is_infix_in_minor ms v /\ F.infix_at ms v))
          (ensures (msz ();
                    let v = U64.uint_to_t (8 * a + 8) in
                    exists (x: nat). M.resolve m a == Some x /\ U64.v (infix_parent ms v) == 8 * x + 8))
  = msz ();
    let v = U64.uint_to_t (8 * a + 8) in
    addr_facts ms v;
    yrepr_elim m ms;
    cases_at ms a;
    if 8 * a >= U64.v ms.bump then past_zero ms a
    else begin
      let x = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun x -> M.covers (yabs ms) x a) in
      if x = a then header_not_infix ms a
      else begin
        covers_lt (yabs ms) x a;
        infix_model m ms a x
      end
    end

/// **A nursery address the bytes resolve to an object, followed safely, is
/// one the model resolves, to that object's block.**
let young_resolve_follow (m: M.mheap) (ms: minor_state) (a: nat)
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ 8 * a + 16 <= minor_heap_size /\
                    (msz (); F.follow_ok ms (U64.uint_to_t (8 * a + 8)) /\
                     Seq.mem (resolve_minor ms (U64.uint_to_t (8 * a + 8))) (minor_objects ms)))
          (ensures (msz ();
                    let r = resolve_minor ms (U64.uint_to_t (8 * a + 8)) in
                    U64.v r >= 8 /\ M.resolve m a == Some ((U64.v r - 8) / 8)))
  = msz ();
    let v = U64.uint_to_t (8 * a + 8) in
    if is_infix_in_minor ms v then infix_back m ms a
    else begin
      resolve_minor_non_infix ms v;
      back_plain m ms a
    end

/// **A nursery address the bytes resolve to an object is one the model
/// resolves, to that object's block.**
let young_resolve_back (m: M.mheap) (ms: minor_state) (a: nat)
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ T.follow_at m a /\ 8 * a + 16 <= minor_heap_size /\
                    (msz (); Seq.mem (resolve_minor ms (U64.uint_to_t (8 * a + 8))) (minor_objects ms)))
          (ensures (msz ();
                    let r = resolve_minor ms (U64.uint_to_t (8 * a + 8)) in
                    U64.v r >= 8 /\ M.resolve m a == Some ((U64.v r - 8) / 8)))
  = msz ();
    let v = U64.uint_to_t (8 * a + 8) in
    if is_infix_in_minor ms v then back_infix m ms a
    else begin
      resolve_minor_non_infix ms v;
      back_plain m ms a
    end
