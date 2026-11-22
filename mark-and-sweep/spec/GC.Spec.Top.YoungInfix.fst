/// ---------------------------------------------------------------------------
/// GC.Spec.Top.YoungInfix - the nursery's infix headers
/// ---------------------------------------------------------------------------
///
/// The promotion of GC.Spec.Pages.Promote (like akhil's Cheney collection)
/// assumes `minor_infix_wf` of the nursery (akhil's trust assumption on the
/// mutator): every word of the nursery whose tag is the infix tag is the
/// infix header of a closure, at its own offset.  `young_infix_wf`: it holds
/// of a nursery the byte representation relates to a model nursery that is
/// well formed (`young_ok`) and whose fields read as infix headers only
/// where they are ones (`Iface.young_infix_ok`, G38).  The words past the
/// bump pointer are zero (`Young.yok`, G38), so no tag there is the infix
/// tag; a header word is a block's, never infix; a field word is the
/// model's.

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

/// The model's condition, sealed.
[@@"opaque_to_smt"]
let yio (m: M.mheap) : prop = T.young_infix_ok m

let yio_intro (m: M.mheap) : Lemma (requires T.young_infix_ok m) (ensures yio m)
  = reveal_opaque (`%yio) (yio m)

/// The model's condition at one field.
let yio_at (m: M.mheap) (x i: nat)
  : Lemma (requires yio m /\ M.is_block m x /\ i < M.wz_of m x)
          (ensures (match M.infix_hdr (M.field m x i) with
                    | Some k -> M.tag_of m x == M.closure_tag /\ k == i + 1 /\ k >= 2 /\ k < M.wz_of m x
                    | None -> True))
  = reveal_opaque (`%yio) (yio m)

let field_at (m: M.mheap) (x a: nat)
  : Lemma (requires x < a) (ensures M.field m x (a - x - 1) == m.M.body a)
  = assert (x + 1 + (a - x - 1) == a)

/// The model's side: the field word is an infix header of its closure.
#push-options "--z3rlimit 40"
let field_model (m: M.mheap) (y: M.mheap) (x a: nat) (n: nat)
  : Lemma (requires R.agree m y /\ yio m /\ M.covers y x a /\ x < a /\
                    y.M.body a == M.VInt n /\ n % 256 == 249)
          (ensures n / 1024 == a - x /\ n / 1024 >= 2 /\ M.tag_of y x == 247 /\ n / 1024 < M.wz_of y x)
  = let i : nat = a - x - 1 in
    field_at m x a;
    R.agree_blocks m y x;
    assert (R.field_word y a);
    R.agree_field_word m y a;
    yio_at m x i
#pop-options

/// A field word with the infix tag: the infix header of its closure.
#push-options "--z3rlimit 40"
let field_infix (m: M.mheap) (ms: minor_state) (x a: nat)
  : Lemma (requires yrepr m ms /\ yio m /\ M.covers (yabs ms) x a /\ x < a /\
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
  : Lemma (requires yrepr m ms /\ yio m /\ M.covers (yabs ms) x a /\ x < a /\
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
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ yio m /\ is_infix_in_minor ms addr)
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

/// **The promotion's assumptions on the nursery hold.**
let young_infix_wf (m: M.mheap) (ms: minor_state)
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ T.young_infix_ok m)
          (ensures minor_wf ms /\ minor_infix_wf ms)
  = yrepr_elim m ms;
    yio_intro m;
    young_objects ms 0UL;
    reveal_opaque (`%minor_infix_wf) (minor_infix_wf ms);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (infix_one m ms))

/// ---------------------------------------------------------------------------
/// What the bytes resolve, the model resolves
/// ---------------------------------------------------------------------------

/// The model's side of an infix header found by the bytes.
#push-options "--z3rlimit 40"
let model_infix (m: M.mheap) (y: M.mheap) (x a: nat) (n: nat)
  : Lemma (requires R.agree m y /\ yio m /\ M.young_ok m /\ M.covers y x a /\ x < a /\
                    y.M.body a == M.VInt n /\ n % 256 == 249 /\ m.M.size == y.M.size)
          (ensures M.resolve m a == Some x)
  = field_model m y x a n;
    R.agree_blocks m y x;
    assert (M.covers m x a);
    assert (R.field_word y a);
    R.agree_field_word m y a;
    assert (m.M.body a == M.VInt n);
    if M.is_block m a then assert (M.covers m a a)
#pop-options

let covers_lt (y: M.mheap) (x a: nat) : Lemma (requires M.covers y x a /\ x <> a) (ensures x < a) = ()

/// The field case: the closure's block.
#push-options "--z3rlimit 40"
let back_field (m: M.mheap) (ms: minor_state) (v: U64.t) (a x: nat)
  : Lemma (requires yrepr m ms /\ yio m /\ M.young_ok m /\ M.covers (yabs ms) x a /\ x < a /\
                    U64.v v == 8 * a + 8 /\ 8 * a + 16 <= minor_heap_size /\ v == U64.uint_to_t (8 * a + 8) /\
                    is_infix_in_minor ms v)
          (ensures M.resolve m a == Some x /\ U64.v (infix_parent ms v) == 8 * x + 8)
  = field_case m ms v a x;
    let hdr = yw ms.data (8 * a) in
    minor_reads ms a;
    absv_infix hdr;
    yrepr_elim m ms;
    assert ((yabs ms).M.body a == absv hdr);
    model_infix m (yabs ms) x a (U64.v hdr);
    lt_bound x a;
    yblock ms x;
    parent_obj ms x;
    infix_concl ms v a x
#pop-options

/// The infix case.
let back_infix (m: M.mheap) (ms: minor_state) (a: nat)
  : Lemma (requires yrepr m ms /\ yio m /\ M.young_ok m /\ 8 * a + 16 <= minor_heap_size /\
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

/// **A nursery address the bytes resolve to an object is one the model
/// resolves, to that object's block.**
let young_resolve_back (m: M.mheap) (ms: minor_state) (a: nat)
  : Lemma (requires yrepr m ms /\ M.young_ok m /\ T.young_infix_ok m /\ 8 * a + 16 <= minor_heap_size /\
                    (msz (); Seq.mem (resolve_minor ms (U64.uint_to_t (8 * a + 8))) (minor_objects ms)))
          (ensures (msz ();
                    let r = resolve_minor ms (U64.uint_to_t (8 * a + 8)) in
                    U64.v r >= 8 /\ M.resolve m a == Some ((U64.v r - 8) / 8)))
  = msz ();
    yio_intro m;
    let v = U64.uint_to_t (8 * a + 8) in
    if is_infix_in_minor ms v then back_infix m ms a
    else begin
      resolve_minor_non_infix ms v;
      back_plain m ms a
    end
