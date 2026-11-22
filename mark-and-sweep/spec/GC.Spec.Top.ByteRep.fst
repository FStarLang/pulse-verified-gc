/// ---------------------------------------------------------------------------
/// GC.Spec.Top.ByteRep - the representation of the byte-level collectors
/// ---------------------------------------------------------------------------
///
/// The collectors of this repository (pages, first-fit, with the generational
/// nursery) work on the byte heap of GC.Spec.Base and the nursery of
/// GC.Gen.MinorHeap.  `byte_rep` is their representation: the relation of
/// GC.Spec.Top.Abs for the major heap and of GC.Spec.Top.Young for the
/// nursery, the reads there, the words of GC.Spec.Top.Word.
///
/// Proved: `byte_rep_faithful`, every condition of GC.Spec.Top.Rep.faithful;
/// and `bad_byte_rep_rejected`: the relation that relates every byte heap to
/// the empty heap is not faithful (a heap of one free block is represented by
/// no byte heap).

module GC.Spec.Top.ByteRep

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Young
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let bsize_ok (n: nat) : bool = n = msize
let bysize_ok (n: nat) : bool = n = ywords
let brsize (g: heap) : GTot nat = msize

let byte_rep : R.rep heap minor_state = {
  R.repr = brepr; R.size_ok = bsize_ok; R.storable = storable_w;
  R.rsize = brsize; R.rhd = read_hd; R.read = read_field;
  R.yrepr = yrepr; R.ysize_ok = bysize_ok; R.ymax = max_young_wosize;
  R.ysize = ysz; R.yhd = yhd; R.yread = yread;
  R.yinit = yinit; R.yalloc = yalloc; R.ywrite = ywrite; R.yreset = yreset;
}

/// ---------------------------------------------------------------------------
/// Faithful
/// ---------------------------------------------------------------------------

let byte_rich () : Lemma (R.rich byte_rep)
  = base_facts ();
    assert (byte_rep.R.size_ok msize /\ byte_rep.R.ysize_ok ywords);
    FStar.Classical.forall_intro (FStar.Classical.move_requires odd_storable);
    FStar.Classical.forall_intro (FStar.Classical.move_requires major_storable);
    FStar.Classical.forall_intro (FStar.Classical.move_requires young_storable)

let byte_major_reads (m: M.mheap) (g: heap)
  : Lemma (requires byte_rep.R.repr m g)
          (ensures byte_rep.R.size_ok m.M.size /\
                   R.reads_model (byte_rep.R.rsize g) (byte_rep.R.rhd g) (byte_rep.R.read g) m)
  = brepr_reads m g

let byte_major_onto (m: M.mheap)
  : Lemma (requires R.representable byte_rep m) (ensures exists (g: heap). byte_rep.R.repr m g)
  = brep_ok_intro m;
    conc_repr m

let byte_major () : Lemma (R.faithful_major byte_rep)
  = FStar.Classical.forall_intro_2 (fun m g -> FStar.Classical.move_requires (byte_major_reads m) g);
    FStar.Classical.forall_intro (FStar.Classical.move_requires byte_major_onto)

let byte_young_reads (m: M.mheap) (ms: minor_state)
  : Lemma (requires byte_rep.R.yrepr m ms)
          (ensures byte_rep.R.ysize_ok m.M.size /\
                   R.reads_model (byte_rep.R.ysize ms) (byte_rep.R.yhd ms) (byte_rep.R.yread ms) m)
  = yrepr_elim m ms;
    yrepr_reads m ms

let byte_yinit (n: nat) : Lemma (R.yinit_ok byte_rep n)
  = if n = ywords then yinit_ok' n

let byte_yalloc (ms: minor_state) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value)
  : Lemma (R.yalloc_ok byte_rep ms sz tag vs)
  = let aux (m: M.mheap)
      : Lemma (requires byte_rep.R.yrepr m ms /\ tag <> M.infix_tag /\ L.length vs == sz /\ R.storable_all byte_rep vs)
              (ensures (match byte_rep.R.yalloc ms sz tag vs with
                        | Some (o, ms') -> M.young_free m o sz /\ byte_rep.R.yrepr (M.young_alloc m o sz tag vs) ms'
                        | None -> sz > byte_rep.R.ymax \/ ~(exists (o: nat). M.young_free m o sz)))
      = match yalloc ms sz tag vs with
        | Some _ -> yalloc_free m ms sz tag vs; yalloc_repr m ms sz tag vs
        | None -> yalloc_none m ms sz tag vs in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let byte_ywrite (ms: minor_state) (o i: nat) (v: M.value) : Lemma (R.ywrite_ok byte_rep ms o i v)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (fun m -> ywrite_ok' m ms o i v))

let byte_yreset (ms: minor_state) : Lemma (R.yreset_ok byte_rep ms)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (fun m -> yreset_ok' m ms))

let byte_young () : Lemma (R.faithful_young byte_rep)
  = FStar.Classical.forall_intro_2 (fun m ms -> FStar.Classical.move_requires (byte_young_reads m) ms);
    FStar.Classical.forall_intro byte_yinit;
    FStar.Classical.forall_intro_4 byte_yalloc;
    FStar.Classical.forall_intro_4 byte_ywrite;
    FStar.Classical.forall_intro byte_yreset

let byte_rep_faithful () : Lemma (R.faithful byte_rep)
  = byte_rich (); byte_major (); byte_young ()

/// ---------------------------------------------------------------------------
/// A degenerate relation: every byte heap "is" the empty heap
/// ---------------------------------------------------------------------------

let empty_rel (m: M.mheap) (g: heap) : prop = m == M.empty_heap 0

let bad_byte_rep : R.rep heap minor_state = { byte_rep with R.repr = empty_rel }

/// The heap of one free block, of the byte heap's size.
let one_hd (j: nat) : option M.header =
  if j = 0 then Some ({ M.wz = msize - 1; M.tag = 0; M.col = M.Blue }) else None

let one_body (w: nat) : M.value = if 0 < w && w < msize then M.VInt 1 else M.VInt 0

let one_block : M.mheap = { M.size = msize; M.hd = one_hd; M.body = one_body }

#push-options "--fuel 1"
let one_block_representable () : Lemma (R.representable bad_byte_rep one_block)
  = base_facts ();
    let m = one_block in
    let cov (w: nat) : Lemma (w < msize ==> M.covers m 0 w) = () in
    FStar.Classical.forall_intro cov;
    let blk (o: nat) : Lemma (M.is_block m o <==> o == 0) = () in
    FStar.Classical.forall_intro blk;
    assert (M.tiled m);
    let fw (w: nat) : Lemma (R.field_word m w <==> (0 < w /\ w < msize))
      = if 0 < w && w < msize then assert (M.covers m 0 w) in
    FStar.Classical.forall_intro fw;
    assert (R.canonical m);
    odd_storable 1;
    assert (bad_byte_rep.R.size_ok msize)
#pop-options

let bad_byte_rep_rejected () : Lemma (~(R.faithful bad_byte_rep))
  = one_block_representable ();
    base_facts ();
    let aux () : Lemma (requires R.faithful bad_byte_rep) (ensures False)
      = assert (exists (g: heap). bad_byte_rep.R.repr one_block g);
        assert (one_block.M.size == msize) in
    FStar.Classical.move_requires aux ()
