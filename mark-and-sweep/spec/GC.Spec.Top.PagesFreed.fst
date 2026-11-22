/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesFreed - the words a page-sweep step frees, as the
/// model's sum over addresses
/// ---------------------------------------------------------------------------
///
/// `PagesFree.freed_words_of g pm p` counts on the byte heap: the sum, over
/// the objects of the walk (`objects zero_addr g`, a sequence), of the size
/// (header included) of those the step frees.  The specification's
/// `freed_words` is a sum over model addresses (`Heap.sum size swept_words`).
/// `freed_reindex`: the two are equal.  The walk's objects are distinct
/// (`HeapModel.objects_is_vertex_set`), and each is the block at its model
/// address (`ByteFacts.obj_maddr`).

module GC.Spec.Top.PagesFreed

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteFacts
module M = GC.Spec.Top.Heap
module U64 = FStar.UInt64
module Seq = FStar.Seq
module PF = GC.Spec.Top.PagesFree
module HG = GC.Spec.HeapGraph
module HM = GC.Spec.HeapModel
module Gr = GC.Spec.Graph

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Sums
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec sum_ext (n: nat) (f g: nat -> GTot nat)
  : Lemma (requires forall (o: nat). o < n ==> f o == g o) (ensures M.sum n f == M.sum n g) (decreases n)
  = if n > 0 then sum_ext (n - 1) f g

let rec sum_add (n: nat) (f g h: nat -> GTot nat)
  : Lemma (requires forall (o: nat). o < n ==> h o == f o + g o)
          (ensures M.sum n h == M.sum n f + M.sum n g) (decreases n)
  = if n > 0 then sum_add (n - 1) f g h

let ind (o0 c: nat) (o: nat) : GTot nat = if o = o0 then c else 0

let rec sum_ind (n o0 c: nat) : Lemma (ensures M.sum n (ind o0 c) == (if o0 < n then c else 0)) (decreases n)
  = if n > 0 then sum_ind (n - 1) o0 c

let zero (o: nat) : GTot nat = 0

let rec sum_zero (n: nat) : Lemma (ensures M.sum n zero == 0) (decreases n)
  = if n > 0 then sum_zero (n - 1)
#pop-options

/// ---------------------------------------------------------------------------
/// The walk's objects are distinct
/// ---------------------------------------------------------------------------

let rec distinct (s: Seq.seq obj_addr) : Tot bool (decreases Seq.length s) =
  if Seq.length s = 0 then true
  else not (Seq.mem (Seq.head s) (Seq.tail s)) && distinct (Seq.tail s)

#push-options "--fuel 1 --ifuel 1"
let rec distinct_of_vertex_set (s: Seq.seq obj_addr)
  : Lemma (requires Gr.is_vertex_set (HG.coerce_to_vertex_list s)) (ensures distinct s)
          (decreases Seq.length s)
  = if Seq.length s > 0 then begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      Seq.lemma_eq_elim s (Seq.cons hd tl);
      HG.coerce_cons_lemma hd tl;
      HG.coerce_mem_lemma tl hd;
      let l = HG.coerce_to_vertex_list s in
      assert (Seq.head l == hd);
      Seq.lemma_eq_elim (Seq.tail l) (HG.coerce_to_vertex_list tl);
      distinct_of_vertex_set tl
    end
#pop-options

let objects_distinct (g: heap) : Lemma (distinct (objects zero_addr g))
  = HM.objects_is_vertex_set g;
    distinct_of_vertex_set (objects zero_addr g)

/// ---------------------------------------------------------------------------
/// The count, by address
/// ---------------------------------------------------------------------------

/// What the step frees at model address `o`, counting the objects of `s`.
let fcount (g: heap) (pm: page_map) (p: nat{p < n_pages}) (s: Seq.seq obj_addr) (o: nat) : GTot nat =
  if pos o + 8 < heap_size && Seq.mem (obj_of o) s && PF.freed_block g pm p (obj_of o)
  then whsize g (obj_of o) else 0

#push-options "--fuel 1 --z3rlimit 40"
let rec reindex (g: heap) (pm: page_map) (p: nat{p < n_pages}) (s: Seq.seq obj_addr)
  : Lemma (requires distinct s /\ (forall (x: obj_addr). Seq.mem x s ==> Seq.mem x (objects zero_addr g)))
          (ensures PF.freed_in g pm p s == M.sum msize (fcount g pm p s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then begin
      sum_ext msize (fcount g pm p s) zero;
      sum_zero msize
    end
    else begin
      let hd = Seq.head s in
      let tl = Seq.tail s in
      Seq.lemma_eq_elim s (Seq.cons hd tl);
      let mem_s (x: obj_addr) : Lemma (Seq.mem x s <==> (x == hd \/ Seq.mem x tl))
        = Seq.mem_cons hd tl in
      FStar.Classical.forall_intro mem_s;
      reindex g pm p tl;
      obj_maddr g hd;
      let o0 = maddr hd in
      let c = if PF.freed_block g pm p hd then whsize g hd else 0 in
      let pt (o: nat) : Lemma (o < msize ==> fcount g pm p s o == fcount g pm p tl o + ind o0 c o)
        = if o < msize && pos o + 8 < heap_size then begin
            maddr_obj o;
            if o = o0 then () else assert (obj_of o =!= hd)
          end in
      FStar.Classical.forall_intro pt;
      sum_add msize (fcount g pm p tl) (ind o0 c) (fcount g pm p s);
      sum_ind msize o0 c;
      assert (o0 < msize);
      assert (PF.freed_in g pm p s == c + PF.freed_in g pm p tl);
      assert (M.sum msize (fcount g pm p s) == M.sum msize (fcount g pm p tl) + c)
    end
#pop-options

/// **The freed words, reindexed**: the byte-level count over the walk's
/// objects is the model's sum over addresses.
let freed_reindex (g: heap) (pm: page_map) (p: nat{p < n_pages})
  : Lemma (PF.freed_words_of g pm p == M.sum msize (fcount g pm p (objects zero_addr g)))
  = objects_distinct g;
    reindex g pm p (objects zero_addr g)
