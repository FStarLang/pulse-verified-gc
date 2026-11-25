/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWNames - the pages witness runs name only what they reach
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  Every program event of both pages witness runs names
/// only blocks reached from the roots along major fields, or young roots
/// (`TrNames.enamed`).  So every reference program they are transparent
/// with names only what it reaches (`TrNames.names_of`): T1's part 2 applies.

module GC.Spec.Top.PWNames

open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
open GC.Spec.Top.PWRun
open GC.Spec.Top.PWPre
open GC.Spec.Top.TrNames
module M = GC.Spec.Top.Heap
module L = FStar.List.Tot
module RF = GC.Spec.Top.RunFacts
module FWS = GC.Spec.Top.FFWStep

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// On the description's world, then on every world the configuration has.
let enamed_wd (x: config pc) (d: dsc) (e: event)
  : Lemma (requires holds x d /\ enamed (wd x d) e) (ensures enamed (wv x) e)
  = views_wd x d;
    FWS.wheq_sym (vw x) (wd x d);
    enamed_wheq (wd x d) (wv x) e

/// A root at a block in use: reached.
let rooted_r (x: config pc) (d: dsc) (o: nat)
  : Lemma (requires holds x d /\ L.memP (M.VPtr (M.Major o)) d.drt /\ iu x o == true)
          (ensures rooted (wd x d) o)
  = res_iu x o;
    rooted_root (wd x d) o o

/// A field of a reached block, resolving to `o'`: reached.
let rooted_f (x: config pc) (d: dsc) (o i a o': nat)
  : Lemma (requires holds x d /\ rooted (wd x d) o /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)) /\
                    M.scannable (Some?.v (d.db o)).bt /\ i < (Some?.v (d.db o)).bw /\
                    vi (Some?.v (d.db o)).bf i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some o')
          (ensures rooted (wd x d) o')
  = blk x d o;
    rooted_step (wd x d) o o'

/// A pointer to a reached block is a named value.
let vn_ptr (w: M.world) (a o: nat)
  : Lemma (requires M.resolve w.M.maj a == Some o /\ rooted w o) (ensures vnamed w (M.VPtr (M.Major a)))
  = ()

let vn_int (w: M.world) (n: int) : Lemma (vnamed w (M.VInt n)) = ()

let vn_young (w: M.world) (a: nat)
  : Lemma (requires L.memP (M.VPtr (M.Young a)) w.M.roots /\ Some? (M.resolve w.M.yng a))
          (ensures vnamed w (M.VPtr (M.Young a)))
  = ()

#push-options "--fuel 4"
let en_l1 (w: M.world) (u: M.value) : Lemma (requires vnamed w u) (ensures forall (v: M.value). L.memP v [u] ==> vnamed w v) = ()
let en_l2 (w: M.world) (u v: M.value)
  : Lemma (requires vnamed w u /\ vnamed w v) (ensures forall (z: M.value). L.memP z [u; v] ==> vnamed w z) = ()
let en_l3 (w: M.world) (u v t: M.value)
  : Lemma (requires vnamed w u /\ vnamed w v /\ vnamed w t) (ensures forall (z: M.value). L.memP z [u; v; t] ==> vnamed w z) = ()
#pop-options

/// ---------------------------------------------------------------------------
/// Events 0-6
/// ---------------------------------------------------------------------------

let n_pre (i: nat) : prop =
  (i == 0 ==> enamed (wv (x0 ())) e0) /\ (i == 1 ==> enamed (wv (x1 ())) e1) /\
  (i == 2 ==> enamed (wv (x2 ())) (e2 ())) /\ (i == 3 ==> enamed (wv (x3 ())) e3) /\
  (i == 4 ==> enamed (wv (x4 ())) (e4 ())) /\ (i == 5 ==> enamed (wv (x5 ())) (e5 ())) /\
  (i == 6 ==> enamed (wv (x6 ())) (e6 ()))

let names_6 () : Lemma (requires pw_room /\ cok) (ensures enamed (wv (x6 ())) (e6 ()))
  = h6 (); distinct ();
    holds_elim (x6 ()) (d6 ());
    db6 (xA ());
    blk (x6 ()) (d6 ()) (xA ());
    assert ((d6 ()).drt == [vK (); vC (); vB (); vA ()]);
    mem_hd (vA ()) []; mem_tl (vB ()) (vA ()) [vA ()]; mem_tl (vC ()) (vA ()) [vB (); vA ()];
    mem_tl (vK ()) (vA ()) [vC (); vB (); vA ()];
    rooted_r (x6 ()) (d6 ()) (xA ());
    res_iu (x6 ()) (xA ());
    en_l1 (wd (x6 ()) (d6 ())) (vA ()); enamed_wd (x6 ()) (d6 ()) (e6 ())

#push-options "--z3rlimit 40"
let names_pre () : Lemma (requires pw_room /\ cok)
  (ensures enamed (wv (x0 ())) e0 /\ enamed (wv (x1 ())) e1 /\ enamed (wv (x2 ())) (e2 ()) /\
           enamed (wv (x3 ())) e3 /\ enamed (wv (x4 ())) (e4 ()) /\ enamed (wv (x5 ())) (e5 ()) /\
           enamed (wv (x6 ())) (e6 ()))
  = init_holds (); h1 (); h2 (); h3 (); h4 (); h5 (); h6 (); distinct ();
    st_vals ();
    // 0, 1, 3: integers
    en_l2 (wd (x0 ()) d0) i1 i1; enamed_wd (x0 ()) d0 e0;
    en_l1 (wd (x1 ()) (d1 ())) i1; enamed_wd (x1 ()) (d1 ()) e1;
    en_l3 (wd (x3 ()) (d3 ())) i1 iw i1; enamed_wd (x3 ()) (d3 ()) e3;
    // 2: B, a root
    holds_elim (x2 ()) (d2 ());
    blk (x2 ()) (d2 ()) (xB ());
    mem_hd (vB ()) (d1 ()).drt;
    rooted_r (x2 ()) (d2 ()) (xB ());
    res_iu (x2 ()) (xB ());
    en_l1 (wd (x2 ()) (d2 ())) (vB ()); enamed_wd (x2 ()) (d2 ()) (e2 ());
    // 4: A.0 := B, both roots
    holds_elim (x4 ()) (d4 ());
    db4 (xA ()); db4 (xB ()); db4 (xK ());
    blk (x4 ()) (d4 ()) (xA ()); blk (x4 ()) (d4 ()) (xB ());
    assert ((d4 ()).drt == [vK (); vC (); vB (); vA ()]);
    mem_hd (vA ()) []; mem_tl (vB ()) (vA ()) [vA ()]; mem_tl (vC ()) (vA ()) [vB (); vA ()];
    mem_tl (vK ()) (vA ()) [vC (); vB (); vA ()];
    mem_hd (vB ()) [vA ()]; mem_tl (vC ()) (vB ()) [vB (); vA ()]; mem_tl (vK ()) (vB ()) [vC (); vB (); vA ()];
    mem_hd (vK ()) [vC (); vB (); vA ()];
    rooted_r (x4 ()) (d4 ()) (xA ()); rooted_r (x4 ()) (d4 ()) (xB ());
    res_iu (x4 ()) (xB ());
    enamed_wd (x4 ()) (d4 ()) (e4 ());
    // 5: B.0 := K + 2, both roots
    holds_elim (x5 ()) (d5 ());
    kd5 ();
    blk (x5 ()) (d5 ()) (xB ()); blk (x5 ()) (d5 ()) (xK ());
    l3 i1 iw i1;
    assert ((d5 ()).drt == [vK (); vC (); vB (); vA ()]);
    rooted_r (x5 ()) (d5 ()) (xB ()); rooted_r (x5 ()) (d5 ()) (xK ());
    res_infix (mx (x5 ())) (xK ());
    enamed_wd (x5 ()) (d5 ()) (e5 ());
    names_6 ()
#pop-options
