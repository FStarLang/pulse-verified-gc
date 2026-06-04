/// ---------------------------------------------------------------------------
/// GC.Gen.ChunkedCheney -- Chunked-major Cheney forwarding core
/// ---------------------------------------------------------------------------

module GC.Gen.ChunkedCheney

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote

module MH = GC.Spec.MajorHeap
module SpecAlloc = GC.Spec.Allocator
module ChunkedPromote = GC.Gen.ChunkedPromote
module Dense = GC.Gen.Cheney
module AllocProps = GC.Gen.AllocProps

let single_chunk_cheney_state (cs: Dense.cheney_state)
  : GTot chunked_cheney_state =
  { ccs_major = MH.single_chunk_major_heap cs.cs_major;
    ccs_fp    = cs.cs_fp;
    ccs_fwd   = cs.cs_fwd;
    ccs_queue = cs.cs_queue }

let chunked_cheney_forward_normal
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : GTot chunked_cheney_state =
  if not (Seq.mem addr (minor_objects minor)) || cs.ccs_fwd addr <> 0UL
  then cs
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then cs
    else
      let res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor cs.ccs_major addr cs.ccs_fp wz fuel in
      if res.new_addr = 0UL then cs
      else
        { ccs_major = res.major_out;
          ccs_fp    = res.fp_out;
          ccs_fwd   = extend_forwarding cs.ccs_fwd addr res.new_addr;
          ccs_queue = Seq.append cs.ccs_queue (Seq.create 1 addr) }

let chunked_cheney_forward_one
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : GTot chunked_cheney_state =
  if cs.ccs_fwd addr <> 0UL then cs
  else if is_infix_in_minor minor addr then
    let parent = infix_parent minor addr in
    let cs' = chunked_cheney_forward_normal minor cs parent fuel in
    if cs'.ccs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (cs'.ccs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then
      let delta = U64.v addr - U64.v parent in
      { cs' with ccs_fwd = extend_forwarding cs'.ccs_fwd addr
                              (U64.uint_to_t
                                (U64.v (cs'.ccs_fwd parent) + delta)) }
    else cs'
  else
    chunked_cheney_forward_normal minor cs addr fuel

let chunked_cheney_forward_normal_noop
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma (requires ~(Seq.mem addr (minor_objects minor)) \/
                    cs.ccs_fwd addr <> 0UL)
          (ensures chunked_cheney_forward_normal minor cs addr fuel == cs)
  = ()

let chunked_cheney_forward_normal_noop_wz0
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma (requires Seq.mem addr (minor_objects minor) /\
                    cs.ccs_fwd addr = 0UL /\
                    minor_wosize minor addr = 0)
          (ensures chunked_cheney_forward_normal minor cs addr fuel == cs)
  = ()

let chunked_cheney_forward_normal_noop_oom
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma
      (requires Seq.mem addr (minor_objects minor) /\
                cs.ccs_fwd addr = 0UL /\
                minor_wosize minor addr > 0 /\
                (ChunkedPromote.chunked_promote_object_with_fuel
                  minor cs.ccs_major addr cs.ccs_fp
                  (minor_wosize minor addr) fuel).new_addr = 0UL)
      (ensures chunked_cheney_forward_normal minor cs addr fuel == cs)
  = ()

let chunked_cheney_forward_normal_success
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma
      (requires Seq.mem addr (minor_objects minor) /\
                cs.ccs_fwd addr = 0UL /\
                minor_wosize minor addr > 0 /\
                (ChunkedPromote.chunked_promote_object_with_fuel
                  minor cs.ccs_major addr cs.ccs_fp
                  (minor_wosize minor addr) fuel).new_addr <> 0UL)
      (ensures
        (let wz = minor_wosize minor addr in
         let res =
           ChunkedPromote.chunked_promote_object_with_fuel
             minor cs.ccs_major addr cs.ccs_fp wz fuel in
         chunked_cheney_forward_normal minor cs addr fuel ==
         { ccs_major = res.major_out;
           ccs_fp    = res.fp_out;
           ccs_fwd   = extend_forwarding cs.ccs_fwd addr res.new_addr;
           ccs_queue = Seq.append cs.ccs_queue (Seq.create 1 addr) }))
  = ()

let chunked_cheney_forward_normal_other_fwd
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (y: U64.t) (fuel: nat)
  : Lemma (requires y <> addr)
          (ensures
            (chunked_cheney_forward_normal minor cs addr fuel).ccs_fwd y ==
            cs.ccs_fwd y)
  = ()

let chunked_cheney_forward_one_noop
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma (requires cs.ccs_fwd addr <> 0UL \/
                    (~(Seq.mem addr (minor_objects minor)) /\
                     ~(is_infix_in_minor minor addr)))
          (ensures chunked_cheney_forward_one minor cs addr fuel == cs)
  = ()

let chunked_cheney_forward_one_normal
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma (requires cs.ccs_fwd addr = 0UL /\
                    ~(is_infix_in_minor minor addr))
          (ensures
            chunked_cheney_forward_one minor cs addr fuel ==
            chunked_cheney_forward_normal minor cs addr fuel)
  = ()

let chunked_cheney_forward_one_infix
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma (requires cs.ccs_fwd addr = 0UL /\
                    is_infix_in_minor minor addr /\
                    U64.v addr >= U64.v (infix_parent minor addr))
          (ensures
            (let parent = infix_parent minor addr in
             let cs' = chunked_cheney_forward_normal minor cs parent fuel in
             let r = chunked_cheney_forward_one minor cs addr fuel in
             r.ccs_major == cs'.ccs_major /\
             r.ccs_fp == cs'.ccs_fp /\
             r.ccs_queue == cs'.ccs_queue))
  = ()

let chunked_cheney_forward_one_infix_guard_pass
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma (requires cs.ccs_fwd addr = 0UL /\
                    is_infix_in_minor minor addr /\
                    (let parent = infix_parent minor addr in
                     let cs' =
                       chunked_cheney_forward_normal minor cs parent fuel in
                     cs'.ccs_fwd parent <> 0UL /\
                     U64.v addr >= U64.v parent /\
                     U64.v (cs'.ccs_fwd parent) +
                       (U64.v addr - U64.v parent) < heap_size))
          (ensures
            (let parent = infix_parent minor addr in
             let cs' = chunked_cheney_forward_normal minor cs parent fuel in
             let delta = U64.v addr - U64.v parent in
             let sum = U64.uint_to_t (U64.v (cs'.ccs_fwd parent) + delta) in
             let r = chunked_cheney_forward_one minor cs addr fuel in
             r.ccs_fwd == extend_forwarding cs'.ccs_fwd addr sum /\
             r.ccs_major == cs'.ccs_major /\
             r.ccs_fp == cs'.ccs_fp /\
             r.ccs_queue == cs'.ccs_queue))
  = ()

let chunked_cheney_forward_one_infix_guard_fail
  (minor: minor_state) (cs: chunked_cheney_state) (addr: U64.t)
  (fuel: nat)
  : Lemma (requires cs.ccs_fwd addr = 0UL /\
                    is_infix_in_minor minor addr /\
                    (let parent = infix_parent minor addr in
                     let cs' =
                       chunked_cheney_forward_normal minor cs parent fuel in
                     ~(cs'.ccs_fwd parent <> 0UL &&
                       U64.v addr >= U64.v parent &&
                       U64.v (cs'.ccs_fwd parent) +
                         (U64.v addr - U64.v parent) < heap_size)))
          (ensures
            chunked_cheney_forward_one minor cs addr fuel ==
            chunked_cheney_forward_normal minor cs
              (infix_parent minor addr) fuel)
  = ()

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_cheney_forward_normal_default_single_chunk_compat
  (minor: minor_state) (cs: Dense.cheney_state) (addr: U64.t)
  : Lemma
      (ensures
        chunked_cheney_forward_normal
          minor (single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        single_chunk_cheney_state
          (Dense.cheney_forward_normal minor cs addr))
  =
  if not (Seq.mem addr (minor_objects minor)) || cs.cs_fwd addr <> 0UL
  then begin
    Dense.cheney_forward_normal_noop minor cs addr;
    chunked_cheney_forward_normal_noop
      minor (single_chunk_cheney_state cs) addr
      SpecAlloc.alloc_search_fuel
  end
  else
    let wz = minor_wosize minor addr in
    if wz = 0 then begin
      Dense.cheney_forward_normal_noop_wz0 minor cs addr;
      chunked_cheney_forward_normal_noop_wz0
        minor (single_chunk_cheney_state cs) addr
        SpecAlloc.alloc_search_fuel
    end
    else begin
      AllocProps.alloc_spec_obj_valid cs.cs_major cs.cs_fp wz;
      ChunkedPromote.chunked_promote_object_with_fuel_single_chunk_compat
        minor cs.cs_major addr cs.cs_fp wz SpecAlloc.alloc_search_fuel;
      let dense_res = promote_object minor cs.cs_major addr cs.cs_fp wz in
      let chunked_res =
        ChunkedPromote.chunked_promote_object_with_fuel
          minor (MH.single_chunk_major_heap cs.cs_major) addr cs.cs_fp wz
          SpecAlloc.alloc_search_fuel in
      assert (chunked_res.major_out ==
              MH.single_chunk_major_heap dense_res.major_out);
      assert (chunked_res.fp_out == dense_res.fp_out);
      assert (chunked_res.new_addr == dense_res.new_addr);
      if dense_res.new_addr = 0UL then begin
        Dense.cheney_forward_normal_noop_oom minor cs addr;
        chunked_cheney_forward_normal_noop_oom
          minor (single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel
      end
      else begin
        Dense.cheney_forward_normal_success minor cs addr;
        chunked_cheney_forward_normal_success
          minor (single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel
      end
    end
#pop-options

#push-options "--z3rlimit 5 --fuel 0 --ifuel 0 --split_queries always"
let chunked_cheney_forward_one_default_single_chunk_compat
  (minor: minor_state) (cs: Dense.cheney_state) (addr: U64.t)
  : Lemma
      (ensures
        chunked_cheney_forward_one
          minor (single_chunk_cheney_state cs) addr
          SpecAlloc.alloc_search_fuel ==
        single_chunk_cheney_state
          (Dense.cheney_forward_one minor cs addr))
  =
  if cs.cs_fwd addr <> 0UL then begin
    Dense.cheney_forward_one_noop minor cs addr;
    chunked_cheney_forward_one_noop
      minor (single_chunk_cheney_state cs) addr
      SpecAlloc.alloc_search_fuel
  end
  else if is_infix_in_minor minor addr then begin
    let parent = infix_parent minor addr in
    chunked_cheney_forward_normal_default_single_chunk_compat minor cs parent;
    let dense_parent = Dense.cheney_forward_normal minor cs parent in
    let chunked_parent =
      chunked_cheney_forward_normal
        minor (single_chunk_cheney_state cs) parent
        SpecAlloc.alloc_search_fuel in
    assert (chunked_parent == single_chunk_cheney_state dense_parent);
    assert (chunked_parent.ccs_fwd == dense_parent.cs_fwd);
    assert (chunked_parent.ccs_major ==
            MH.single_chunk_major_heap dense_parent.cs_major);
    assert (chunked_parent.ccs_fp == dense_parent.cs_fp);
    assert (chunked_parent.ccs_queue == dense_parent.cs_queue);
    if dense_parent.cs_fwd parent <> 0UL &&
       U64.v addr >= U64.v parent &&
       U64.v (dense_parent.cs_fwd parent) + (U64.v addr - U64.v parent) < heap_size
    then begin
      assert (chunked_parent.ccs_fwd parent <> 0UL);
      assert (U64.v (chunked_parent.ccs_fwd parent) ==
              U64.v (dense_parent.cs_fwd parent));
      Dense.cheney_forward_one_infix_guard_pass minor cs addr;
      chunked_cheney_forward_one_infix_guard_pass
        minor (single_chunk_cheney_state cs) addr
        SpecAlloc.alloc_search_fuel
    end
    else begin
      assert (~(chunked_parent.ccs_fwd parent <> 0UL &&
                U64.v addr >= U64.v parent &&
                U64.v (chunked_parent.ccs_fwd parent) +
                  (U64.v addr - U64.v parent) < heap_size));
      Dense.cheney_forward_one_infix_guard_fail minor cs addr;
      chunked_cheney_forward_one_infix_guard_fail
        minor (single_chunk_cheney_state cs) addr
        SpecAlloc.alloc_search_fuel
    end
  end
  else begin
    Dense.cheney_forward_one_normal minor cs addr;
    chunked_cheney_forward_one_normal
      minor (single_chunk_cheney_state cs) addr
      SpecAlloc.alloc_search_fuel;
    chunked_cheney_forward_normal_default_single_chunk_compat minor cs addr
  end
#pop-options
