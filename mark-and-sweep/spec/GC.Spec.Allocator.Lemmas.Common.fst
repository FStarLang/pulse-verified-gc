module GC.Spec.Allocator.Lemmas.Common

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Free-list validity: every node in the free list is a member of objects zero_addr g.
/// This is an invariant maintained by sweep and allocation.
#restart-solver
#push-options "--z3rlimit 12 --fuel 2 --ifuel 1"
let rec fl_valid (g: heap) (fp: U64.t) (fuel: nat) : Tot prop (decreases fuel) =
  if fuel = 0 then True
  else if fp = 0UL then True
  else if U64.v fp < U64.v mword then True
  else if U64.v fp >= heap_size then True
  else if U64.v fp % U64.v mword <> 0 then True
  else
    Seq.mem fp (objects zero_addr g) /\
    U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
    (let hd = hd_address (fp <: obj_addr) in
     let next_fp = read_word g (fp <: obj_addr) in
     U64.v hd + 16 <= heap_size ==>
     next_fp <> fp /\  // no self-loops in the free list
     fl_valid g next_fp (fuel - 1))
#pop-options

/// If fl_valid, cur_fp is a member of objects.
let fl_valid_gives_mem (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    fl_valid g fp fuel)
          (ensures Seq.mem fp (objects zero_addr g))
  = ()

/// If fl_valid, cur_fp has wosize >= 1.
let fl_valid_gives_wosize (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    fl_valid g fp fuel)
          (ensures U64.v (wosize_of_object (fp <: obj_addr) g) >= 1)
  = ()

/// If fl_valid, the first link is not a self-loop and the tail is valid.
let fl_valid_next (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    fl_valid g fp fuel)
          (ensures (let obj : obj_addr = fp in
                    let hd = hd_address obj in
                    U64.v hd + 16 <= heap_size ==>
                    read_word g obj <> fp /\
                    fl_valid g (read_word g obj) (fuel - 1)))
  = ()

/// fl_valid introduction forms.
let fl_valid_null (g: heap) (fuel: nat)
  : Lemma (requires fuel > 0)
          (ensures fl_valid g 0UL fuel)
  = ()

let fl_valid_step (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    Seq.mem fp (objects zero_addr g) /\
                    U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
                    (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
                      read_word g (fp <: obj_addr) <> fp /\
                      fl_valid g (read_word g (fp <: obj_addr)) (fuel - 1)))
          (ensures fl_valid g fp fuel)
  = ()

let fl_valid_elim (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    U64.v fp >= U64.v mword /\
                    U64.v fp < heap_size /\
                    U64.v fp % U64.v mword = 0 /\
                    fl_valid g fp fuel)
          (ensures Seq.mem fp (objects zero_addr g) /\
                   U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
                   (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
                     read_word g (fp <: obj_addr) <> fp /\
                     fl_valid g (read_word g (fp <: obj_addr)) (fuel - 1)))
  = ()

let fl_valid_zero (g: heap) (fp: U64.t)
  : Lemma (fl_valid g fp 0)
  = ()

let fl_valid_terminal (g: heap) (fp: U64.t) (fuel: nat)
  : Lemma (requires fuel > 0 /\
                    (fp = 0UL \/ U64.v fp < U64.v mword \/ U64.v fp >= heap_size \/
                     U64.v fp % U64.v mword <> 0))
          (ensures fl_valid g fp fuel)
  = ()

/// fl_valid weakening: more fuel implies less fuel.
#push-options "--z3rlimit 12 --fuel 2 --ifuel 1"
let rec fl_valid_weaken (g: heap) (fp: U64.t) (fuel_strong fuel_weak: nat)
  : Lemma (requires fl_valid g fp fuel_strong /\ fuel_weak <= fuel_strong)
          (ensures fl_valid g fp fuel_weak)
          (decreases fuel_weak)
  = if fuel_weak = 0 then ()
    else if fp = 0UL then ()
    else if U64.v fp < U64.v mword then ()
    else if U64.v fp >= heap_size then ()
    else if U64.v fp % U64.v mword <> 0 then ()
    else begin
      let obj : obj_addr = fp in
      let hd = hd_address obj in
      if U64.v hd + 16 <= heap_size then
        fl_valid_weaken g (read_word g obj) (fuel_strong - 1) (fuel_weak - 1)
      else ()
    end
#pop-options
