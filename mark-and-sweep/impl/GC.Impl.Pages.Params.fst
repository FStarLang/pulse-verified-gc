module GC.Impl.Pages.Params

friend GC.Spec.Pages.Params

open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout

module U64 = FStar.UInt64

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let page_wsize_u64 = assert_norm (page_wsize == 4096); 4096UL

let n_cls_u64 = 31UL

/// The class table, value by value.
let cls_values () : Lemma (cls 0 == 2 /\
                            cls 1 == 3 /\
                            cls 2 == 4 /\
                            cls 3 == 5 /\
                            cls 4 == 6 /\
                            cls 5 == 7 /\
                            cls 6 == 8 /\
                            cls 7 == 10 /\
                            cls 8 == 12 /\
                            cls 9 == 14 /\
                            cls 10 == 16 /\
                            cls 11 == 17 /\
                            cls 12 == 19 /\
                            cls 13 == 22 /\
                            cls 14 == 25 /\
                            cls 15 == 28 /\
                            cls 16 == 32 /\
                            cls 17 == 33 /\
                            cls 18 == 37 /\
                            cls 19 == 42 /\
                            cls 20 == 47 /\
                            cls 21 == 53 /\
                            cls 22 == 59 /\
                            cls 23 == 65 /\
                            cls 24 == 73 /\
                            cls 25 == 81 /\
                            cls 26 == 89 /\
                            cls 27 == 99 /\
                            cls 28 == 108 /\
                            cls 29 == 118 /\
                            cls 30 == 128)
  = assert_norm (cls 0 == 2); assert_norm (cls 1 == 3); assert_norm (cls 2 == 4); assert_norm (cls 3 == 5); assert_norm (cls 4 == 6); assert_norm (cls 5 == 7); assert_norm (cls 6 == 8); assert_norm (cls 7 == 10); assert_norm (cls 8 == 12); assert_norm (cls 9 == 14); assert_norm (cls 10 == 16); assert_norm (cls 11 == 17); assert_norm (cls 12 == 19); assert_norm (cls 13 == 22); assert_norm (cls 14 == 25); assert_norm (cls 15 == 28); assert_norm (cls 16 == 32); assert_norm (cls 17 == 33); assert_norm (cls 18 == 37); assert_norm (cls 19 == 42); assert_norm (cls 20 == 47); assert_norm (cls 21 == 53); assert_norm (cls 22 == 59); assert_norm (cls 23 == 65); assert_norm (cls 24 == 73); assert_norm (cls 25 == 81); assert_norm (cls 26 == 89); assert_norm (cls 27 == 99); assert_norm (cls 28 == 108); assert_norm (cls 29 == 118); assert_norm (cls 30 == 128)

/// A chain of tests on the class number; every class is a constant.
let cls_u64 c =
  cls_values ();
  if c = 0UL then 2UL
  else if c = 1UL then 3UL
  else if c = 2UL then 4UL
  else if c = 3UL then 5UL
  else if c = 4UL then 6UL
  else if c = 5UL then 7UL
  else if c = 6UL then 8UL
  else if c = 7UL then 10UL
  else if c = 8UL then 12UL
  else if c = 9UL then 14UL
  else if c = 10UL then 16UL
  else if c = 11UL then 17UL
  else if c = 12UL then 19UL
  else if c = 13UL then 22UL
  else if c = 14UL then 25UL
  else if c = 15UL then 28UL
  else if c = 16UL then 32UL
  else if c = 17UL then 33UL
  else if c = 18UL then 37UL
  else if c = 19UL then 42UL
  else if c = 20UL then 47UL
  else if c = 21UL then 53UL
  else if c = 22UL then 59UL
  else if c = 23UL then 65UL
  else if c = 24UL then 73UL
  else if c = 25UL then 81UL
  else if c = 26UL then 89UL
  else if c = 27UL then 99UL
  else if c = 28UL then 108UL
  else if c = 29UL then 118UL
  else 128UL
