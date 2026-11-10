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

/// A match on the class number, every class a constant: KaRaMeL emits a
/// `switch`, which the C compiler makes a table.
let cls_u64 c =
  cls_values ();
  match c with
  | 0UL -> 2UL
  | 1UL -> 3UL
  | 2UL -> 4UL
  | 3UL -> 5UL
  | 4UL -> 6UL
  | 5UL -> 7UL
  | 6UL -> 8UL
  | 7UL -> 10UL
  | 8UL -> 12UL
  | 9UL -> 14UL
  | 10UL -> 16UL
  | 11UL -> 17UL
  | 12UL -> 19UL
  | 13UL -> 22UL
  | 14UL -> 25UL
  | 15UL -> 28UL
  | 16UL -> 32UL
  | 17UL -> 33UL
  | 18UL -> 37UL
  | 19UL -> 42UL
  | 20UL -> 47UL
  | 21UL -> 53UL
  | 22UL -> 59UL
  | 23UL -> 65UL
  | 24UL -> 73UL
  | 25UL -> 81UL
  | 26UL -> 89UL
  | 27UL -> 99UL
  | 28UL -> 108UL
  | 29UL -> 118UL
  | _ -> 128UL


/// The slots per page, value by value.
let ns_values () : Lemma (n_slots 0 == 2048 /\
                          n_slots 1 == 1365 /\
                          n_slots 2 == 1024 /\
                          n_slots 3 == 819 /\
                          n_slots 4 == 682 /\
                          n_slots 5 == 585 /\
                          n_slots 6 == 512 /\
                          n_slots 7 == 409 /\
                          n_slots 8 == 341 /\
                          n_slots 9 == 292 /\
                          n_slots 10 == 256 /\
                          n_slots 11 == 240 /\
                          n_slots 12 == 215 /\
                          n_slots 13 == 186 /\
                          n_slots 14 == 163 /\
                          n_slots 15 == 146 /\
                          n_slots 16 == 128 /\
                          n_slots 17 == 124 /\
                          n_slots 18 == 110 /\
                          n_slots 19 == 97 /\
                          n_slots 20 == 87 /\
                          n_slots 21 == 77 /\
                          n_slots 22 == 69 /\
                          n_slots 23 == 63 /\
                          n_slots 24 == 56 /\
                          n_slots 25 == 50 /\
                          n_slots 26 == 46 /\
                          n_slots 27 == 41 /\
                          n_slots 28 == 37 /\
                          n_slots 29 == 34 /\
                          n_slots 30 == 32)
  = assert_norm (n_slots 0 == 2048); assert_norm (n_slots 1 == 1365); assert_norm (n_slots 2 == 1024); assert_norm (n_slots 3 == 819); assert_norm (n_slots 4 == 682); assert_norm (n_slots 5 == 585); assert_norm (n_slots 6 == 512); assert_norm (n_slots 7 == 409); assert_norm (n_slots 8 == 341); assert_norm (n_slots 9 == 292); assert_norm (n_slots 10 == 256); assert_norm (n_slots 11 == 240); assert_norm (n_slots 12 == 215); assert_norm (n_slots 13 == 186); assert_norm (n_slots 14 == 163); assert_norm (n_slots 15 == 146); assert_norm (n_slots 16 == 128); assert_norm (n_slots 17 == 124); assert_norm (n_slots 18 == 110); assert_norm (n_slots 19 == 97); assert_norm (n_slots 20 == 87); assert_norm (n_slots 21 == 77); assert_norm (n_slots 22 == 69); assert_norm (n_slots 23 == 63); assert_norm (n_slots 24 == 56); assert_norm (n_slots 25 == 50); assert_norm (n_slots 26 == 46); assert_norm (n_slots 27 == 41); assert_norm (n_slots 28 == 37); assert_norm (n_slots 29 == 34); assert_norm (n_slots 30 == 32)

/// A match on the class number: a `switch` in C, made a table.
let n_slots_u64 c =
  ns_values ();
  match c with
  | 0UL -> 2048UL
  | 1UL -> 1365UL
  | 2UL -> 1024UL
  | 3UL -> 819UL
  | 4UL -> 682UL
  | 5UL -> 585UL
  | 6UL -> 512UL
  | 7UL -> 409UL
  | 8UL -> 341UL
  | 9UL -> 292UL
  | 10UL -> 256UL
  | 11UL -> 240UL
  | 12UL -> 215UL
  | 13UL -> 186UL
  | 14UL -> 163UL
  | 15UL -> 146UL
  | 16UL -> 128UL
  | 17UL -> 124UL
  | 18UL -> 110UL
  | 19UL -> 97UL
  | 20UL -> 87UL
  | 21UL -> 77UL
  | 22UL -> 69UL
  | 23UL -> 63UL
  | 24UL -> 56UL
  | 25UL -> 50UL
  | 26UL -> 46UL
  | 27UL -> 41UL
  | 28UL -> 37UL
  | 29UL -> 34UL
  | _ -> 32UL


/// The class of each size, value by value.
let class_values () : Lemma (requires small_max == 128) (ensures class_of 1 == 0 /\
                             class_of 2 == 0 /\
                             class_of 3 == 1 /\
                             class_of 4 == 2 /\
                             class_of 5 == 3 /\
                             class_of 6 == 4 /\
                             class_of 7 == 5 /\
                             class_of 8 == 6 /\
                             class_of 9 == 7 /\
                             class_of 10 == 7 /\
                             class_of 11 == 8 /\
                             class_of 12 == 8 /\
                             class_of 13 == 9 /\
                             class_of 14 == 9 /\
                             class_of 15 == 10 /\
                             class_of 16 == 10 /\
                             class_of 17 == 11 /\
                             class_of 18 == 12 /\
                             class_of 19 == 12 /\
                             class_of 20 == 13 /\
                             class_of 21 == 13 /\
                             class_of 22 == 13 /\
                             class_of 23 == 14 /\
                             class_of 24 == 14 /\
                             class_of 25 == 14 /\
                             class_of 26 == 15 /\
                             class_of 27 == 15 /\
                             class_of 28 == 15 /\
                             class_of 29 == 16 /\
                             class_of 30 == 16 /\
                             class_of 31 == 16 /\
                             class_of 32 == 16 /\
                             class_of 33 == 17 /\
                             class_of 34 == 18 /\
                             class_of 35 == 18 /\
                             class_of 36 == 18 /\
                             class_of 37 == 18 /\
                             class_of 38 == 19 /\
                             class_of 39 == 19 /\
                             class_of 40 == 19 /\
                             class_of 41 == 19 /\
                             class_of 42 == 19 /\
                             class_of 43 == 20 /\
                             class_of 44 == 20 /\
                             class_of 45 == 20 /\
                             class_of 46 == 20 /\
                             class_of 47 == 20 /\
                             class_of 48 == 21 /\
                             class_of 49 == 21 /\
                             class_of 50 == 21 /\
                             class_of 51 == 21 /\
                             class_of 52 == 21 /\
                             class_of 53 == 21 /\
                             class_of 54 == 22 /\
                             class_of 55 == 22 /\
                             class_of 56 == 22 /\
                             class_of 57 == 22 /\
                             class_of 58 == 22 /\
                             class_of 59 == 22 /\
                             class_of 60 == 23 /\
                             class_of 61 == 23 /\
                             class_of 62 == 23 /\
                             class_of 63 == 23 /\
                             class_of 64 == 23 /\
                             class_of 65 == 23 /\
                             class_of 66 == 24 /\
                             class_of 67 == 24 /\
                             class_of 68 == 24 /\
                             class_of 69 == 24 /\
                             class_of 70 == 24 /\
                             class_of 71 == 24 /\
                             class_of 72 == 24 /\
                             class_of 73 == 24 /\
                             class_of 74 == 25 /\
                             class_of 75 == 25 /\
                             class_of 76 == 25 /\
                             class_of 77 == 25 /\
                             class_of 78 == 25 /\
                             class_of 79 == 25 /\
                             class_of 80 == 25 /\
                             class_of 81 == 25 /\
                             class_of 82 == 26 /\
                             class_of 83 == 26 /\
                             class_of 84 == 26 /\
                             class_of 85 == 26 /\
                             class_of 86 == 26 /\
                             class_of 87 == 26 /\
                             class_of 88 == 26 /\
                             class_of 89 == 26 /\
                             class_of 90 == 27 /\
                             class_of 91 == 27 /\
                             class_of 92 == 27 /\
                             class_of 93 == 27 /\
                             class_of 94 == 27 /\
                             class_of 95 == 27 /\
                             class_of 96 == 27 /\
                             class_of 97 == 27 /\
                             class_of 98 == 27 /\
                             class_of 99 == 27 /\
                             class_of 100 == 28 /\
                             class_of 101 == 28 /\
                             class_of 102 == 28 /\
                             class_of 103 == 28 /\
                             class_of 104 == 28 /\
                             class_of 105 == 28 /\
                             class_of 106 == 28 /\
                             class_of 107 == 28 /\
                             class_of 108 == 28 /\
                             class_of 109 == 29 /\
                             class_of 110 == 29 /\
                             class_of 111 == 29 /\
                             class_of 112 == 29 /\
                             class_of 113 == 29 /\
                             class_of 114 == 29 /\
                             class_of 115 == 29 /\
                             class_of 116 == 29 /\
                             class_of 117 == 29 /\
                             class_of 118 == 29 /\
                             class_of 119 == 30 /\
                             class_of 120 == 30 /\
                             class_of 121 == 30 /\
                             class_of 122 == 30 /\
                             class_of 123 == 30 /\
                             class_of 124 == 30 /\
                             class_of 125 == 30 /\
                             class_of 126 == 30 /\
                             class_of 127 == 30 /\
                             class_of 128 == 30)
  = assert_norm (class_of 1 == 0);
    assert_norm (class_of 2 == 0);
    assert_norm (class_of 3 == 1);
    assert_norm (class_of 4 == 2);
    assert_norm (class_of 5 == 3);
    assert_norm (class_of 6 == 4);
    assert_norm (class_of 7 == 5);
    assert_norm (class_of 8 == 6);
    assert_norm (class_of 9 == 7);
    assert_norm (class_of 10 == 7);
    assert_norm (class_of 11 == 8);
    assert_norm (class_of 12 == 8);
    assert_norm (class_of 13 == 9);
    assert_norm (class_of 14 == 9);
    assert_norm (class_of 15 == 10);
    assert_norm (class_of 16 == 10);
    assert_norm (class_of 17 == 11);
    assert_norm (class_of 18 == 12);
    assert_norm (class_of 19 == 12);
    assert_norm (class_of 20 == 13);
    assert_norm (class_of 21 == 13);
    assert_norm (class_of 22 == 13);
    assert_norm (class_of 23 == 14);
    assert_norm (class_of 24 == 14);
    assert_norm (class_of 25 == 14);
    assert_norm (class_of 26 == 15);
    assert_norm (class_of 27 == 15);
    assert_norm (class_of 28 == 15);
    assert_norm (class_of 29 == 16);
    assert_norm (class_of 30 == 16);
    assert_norm (class_of 31 == 16);
    assert_norm (class_of 32 == 16);
    assert_norm (class_of 33 == 17);
    assert_norm (class_of 34 == 18);
    assert_norm (class_of 35 == 18);
    assert_norm (class_of 36 == 18);
    assert_norm (class_of 37 == 18);
    assert_norm (class_of 38 == 19);
    assert_norm (class_of 39 == 19);
    assert_norm (class_of 40 == 19);
    assert_norm (class_of 41 == 19);
    assert_norm (class_of 42 == 19);
    assert_norm (class_of 43 == 20);
    assert_norm (class_of 44 == 20);
    assert_norm (class_of 45 == 20);
    assert_norm (class_of 46 == 20);
    assert_norm (class_of 47 == 20);
    assert_norm (class_of 48 == 21);
    assert_norm (class_of 49 == 21);
    assert_norm (class_of 50 == 21);
    assert_norm (class_of 51 == 21);
    assert_norm (class_of 52 == 21);
    assert_norm (class_of 53 == 21);
    assert_norm (class_of 54 == 22);
    assert_norm (class_of 55 == 22);
    assert_norm (class_of 56 == 22);
    assert_norm (class_of 57 == 22);
    assert_norm (class_of 58 == 22);
    assert_norm (class_of 59 == 22);
    assert_norm (class_of 60 == 23);
    assert_norm (class_of 61 == 23);
    assert_norm (class_of 62 == 23);
    assert_norm (class_of 63 == 23);
    assert_norm (class_of 64 == 23);
    assert_norm (class_of 65 == 23);
    assert_norm (class_of 66 == 24);
    assert_norm (class_of 67 == 24);
    assert_norm (class_of 68 == 24);
    assert_norm (class_of 69 == 24);
    assert_norm (class_of 70 == 24);
    assert_norm (class_of 71 == 24);
    assert_norm (class_of 72 == 24);
    assert_norm (class_of 73 == 24);
    assert_norm (class_of 74 == 25);
    assert_norm (class_of 75 == 25);
    assert_norm (class_of 76 == 25);
    assert_norm (class_of 77 == 25);
    assert_norm (class_of 78 == 25);
    assert_norm (class_of 79 == 25);
    assert_norm (class_of 80 == 25);
    assert_norm (class_of 81 == 25);
    assert_norm (class_of 82 == 26);
    assert_norm (class_of 83 == 26);
    assert_norm (class_of 84 == 26);
    assert_norm (class_of 85 == 26);
    assert_norm (class_of 86 == 26);
    assert_norm (class_of 87 == 26);
    assert_norm (class_of 88 == 26);
    assert_norm (class_of 89 == 26);
    assert_norm (class_of 90 == 27);
    assert_norm (class_of 91 == 27);
    assert_norm (class_of 92 == 27);
    assert_norm (class_of 93 == 27);
    assert_norm (class_of 94 == 27);
    assert_norm (class_of 95 == 27);
    assert_norm (class_of 96 == 27);
    assert_norm (class_of 97 == 27);
    assert_norm (class_of 98 == 27);
    assert_norm (class_of 99 == 27);
    assert_norm (class_of 100 == 28);
    assert_norm (class_of 101 == 28);
    assert_norm (class_of 102 == 28);
    assert_norm (class_of 103 == 28);
    assert_norm (class_of 104 == 28);
    assert_norm (class_of 105 == 28);
    assert_norm (class_of 106 == 28);
    assert_norm (class_of 107 == 28);
    assert_norm (class_of 108 == 28);
    assert_norm (class_of 109 == 29);
    assert_norm (class_of 110 == 29);
    assert_norm (class_of 111 == 29);
    assert_norm (class_of 112 == 29);
    assert_norm (class_of 113 == 29);
    assert_norm (class_of 114 == 29);
    assert_norm (class_of 115 == 29);
    assert_norm (class_of 116 == 29);
    assert_norm (class_of 117 == 29);
    assert_norm (class_of 118 == 29);
    assert_norm (class_of 119 == 30);
    assert_norm (class_of 120 == 30);
    assert_norm (class_of 121 == 30);
    assert_norm (class_of 122 == 30);
    assert_norm (class_of 123 == 30);
    assert_norm (class_of 124 == 30);
    assert_norm (class_of 125 == 30);
    assert_norm (class_of 126 == 30);
    assert_norm (class_of 127 == 30);
    assert_norm (class_of 128 == 30)

/// A match on the size, every class a constant: a `switch` in C, made a
/// table, as OCaml 5's `sizeclass_wsize`.
let class_u64 w =
  assert_norm (small_max == 128);
  class_values ();
  match w with
  | 1UL -> 0UL
  | 2UL -> 0UL
  | 3UL -> 1UL
  | 4UL -> 2UL
  | 5UL -> 3UL
  | 6UL -> 4UL
  | 7UL -> 5UL
  | 8UL -> 6UL
  | 9UL -> 7UL
  | 10UL -> 7UL
  | 11UL -> 8UL
  | 12UL -> 8UL
  | 13UL -> 9UL
  | 14UL -> 9UL
  | 15UL -> 10UL
  | 16UL -> 10UL
  | 17UL -> 11UL
  | 18UL -> 12UL
  | 19UL -> 12UL
  | 20UL -> 13UL
  | 21UL -> 13UL
  | 22UL -> 13UL
  | 23UL -> 14UL
  | 24UL -> 14UL
  | 25UL -> 14UL
  | 26UL -> 15UL
  | 27UL -> 15UL
  | 28UL -> 15UL
  | 29UL -> 16UL
  | 30UL -> 16UL
  | 31UL -> 16UL
  | 32UL -> 16UL
  | 33UL -> 17UL
  | 34UL -> 18UL
  | 35UL -> 18UL
  | 36UL -> 18UL
  | 37UL -> 18UL
  | 38UL -> 19UL
  | 39UL -> 19UL
  | 40UL -> 19UL
  | 41UL -> 19UL
  | 42UL -> 19UL
  | 43UL -> 20UL
  | 44UL -> 20UL
  | 45UL -> 20UL
  | 46UL -> 20UL
  | 47UL -> 20UL
  | 48UL -> 21UL
  | 49UL -> 21UL
  | 50UL -> 21UL
  | 51UL -> 21UL
  | 52UL -> 21UL
  | 53UL -> 21UL
  | 54UL -> 22UL
  | 55UL -> 22UL
  | 56UL -> 22UL
  | 57UL -> 22UL
  | 58UL -> 22UL
  | 59UL -> 22UL
  | 60UL -> 23UL
  | 61UL -> 23UL
  | 62UL -> 23UL
  | 63UL -> 23UL
  | 64UL -> 23UL
  | 65UL -> 23UL
  | 66UL -> 24UL
  | 67UL -> 24UL
  | 68UL -> 24UL
  | 69UL -> 24UL
  | 70UL -> 24UL
  | 71UL -> 24UL
  | 72UL -> 24UL
  | 73UL -> 24UL
  | 74UL -> 25UL
  | 75UL -> 25UL
  | 76UL -> 25UL
  | 77UL -> 25UL
  | 78UL -> 25UL
  | 79UL -> 25UL
  | 80UL -> 25UL
  | 81UL -> 25UL
  | 82UL -> 26UL
  | 83UL -> 26UL
  | 84UL -> 26UL
  | 85UL -> 26UL
  | 86UL -> 26UL
  | 87UL -> 26UL
  | 88UL -> 26UL
  | 89UL -> 26UL
  | 90UL -> 27UL
  | 91UL -> 27UL
  | 92UL -> 27UL
  | 93UL -> 27UL
  | 94UL -> 27UL
  | 95UL -> 27UL
  | 96UL -> 27UL
  | 97UL -> 27UL
  | 98UL -> 27UL
  | 99UL -> 27UL
  | 100UL -> 28UL
  | 101UL -> 28UL
  | 102UL -> 28UL
  | 103UL -> 28UL
  | 104UL -> 28UL
  | 105UL -> 28UL
  | 106UL -> 28UL
  | 107UL -> 28UL
  | 108UL -> 28UL
  | 109UL -> 29UL
  | 110UL -> 29UL
  | 111UL -> 29UL
  | 112UL -> 29UL
  | 113UL -> 29UL
  | 114UL -> 29UL
  | 115UL -> 29UL
  | 116UL -> 29UL
  | 117UL -> 29UL
  | 118UL -> 29UL
  | 119UL -> 30UL
  | 120UL -> 30UL
  | 121UL -> 30UL
  | 122UL -> 30UL
  | 123UL -> 30UL
  | 124UL -> 30UL
  | 125UL -> 30UL
  | 126UL -> 30UL
  | 127UL -> 30UL
  | _ -> 30UL
