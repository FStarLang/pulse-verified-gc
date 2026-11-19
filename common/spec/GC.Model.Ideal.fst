/// ---------------------------------------------------------------------------
/// GC.Model.Ideal - the program's memory with no garbage collector
/// ---------------------------------------------------------------------------
///
/// The ideal execution of an OCaml program: unlimited memory, no collector,
/// every object ever allocated stays where it was put.  It is what the
/// mutator-equivalence theorem (`GC.Gen.Run.Simulation`) compares the real
/// execution against (mutator-equivalence-plan.md, section 3.4).
///
///   * **Values** (`value`): a machine word that is not a pointer to an
///     object (`Word`: an OCaml int, a pointer to static data or code; that
///     such a word lies outside the real heaps is the real side's business,
///     `GC.Model.Represents.value_rep`), or a
///     pointer to an object (`Ptr { head; infix_offset }`; the offset, in
///     words, is 0 except for a pointer into a closure at an infix header).
///   * **Objects** (`ideal_object`): a tag, a size, and fields -- values for
///     a scannable object, raw words for a no-scan one (strings, floats).
///   * **Memory** (`ideal_memory`): the sequence of every object allocated
///     (object `id` is the `id`-th one allocated: fresh by construction, never
///     reused) and the program's roots.
///   * **Program events** (`program_event`): `Alloc` (with every initialising
///     write), `Write`, `Read`, `SetRoots`, and their effect, a function
///     (`ideal_step`).  The allocation's result is held by the program: it is
///     appended to the roots (until the program drops it with `SetRoots`).
///   * **Well-formedness** (`wf_event`, `wf_program`): OCaml's type safety,
///     stated once -- every event mentions only objects the program can reach,
///     valid field indices, and values only into scannable fields.

module GC.Model.Ideal

open FStar.Seq
open FStar.List.Tot

module U64 = FStar.UInt64
module O = GC.Spec.Object

/// ---------------------------------------------------------------------------
/// Values, objects, memory
/// ---------------------------------------------------------------------------

/// An object's identity: the number of objects allocated before it.
type obj_id = nat

/// A header tag.
let tag_t = t: U64.t{U64.v t < 256}

/// A value of the program: a word that is not a pointer to an object, or a
/// pointer to object `head`, `infix_offset` words into it.  (The ideal
/// memory has no heaps; where a word may lie in the real memory is stated
/// on the real side, `GC.Model.Represents.value_rep`.)
type value =
  | Word : w: U64.t -> value
  | Ptr { head: obj_id; infix_offset: nat }

/// The fields of an object: values (scannable), or raw words (no-scan).
noeq type ideal_fields =
  | Scannable : seq value -> ideal_fields
  | NoScan : seq U64.t -> ideal_fields

let fields_length (f: ideal_fields) : nat =
  match f with
  | Scannable vs -> Seq.length vs
  | NoScan ws -> Seq.length ws

/// An object: its tag, its size in words, and its fields.
noeq type ideal_object = {
  tag: tag_t;
  size: nat;
  fields: f: ideal_fields{fields_length f == size};
}

/// The memory: every object allocated so far, and the roots.
noeq type ideal_memory = {
  objects: seq ideal_object;
  roots: seq value;
}

/// Nothing allocated, no roots.
let empty_ideal : ideal_memory = { objects = Seq.empty; roots = Seq.empty }

/// `id` is an object of `m`.
let valid_id (m: ideal_memory) (id: obj_id) : bool = id < Seq.length m.objects

/// Scannable exactly when the tag is below `No_scan_tag`.
let tag_scannable (tag: tag_t) : bool = U64.v tag < U64.v O.no_scan_tag

/// The values in the fields of `o` (none for a no-scan object).
let field_values (o: ideal_object) : seq value =
  match o.fields with
  | Scannable vs -> vs
  | NoScan _ -> Seq.empty

/// The `i`-th field of `o`, as stored: a value, or a raw word.
noeq type field_content =
  | FValue : value -> field_content
  | FRaw : U64.t -> field_content

let field_at (o: ideal_object) (i: nat{i < o.size}) : field_content =
  match o.fields with
  | Scannable vs -> FValue (Seq.index vs i)
  | NoScan ws -> FRaw (Seq.index ws i)

/// The object pointed at by a value, if any.
let target (v: value) : option obj_id =
  match v with
  | Word _ -> None
  | Ptr { head } -> Some head

/// A value is valid in `m`: a pointer names an object of `m`, and a pointer
/// with an infix offset `k > 0` points into a closure whose field `k - 1` is
/// an infix header (OCaml's mutually recursive closures) whose size is `k`:
/// the header gives the offset back to the closure (`Infix_offset_hd`), which
/// is how the real heap resolves the pointer.  The offset is at least 2: a
/// closure's first field is its code pointer, so OCaml never builds offset 1
/// (and the real heap's `infix_addr_conds` asks for it).
let valid_value (m: ideal_memory) (v: value) : prop =
  match v with
  | Word _ -> True
  | Ptr { head; infix_offset } ->
      valid_id m head /\
      (infix_offset > 0 ==>
        (let o = Seq.index m.objects head in
         o.tag == O.closure_tag /\ 2 <= infix_offset /\ infix_offset < o.size /\
         (match field_at o (infix_offset - 1) with
          | FValue (Word w) -> O.getTag w == O.infix_tag /\ U64.v (O.getWosize w) == infix_offset
          | _ -> False)))

/// Well-formed memory: every value in a field or a root is valid.
let wf_memory (m: ideal_memory) : prop =
  (forall (i: nat). i < Seq.length m.roots ==> valid_value m (Seq.index m.roots i)) /\
  (forall (id: obj_id) (i: nat).
     valid_id m id /\ i < Seq.length (field_values (Seq.index m.objects id)) ==>
     valid_value m (Seq.index (field_values (Seq.index m.objects id)) i))

/// ---------------------------------------------------------------------------
/// Reachability
/// ---------------------------------------------------------------------------

/// An edge: a field of `src` points at `dst`.
let points_to (m: ideal_memory) (src dst: obj_id) : prop =
  valid_id m src /\
  (let vs = field_values (Seq.index m.objects src) in
   exists (i: nat). i < Seq.length vs /\ target (Seq.index vs i) == Some dst)

/// A root names `id`.
let root_names (m: ideal_memory) (id: obj_id) : prop =
  exists (i: nat). i < Seq.length m.roots /\ target (Seq.index m.roots i) == Some id

/// `id` is reachable from the roots in at most `n` edges.
let rec reach_within (m: ideal_memory) (n: nat) (id: obj_id) : Tot prop (decreases n) =
  if n = 0 then root_names m id
  else reach_within m (n - 1) id \/
       (exists (src: obj_id). reach_within m (n - 1) src /\ points_to m src id)

/// **Reachable**: from a root, along fields.
let reachable (m: ideal_memory) (id: obj_id) : prop =
  exists (n: nat). reach_within m n id

/// A value the program may use: a word, or a pointer to a reachable object.
let usable (m: ideal_memory) (v: value) : prop =
  valid_value m v /\ (match target v with None -> True | Some id -> reachable m id)

/// ---------------------------------------------------------------------------
/// Program events
/// ---------------------------------------------------------------------------

/// What the program does.  `Alloc tag size init`: a new object, with every
/// initialising write; `Write obj i v`: store `v` in field `i` of `obj`
/// (a raw word, for a no-scan object, is `Word`'s word); `Read obj i`;
/// `SetRoots rs`: the program's roots are now `rs` (registers, stack, and
/// the static slots that hold heap values).
noeq type program_event =
  | Alloc : tag: tag_t -> size: nat -> init: ideal_fields -> program_event
  | Write : obj: obj_id -> field: nat -> v: value -> program_event
  | Read : obj: obj_id -> field: nat -> program_event
  | SetRoots : roots: seq value -> program_event

/// Replace field `i` of `o`.  A no-scan field takes the word of a `Word`.
let update_field (o: ideal_object) (i: nat) (v: value) : ideal_object =
  if i >= o.size then o
  else match o.fields, v with
       | Scannable vs, _ -> { o with fields = Scannable (Seq.upd vs i v) }
       | NoScan ws, Word w -> { o with fields = NoScan (Seq.upd ws i w) }
       | NoScan _, Ptr _ -> o

/// **The effect of a program event.**  `Alloc` appends the object (its id is
/// the old length) and the pointer to it to the roots: the program holds the
/// result.  An ill-formed event (`wf_event`) changes what it may.
let ideal_step (m: ideal_memory) (e: program_event) : ideal_memory =
  match e with
  | Alloc tag size init ->
      if fields_length init = size
      then { objects = Seq.snoc m.objects ({ tag; size; fields = init });
             roots = Seq.snoc m.roots (Ptr { head = Seq.length m.objects; infix_offset = 0 }) }
      else m
  | Write obj i v ->
      if valid_id m obj
      then { m with objects = Seq.upd m.objects obj (update_field (Seq.index m.objects obj) i v) }
      else m
  | Read _ _ -> m
  | SetRoots rs -> { m with roots = rs }

/// The memory after a list of program events.
let rec ideal_run_from (m: ideal_memory) (ps: list program_event) : Tot ideal_memory (decreases ps) =
  match ps with
  | [] -> m
  | e :: rest -> ideal_run_from (ideal_step m e) rest

let ideal_run (ps: list program_event) : ideal_memory = ideal_run_from empty_ideal ps

/// ---------------------------------------------------------------------------
/// Program well-formedness
/// ---------------------------------------------------------------------------

/// The initial fields of an object: all usable values (scannable), or any
/// words (no-scan).
let init_usable (m: ideal_memory) (f: ideal_fields) : prop =
  match f with
  | Scannable vs -> forall (i: nat). i < Seq.length vs ==> usable m (Seq.index vs i)
  | NoScan _ -> True

/// **A well-formed event** in `m`.
///   * `Alloc`: at least one field, a block tag (not `Infix_tag`, which only
///     appears inside closures), scannable exactly by the tag, the fields
///     matching the size, initial values the program can reach;
///   * `Write`: a reachable object that is not a closure (whose body holds
///     the infix headers), a field index in range, and a usable value -- a
///     word, for a no-scan object;
///   * `Read`: a reachable object, a field index in range;
///   * `SetRoots`: values the program can reach.
let wf_event (m: ideal_memory) (e: program_event) : prop =
  match e with
  | Alloc tag size init ->
      size >= 1 /\ size < pow2 54 /\ tag <> O.infix_tag /\
      fields_length init == size /\
      (Scannable? init <==> tag_scannable tag) /\
      init_usable m init
  | Write obj i v ->
      valid_id m obj /\ reachable m obj /\
      (let o = Seq.index m.objects obj in
       o.tag <> O.closure_tag /\ i < o.size /\ usable m v /\
       (NoScan? o.fields ==> Word? v))
  | Read obj i ->
      valid_id m obj /\ reachable m obj /\ i < (Seq.index m.objects obj).size
  | SetRoots rs ->
      forall (i: nat). i < Seq.length rs ==> usable m (Seq.index rs i)

/// **A well-formed program** from `m`: every event well formed where it
/// occurs.
let rec wf_program_from (m: ideal_memory) (ps: list program_event) : Tot prop (decreases ps) =
  match ps with
  | [] -> True
  | e :: rest -> wf_event m e /\ wf_program_from (ideal_step m e) rest

let wf_program (ps: list program_event) : prop = wf_program_from empty_ideal ps

/// Every object of a well-formed memory is well formed: scannable exactly by
/// its tag, at least one field, not an infix block.
let wf_objects (m: ideal_memory) : prop =
  forall (id: obj_id). valid_id m id ==>
    (let o = Seq.index m.objects id in
     o.size >= 1 /\ o.size < pow2 54 /\ o.tag <> O.infix_tag /\
     (Scannable? o.fields <==> tag_scannable o.tag))

/// ---------------------------------------------------------------------------
/// Facts
/// ---------------------------------------------------------------------------

/// The empty memory is well formed.
let empty_wf (_: unit) : Lemma (wf_memory empty_ideal /\ wf_objects empty_ideal) = ()

/// **A well-formed event keeps the memory well formed.**
/// Objects only ever grow at the end and keep their indices: a value valid
/// in `m` stays valid when the objects it can name keep their tag, size and
/// fields.
let valid_value_mono (m m': ideal_memory) (v: value)
  : Lemma (requires valid_value m v /\ Seq.length m.objects <= Seq.length m'.objects /\
                    (match v with
                     | Ptr { head } -> Seq.index m'.objects head == Seq.index m.objects head
                     | Word _ -> True))
          (ensures valid_value m' v)
  = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let ideal_alloc_wf (m: ideal_memory) (tag: tag_t) (size: nat) (init: ideal_fields)
  : Lemma (requires wf_memory m /\ wf_objects m /\ wf_event m (Alloc tag size init))
          (ensures wf_memory (ideal_step m (Alloc tag size init)) /\
                   wf_objects (ideal_step m (Alloc tag size init)))
  = let m' = ideal_step m (Alloc tag size init) in
    let n = Seq.length m.objects in
    let o = { tag; size; fields = init } in
    assert (m'.objects == Seq.snoc m.objects o);
    let old (id: obj_id) : Lemma (requires id < n) (ensures Seq.index m'.objects id == Seq.index m.objects id)
      = () in
    let mono (v: value) : Lemma (requires valid_value m v) (ensures valid_value m' v)
      = match v with
        | Word _ -> ()
        | Ptr { head } -> old head; valid_value_mono m m' v
    in
    let root (i: nat) : Lemma (i < Seq.length m'.roots ==> valid_value m' (Seq.index m'.roots i))
      = if i >= Seq.length m'.roots then () else if i < Seq.length m.roots then mono (Seq.index m.roots i)
        else assert (Seq.index m'.objects n == o)
    in
    let field (id: obj_id) (i: nat)
      : Lemma (valid_id m' id /\ i < Seq.length (field_values (Seq.index m'.objects id)) ==>
               valid_value m' (Seq.index (field_values (Seq.index m'.objects id)) i))
      = if not (valid_id m' id && i < Seq.length (field_values (Seq.index m'.objects id))) then ()
        else if id < n then begin old id; mono (Seq.index (field_values (Seq.index m.objects id)) i) end
        else begin
          assert (Seq.index m'.objects id == o);
          match init with
          | Scannable vs -> assert (usable m (Seq.index vs i)); mono (Seq.index vs i)
          | NoScan _ -> ()
        end
    in
    let obj (id: obj_id) : Lemma (valid_id m' id ==>
          (let o = Seq.index m'.objects id in
           o.size >= 1 /\ o.size < pow2 54 /\ o.tag <> O.infix_tag /\
           (Scannable? o.fields <==> tag_scannable o.tag)))
      = if id < n then old id else ()
    in
    FStar.Classical.forall_intro root;
    FStar.Classical.forall_intro_2 field;
    FStar.Classical.forall_intro obj

let ideal_write_wf (m: ideal_memory) (obj: obj_id) (j: nat) (v: value)
  : Lemma (requires wf_memory m /\ wf_objects m /\ wf_event m (Write obj j v))
          (ensures wf_memory (ideal_step m (Write obj j v)) /\
                   wf_objects (ideal_step m (Write obj j v)))
  = let m' = ideal_step m (Write obj j v) in
    let o = Seq.index m.objects obj in
    let o' = update_field o j v in
    assert (m'.objects == Seq.upd m.objects obj o');
    assert (o'.tag == o.tag /\ o'.size == o.size /\ (Scannable? o'.fields <==> Scannable? o.fields));
    // `obj` is not a closure, so no infix pointer resolves through it
    let mono (w: value) : Lemma (requires valid_value m w) (ensures valid_value m' w)
      = match w with
        | Word _ -> ()
        | Ptr { head; infix_offset } ->
            if head = obj then begin
              if infix_offset > 0 then assert False
            end else valid_value_mono m m' w
    in
    let root (i: nat) : Lemma (i < Seq.length m'.roots ==> valid_value m' (Seq.index m'.roots i))
      = if i < Seq.length m'.roots then mono (Seq.index m.roots i)
    in
    let field (id: obj_id) (i: nat)
      : Lemma (valid_id m' id /\ i < Seq.length (field_values (Seq.index m'.objects id)) ==>
               valid_value m' (Seq.index (field_values (Seq.index m'.objects id)) i))
      = if not (valid_id m' id && i < Seq.length (field_values (Seq.index m'.objects id))) then ()
        else if id <> obj then mono (Seq.index (field_values (Seq.index m.objects id)) i)
        else match o.fields with
             | Scannable vs ->
                 if i = j then mono v
                 else begin
                   assert (Seq.index (field_values o') i == Seq.index vs i);
                   mono (Seq.index vs i)
                 end
             | NoScan _ -> ()
    in
    FStar.Classical.forall_intro root;
    FStar.Classical.forall_intro_2 field
#pop-options

let ideal_step_wf (m: ideal_memory) (e: program_event)
  : Lemma (requires wf_memory m /\ wf_objects m /\ wf_event m e)
          (ensures wf_memory (ideal_step m e) /\ wf_objects (ideal_step m e))
  = match e with
    | Alloc tag size init -> ideal_alloc_wf m tag size init
    | Write obj j v -> ideal_write_wf m obj j v
    | Read _ _ -> ()
    | SetRoots rs -> ()

#push-options "--fuel 2 --ifuel 1"
let rec ideal_run_from_snoc (m: ideal_memory) (ps: list program_event) (e: program_event)
  : Lemma (ensures ideal_run_from m (ps @ [e]) == ideal_step (ideal_run_from m ps) e /\
                   (wf_program_from m (ps @ [e]) <==> wf_program_from m ps /\ wf_event (ideal_run_from m ps) e))
          (decreases ps)
  = match ps with
    | [] -> ()
    | e0 :: rest -> ideal_run_from_snoc (ideal_step m e0) rest e
#pop-options

/// Snoc decomposition of a run of the program (the runs of
/// `GC.Gen.Run.Step` grow at the end).
let ideal_run_snoc (ps: list program_event) (e: program_event)
  : Lemma (ideal_run (ps @ [e]) == ideal_step (ideal_run ps) e /\
           (wf_program (ps @ [e]) <==> wf_program ps /\ wf_event (ideal_run ps) e))
  = ideal_run_from_snoc empty_ideal ps e
