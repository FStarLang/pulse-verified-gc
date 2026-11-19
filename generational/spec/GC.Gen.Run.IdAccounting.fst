module GC.Gen.Run.IdAccounting

open FStar.List.Tot
open GC.Gen.Run.Step

module I = GC.Model.Ideal

let program_kind_of e = ()

let rec account_hoist a ks ps =
  match ks with
  | [] -> ()
  | KSlice _ :: rest -> account_hoist a rest ps
  | KStart :: rest -> account_hoist (start_acc a) rest ps
  | k :: rest ->
      if is_program_kind k
      then (match ps with
            | [] -> ()
            | pe :: ps' -> account_hoist (kind_step a k (Some pe)) rest ps')
      else account_hoist (kind_step a k None) rest ps

let live_ids_hoist ps ks id = account_hoist empty_acc ks ps

let rec account_snoc a ks ps k pe =
  match ks with
  | [] -> ()
  | k0 :: ks' ->
      if is_program_kind k0
      then (match ps with
            | pe0 :: ps' -> account_snoc (kind_step a k0 (Some pe0)) ks' ps' k pe)
      else account_snoc (kind_step a k0 None) ks' ps k pe

let rec n_program_snoc ks k =
  match ks with
  | [] -> ()
  | _ :: ks' -> n_program_snoc ks' k

let kinds_snoc es e = FStar.List.Tot.Properties.map_append kind_of es [e]

let rt_ok_empty _ = ()

/// A program event keeps every field of every object a field.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let field_value_stable (m: I.ideal_memory) (pe: I.program_event) (x: I.obj_id) (j: nat)
  : Lemma (Some? (field_value m x j) ==> Some? (field_value (I.ideal_step m pe) x j))
  = let m' = I.ideal_step m pe in
    if Some? (field_value m x j) then
      match pe with
      | I.Alloc tag size init ->
          if I.fields_length init = size then
            assert (Seq.index m'.I.objects x == Seq.index m.I.objects x)
      | I.Write obj i v ->
          if x = obj then begin
            let o = Seq.index m.I.objects obj in
            assert (Seq.index m'.I.objects x == I.update_field o i v);
            if i < o.I.size then
              (match o.I.fields, v with
               | I.Scannable vs, _ -> assert (I.field_values (I.update_field o i v) == Seq.upd vs i v)
               | _ -> ())
          end else assert (Seq.index m'.I.objects x == Seq.index m.I.objects x)
      | _ -> ()
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let kind_step_rt_ok a k pe =
  let a' = kind_step a k pe in
  let aux (x: I.obj_id) (j: nat) : Lemma (a'.rt x j ==> Some? (field_value a'.mem x j)) =
    field_value_stable a.mem (match pe with Some pe -> pe | None -> I.Read 0 0) x j;
    match pe with
    | Some (I.Alloc tag size init) ->
        if I.fields_length init = size then begin
          let n = Seq.length a.mem.I.objects in
          let o : I.ideal_object = { I.tag = tag; I.size = size; I.fields = init } in
          assert (Seq.index (I.ideal_step a.mem (I.Alloc tag size init)).I.objects n == o)
        end
    | _ -> ()
  in
  FStar.Classical.forall_intro_2 aux
#pop-options
