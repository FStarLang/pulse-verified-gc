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
