(*
   Copyright 2019 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(* FStarC.Interactive.Lsp needs to construct responses to various *
 * queries; this file collects helpers for them                  *)

module FStarC.Interactive.QueryHelper
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Range
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Interactive.JsonHelper
open FStarC.Interactive.CompletionTable

module U = FStarC.Util
module DsEnv = FStarC.Syntax.DsEnv
module TcErr = FStarC.TypeChecker.Err
module TcEnv = FStarC.TypeChecker.Env
module CTable = FStarC.Interactive.CompletionTable
module Docs = FStarC.Docs
module SyntaxUtil = FStarC.Syntax.Util

let with_printed_effect_args #a (k : unit -> ML a) : ML a =
  Options.with_saved_options
    (fun () -> Options.set_option "print_effect_args" (Options.Bool true); k ())

let term_to_string tcenv t =
  with_printed_effect_args (fun () -> Syntax.Print.term_to_string' (DsEnv.set_current_module tcenv.dsenv tcenv.curmodule) t)

let sigelt_to_string tcenv se =
  with_printed_effect_args (fun () -> Syntax.Print.sigelt_to_string' (DsEnv.set_current_module tcenv.dsenv tcenv.curmodule) se)

let rec find_sigelt (ses:list Syntax.Syntax.sigelt) (lid:Ident.lident)
  : ML (option Syntax.Syntax.sigelt)
  =
  U.find_map ses (fun se ->
    match se.sigel with
    | Syntax.Syntax.Sig_bundle {ses} -> find_sigelt ses lid
    | _ ->
      if SyntaxUtil.lids_of_sigelt se
         |> List.existsb (fun l -> Ident.lid_equals l lid)
      then Some se
      else None)

let interface_sigelt (tcenv:TcEnv.env) (lid:Ident.lident)
  : ML (option Syntax.Syntax.sigelt)
  =
  match U.find_map tcenv.modules (fun m ->
          if m.is_interface then find_sigelt m.declarations lid else None) with
  | Some se -> Some se
  | None ->
    (* At this base an interface checked together with its implementation is
       interleaved into it rather than kept as a module of its own. Its
       declarations are still in the signature context, with ranges in the
       interface file. *)
    U.find_map tcenv.gamma_sig (fun (lids, se) ->
      match se.Syntax.Syntax.sigel with
      | Syntax.Syntax.Sig_declare_typ _
        when List.existsb (Ident.lid_equals lid) lids
          && FStarC.Parser.Dep.is_interface (Range.Ops.file_of_range se.sigrng) ->
        Some se
      | _ -> None)

let docs_of_lid (tcenv:TcEnv.env) (lid:Ident.lident) : ML (option string) =
  let se =
    match interface_sigelt tcenv lid with
    | Some se -> Some se
    | None ->
      (match TcEnv.lookup_qname tcenv lid with
       | Some (Inr (se, _), _) -> Some se
       | _ -> None)
  in
  match se with
  | Some se -> (
    match Docs.doc_of_sigelt se with
    (* The protocol's [documentation] field is a single string, so the
       lines are joined here, at the edge, rather than anywhere the
       compiler stores them. *)
    | Docs.Doc_text lines -> Some (String.concat "\n" lines)
    (* See the interface: an unusable payload is reported as "no
       documentation" rather than as an error, since the request has
       nowhere to say more. *)
    | Docs.Doc_absent
    | Docs.Doc_unsupported _ -> None
  )
  | _ -> None

let symlookup tcenv symbol pos_opt requested_info =
  let info_of_lid_str lid_str =
    let lid = Ident.lid_of_ids (List.map Ident.id_of_text (U.split lid_str ".")) in
    let lid = Option.dflt lid <| DsEnv.resolve_to_fully_qualified_name tcenv.dsenv lid in
    try_lookup_lid tcenv lid |> Option.map (fun ((_, typ), r) -> (Inr lid, typ, r)) in

  let docs_of_lid lid = docs_of_lid tcenv lid in

  let def_of_lid lid =
    Option.bind (TcEnv.lookup_qname tcenv lid) (function
      | (Inr (se, _), _) -> Some (sigelt_to_string tcenv se)
      | _ -> None) in

  let info_at_pos_opt =
    Option.bind pos_opt (fun (file, row, col) ->
      TcErr.info_at_pos tcenv file row col) in

  let info_opt =
    match info_at_pos_opt with
    | Some _ -> info_at_pos_opt
    | None -> if symbol = "" then None else info_of_lid_str symbol in

    match info_opt with
    | None -> None
    | Some (name_or_lid, typ, rng) ->
      let name =
        match name_or_lid with
        | Inl name -> name
        | Inr lid -> Ident.string_of_lid lid in
      let str_of_opt = function
        | None -> "<none>"
        | Some s -> s in
      let typ_str =
        if List.mem "type" requested_info then
          Some (term_to_string tcenv typ)
        else None in
      let doc_str =
        match name_or_lid with
        | Inr lid when List.mem "documentation" requested_info -> docs_of_lid lid
        | _ -> None in
      let def_str =
        match name_or_lid with
        | Inr lid when List.mem "definition" requested_info -> def_of_lid lid
        | _ -> None in
      let def_range =
        if List.mem "defined-at" requested_info then Some rng else None in
      Some ({ slr_name = name; slr_def_range = def_range;
             slr_typ = typ_str; slr_doc = doc_str; slr_def = def_str })

let mod_filter = function
  | _, CTable.Namespace _
  | _, CTable.Module { CTable.mod_loaded = true } -> None
  | pth, CTable.Module md ->
    Some (pth, CTable.Module ({ md with CTable.mod_name = CTable.mod_name md ^ "." }))

let ck_completion (st: repl_state) (search_term: string) : ML (list CTable.completion_result) =
  let needle = U.split search_term "." in
  let mods_and_nss = CTable.autocomplete_mod_or_ns st.repl_names needle mod_filter in
  let lids = CTable.autocomplete_lid st.repl_names needle in
  lids @ mods_and_nss