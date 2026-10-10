(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Reflection.V2.Derived

open FStar.Stubs.Reflection.Types
open FStar.Reflection.Const
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data
open FStar.Order
open FStar.VConfig
open FStar.Reflection.V2.Collect

(*| Returns the sort (type annotation) of a binder. *)
let type_of_binder (b : binder) : typ =
    (inspect_binder b).sort

(*| Inspects a term with `FStar.Stubs.Reflection.V2.Builtins.inspect_ln`,
    looking through any number of ascriptions.

    The returned view is never `Tv_AscribedT` or `Tv_AscribedC` and precedes
    the term. An identical copy of
    `FStar.Reflection.V2.Collect.inspect_ln_unascribe`. *)
let rec inspect_ln_unascribe (t:term) : tv:term_view{tv << t /\ notAscription tv} =
    match inspect_ln t with
    | Tv_AscribedT t' _ _ _
    | Tv_AscribedC t' _ _ _ -> inspect_ln_unascribe t'
    | tv -> tv

(*| Compares two bound variables by de Bruijn index. *)
let compare_bv (v1 v2 : bv) : order =
  Order.compare_int (inspect_bv v1).index (inspect_bv v2).index

(*| Compares two named variables by their unique numbers, ignoring their
    pretty-printing names. *)
let compare_namedv (v1 v2 : namedv) : order =
  Order.compare_int (inspect_namedv v1).uniq (inspect_namedv v2).uniq

(*| Shifts the de Bruijn index of a substitution element by `n`, for use under
    `n` additional binders.

    Every `FStar.Stubs.Syntax.Syntax.subst_elt` constructor carrying an index
    has it increased by `n`; `NT` elements are unchanged. *)
let shift n s = match s with
    | DB i t -> DB (i+n) t
    | DT i t -> DT (i+n) t
    | UN i t -> UN (i+n) t
    | NM x i -> NM x (i+n)
    | UD x i -> UD x (i+n)
    | NT _ _ -> s
(*| Shifts every element of a substitution by `n` with
    `FStar.Reflection.V2.Derived.shift`. *)
let shift_subst n s = List.Tot.map (shift n) s

(*| Substitutes `t1` for the named variable `n` in `t2`.

    Uses `FStar.Stubs.Reflection.V2.Builtins.subst_term` with the single
    element `NT n t1`. *)
let subst1 (n:namedv) (t1:term) (t2:term) : term =
  subst_term [NT n t1] t2

(*
 * AR: add versions that take attributes as arguments?
 *)
(*| Builds an explicit binder with pretty-printing name `nm`, sort `sort` and
    no attributes.

    The result is a locally nameless `FStar.Stubs.Reflection.Types.binder`,
    proved to be a `simple_binder`. For an implicit binder use
    `FStar.Reflection.V2.Derived.mk_implicit_binder`. *)
let mk_binder (nm : string) (sort : typ) : simple_binder =
  let bv : binder_view = {
    ppname = seal nm;
    qual   = Q_Explicit;
    attrs  = [];
    sort   = sort;
  }
  in
  inspect_pack_binder bv;
  pack_binder bv

(*| Builds an implicit binder with pretty-printing name `nm`, sort `sort` and
    no attributes. *)
let mk_implicit_binder (nm : string) (sort : typ) : binder =
  pack_binder {
    ppname = seal nm;
    qual   = Q_Implicit;
    attrs  = [];
    sort   = sort;
  }

(*| Extends a typing environment with the variable of a binding.

    The variable keeps the unique number, sort and pretty-printing name of the
    binding. See `FStar.Stubs.Reflection.V2.Builtins.push_namedv`. *)
let push_binding (e:env) (b:binding) : env =
  let nv : namedv = pack_namedv {
    uniq = b.uniq;
    sort = seal b.sort;
    ppname = b.ppname;
  }
  in
  push_namedv e nv

(*| Joins the components of a qualified name with dots, as in
    `["FStar"; "List"; "map"]` to `"FStar.List.map"`.

    The empty name gives the empty string. Equivalent to
    `FStar.Stubs.Reflection.V2.Builtins.implode_qn`. *)
val flatten_name : name -> Tot string
let rec flatten_name ns =
    match ns with
    | [] -> ""
    | [n] -> n
    | n::ns -> n ^ "." ^ flatten_name ns

(*| Applies a term to a list of arguments, with their qualifiers.

    `mk_app t [a1; ...; an]` builds one `Tv_App` node per argument, so the
    result is `t a1 ... an`; with no arguments it is `t` itself. The inverse of
    `FStar.Reflection.V2.Collect.collect_app_ln`. For only explicit arguments
    see `FStar.Reflection.V2.Derived.mk_e_app`. *)
let rec mk_app (t : term) (args : list argv) : Tot term (decreases args) =
    match args with
    | [] -> t
    | (x::xs) -> mk_app (pack_ln (Tv_App t x)) xs

// Helper for when all arguments are explicit
(*| Applies a term to a list of explicit arguments.

    The result is unelaborated syntax: implicit arguments such as types are not
    inserted. Here the result is compared with a quoted term.

    ```fstar
    let sum12 : term = mk_e_app (pack (Tv_FVar (pack_fv add_qn))) [`1; `2]

    let _ = assert True by (
      guard (compare_term sum12 (`(1 + 2)) = FStar.Order.Eq))
    ``` *)
let mk_e_app (t : term) (args : list term) : Tot term =
    let e t = (t, Q_Explicit) in
    mk_app t (List.Tot.Base.map e args)

(*| The unknown universe, `Uv_Unk`, to be inferred by the typechecker. *)
let u_unk : universe = pack_universe Uv_Unk

(*| Builds the curried arrow type `b1 -> ... -> bn -> Tot cod`, or `cod` when
    there are no binders.

    Every arrow has a `Tot` computation type. The binders are used as given, in
    the locally nameless representation, so `cod` and later sorts must refer to
    earlier binders by de Bruijn index. See
    `FStar.Tactics.V2.SyntaxHelpers.mk_tot_arr` for the named-view counterpart. *)
let rec mk_tot_arr_ln (bs: list binder) (cod : term) : Tot term (decreases bs) =
    match bs with
    | [] -> cod
    | (b::bs) -> pack_ln (Tv_Arrow b (pack_comp (mk_tot_comp (mk_tot_arr_ln bs cod))))

(*| Builds the curried arrow type `b1 -> ... -> bn -> cod` ending in the
    computation type `cod`, for a non-empty list of binders.

    Intermediate arrows have `Tot` computation types. As for
    `FStar.Reflection.V2.Derived.mk_tot_arr_ln`, the binders are used as given,
    in the locally nameless representation. *)
let rec mk_arr_ln (bs: list binder{~(Nil? bs)}) (cod : comp) : Tot term (decreases bs) =
    match bs with
    | [b] -> pack_ln (Tv_Arrow b cod)
    | (b::bs) -> pack_ln (Tv_Arrow b (pack_comp (mk_tot_comp (mk_arr_ln bs cod))))

(*| Returns the fully qualified, dot-separated name of a top-level name. *)
let fv_to_string (fv:fv) : string = implode_qn (inspect_fv fv)

(*| Builds a string literal term. *)
let mk_stringlit (s : string) : term =
    pack_ln (Tv_Const (C_String s))

(*| Builds the term `Prims.strcat t1 t2`, concatenating two string terms. *)
let mk_strcat (t1 t2 : term) : term =
    mk_e_app (pack_ln (Tv_FVar (pack_fv ["Prims"; "strcat"]))) [t1; t2]

(*| Builds the term `Cons h t`, without the implicit type argument.

    The type argument is left for elaboration; see
    `FStar.Reflection.V2.Derived.mk_cons_t` to supply it. *)
let mk_cons (h t : term) : term =
   mk_e_app (pack_ln (Tv_FVar (pack_fv cons_qn))) [h; t]

(*| Builds the term `Cons #ty h t`, with the element type given as the implicit
    argument. *)
let mk_cons_t (ty h t : term) : term =
   mk_app (pack_ln (Tv_FVar (pack_fv cons_qn))) [(ty, Q_Implicit); (h, Q_Explicit); (t, Q_Explicit)]

(*| Builds the list term `[t1; ...; tn]` from a list of terms, with
    `FStar.Reflection.V2.Derived.mk_cons` and `Nil`.

    Type arguments are not supplied and are left for elaboration. *)
let rec mk_list (ts : list term) : term =
    match ts with
    | [] -> pack_ln (Tv_FVar (pack_fv nil_qn))
    | t::ts -> mk_cons t (mk_list ts)

(*| Builds a tuple term from at most eight components.

    No components give `()`, one component gives the component itself, and two
    to eight components give the application of
    `FStar.Pervasives.Native.Mktuple2` to `Mktuple8` to the components, without
    type arguments. See `FStar.Reflection.V2.Derived.destruct_tuple` for the
    inverse. *)
let mktuple_n (ts : list term{List.Tot.Base.length ts <= 8}) : term =
    match List.Tot.Base.length ts with
    | 0 -> pack_ln (Tv_Const C_Unit)
    | 1 -> let [x] = ts in x
    | n -> begin
           let qn = match n with
                    | 2 -> mktuple2_qn
                    | 3 -> mktuple3_qn
                    | 4 -> mktuple4_qn
                    | 5 -> mktuple5_qn
                    | 6 -> mktuple6_qn
                    | 7 -> mktuple7_qn
                    | 8 -> mktuple8_qn
           in mk_e_app (pack_ln (Tv_FVar (pack_fv qn))) ts
           end

(*| Returns the components of a tuple term, or `None` if the term is not a
    tuple.

    The term must be an application of one of the constructors
    `FStar.Pervasives.Native.Mktuple2` to `Mktuple8`, as a plain top-level
    name; its explicit arguments are returned and the implicit type arguments
    dropped. *)
let destruct_tuple (t : term) : option (list term) =
    let head, args = collect_app_ln t in
    match inspect_ln head with
    | Tv_FVar fv ->
        if List.Tot.Base.mem
                (inspect_fv fv) [mktuple2_qn; mktuple3_qn; mktuple4_qn; mktuple5_qn;
                                 mktuple6_qn; mktuple7_qn; mktuple8_qn]
        then Some (List.Tot.Base.concatMap (fun (t, q) ->
                                      match q with
                                      | Q_Explicit -> [t]
                                      | _ -> []) args)
        else None
    | _ -> None

(*| Builds the pair term `(t1, t2)`; see
    `FStar.Reflection.V2.Derived.mktuple_n`. *)
let mkpair (t1 t2 : term) : term =
    mktuple_n [t1;t2]

(*| Returns the innermost head of a term.

    It descends repeatedly into the function of an application, the body of an
    ascription, the scrutinee of a match, the definition of a `let`, the body of
    an abstraction and the formula of a refinement. Any other term is its own
    head. Used by `FStar.Reflection.V2.Derived.is_uvar`. *)
let rec head (t : term) : term =
    match inspect_ln t with
    | Tv_Match t _ _
    | Tv_Let _ _ _ t _
    | Tv_Abs _ t
    | Tv_Refine _ t
    | Tv_App t _
    | Tv_AscribedT t _ _ _
    | Tv_AscribedC t _ _ _ -> head t

    | Tv_Unknown
    | Tv_Uvar _ _
    | Tv_Const _
    | Tv_Type _
    | Tv_Var _
    | Tv_BVar _
    | Tv_FVar _
    | Tv_UInst _ _
    | Tv_Arrow _ _
    | Tv_Unsupp -> t

(*| Tests whether a term is the top-level name `nm`, given as a dot-separated
    string.

    Ascriptions and universe instantiations are ignored; an application of the
    name does not count. See `FStar.Reflection.V2.Derived.is_name_imp` for a
    variant that allows implicit arguments. *)
let is_fvar (t : term) (nm:string) : bool =
    match inspect_ln_unascribe t with
    | Tv_FVar fv
    | Tv_UInst fv _ -> implode_qn (inspect_fv fv) = nm
    | _ -> false

(*| Tests whether a term is one of the top-level names in `nms`, with
    `FStar.Reflection.V2.Derived.is_fvar`. *)
let rec is_any_fvar (t : term) (nms:list string) : bool =
    match nms with
    | [] -> false
    | v::vs -> is_fvar t v || is_any_fvar t vs

(*| Tests whether the head of a term, as computed by
    `FStar.Reflection.V2.Derived.head`, is a unification variable.

    The term is not compressed first, so a unification variable that has
    already been solved may still be reported. *)
let is_uvar (t : term) : bool =
    match inspect_ln (head t) with
    | Tv_Uvar _ _ -> true
    | _ -> false

(*| Returns the binder with its qualifier replaced by `q`. *)
let binder_set_qual (q:aqualv) (b:binder) : Tot binder =
  let bview = inspect_binder b in
  pack_binder { bview with qual=q }

(*| Adds the attribute `FStar.VConfig.check_with vcfg` to a top-level
    declaration, so that it is checked with the verification options `vcfg`.

    The attribute is prepended to the existing attributes of the sigelt. *)
val add_check_with : vconfig -> sigelt -> Tot sigelt
let add_check_with vcfg se =
  let attrs = sigelt_attrs se in
  let vcfg_t = embed_vconfig vcfg in
  let t = `(check_with (`#vcfg_t)) in
  set_sigelt_attrs (t :: attrs) se


(*| Drops the universe instantiation from a universe-instantiated top-level
    name, turning `Tv_UInst fv us` into `Tv_FVar fv`; any other term is
    returned unchanged. *)
let un_uinst (t:term) : term =
  match inspect_ln t with
  | Tv_UInst fv _ -> pack_ln (Tv_FVar fv)
  | _ -> t

(*| Tests whether a term is the top-level name `nm`, possibly with universes and
    applied only to implicit arguments.

    Ascriptions are ignored. `FStar.Reflection.V2.Derived.unsquash_term` uses it
    to recognize `squash`. *)
let rec is_name_imp (nm : name) (t : term) : bool =
    begin match inspect_ln_unascribe t with
    | Tv_FVar fv
    | Tv_UInst fv _ ->
        if inspect_fv fv = nm
        then true
        else false
    | Tv_App l (_, Q_Implicit) ->
        is_name_imp nm l
    | _ -> false
    end

(*| Returns `Some t'` when the term is `squash t'`, and `None` otherwise.

    The head may carry universes and implicit arguments (see
    `FStar.Reflection.V2.Derived.is_name_imp`), and ascriptions are ignored. *)
let unsquash_term (t : term) : option term =
    match inspect_ln_unascribe t with
    | Tv_App l (r, Q_Explicit) ->
        if is_name_imp squash_qn l
        then Some r
        else None
    | _ -> None

(*| Strips one `squash` from a term if present, with
    `FStar.Reflection.V2.Derived.unsquash_term`, and returns the term unchanged
    otherwise. *)
let maybe_unsquash_term (t : term) : term =
    match unsquash_term t with
    | Some t' -> t'
    | None -> t
