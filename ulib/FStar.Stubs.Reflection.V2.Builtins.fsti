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
module FStar.Stubs.Reflection.V2.Builtins

open FStar.Order
open FStar.Stubs.Syntax.Syntax
open FStar.VConfig
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data

(*** Views ***)

(* NOTE: You probably want inspect/pack from FStar.Tactics, which work
 * over a fully named representation. If you use these, you have to
 * work with de Bruijn indices (using Tv_BVar). The only reason these
 * two exists is that they can be made Tot, and hence can be used in
 * specifications. *)

(* Views *)
(*| Reveals the top-level syntax of a term as a `FStar.Stubs.Reflection.V2.Data.term_view`, using de Bruijn indices for bound variables.

    The result is guaranteed to precede `t` (`tv << t`), since it morally
    exposes the immediate subterms of `t`; this makes `inspect_ln` usable in
    total, structurally recursive functions over terms, including in
    specifications. The guarantee is justified by the model in which `term` is
    a datatype with a single constructor `Pack` of a `term_view`, `pack_ln` is
    `Pack` and `inspect_ln` removes it. The real `term` is the compiler's
    internal syntax, and the primitive is implemented by the compiler
    consistently with this model.

    Bound variables appear as `Tv_BVar`. Metaprograms usually prefer
    `FStar.Tactics.NamedView.inspect`, which works over a fully named
    representation but runs in `Tac`; `inspect_ln` is `Tot`. Syntax that the
    view cannot represent is returned as `Tv_Unsupp`.

    ```fstar
    let is_fvar_named (t:term) (qn:name) : bool =
      match inspect_ln t with
      | Tv_FVar fv -> inspect_fv fv = qn
      | _ -> false

    let _ = assert True by (guard (is_fvar_named (`Prims.int) int_lid))
    ``` *)
val inspect_ln     : (t:term) -> tv:term_view{tv << t}
(*| Builds a term from a `FStar.Stubs.Reflection.V2.Data.term_view`; the inverse of `FStar.Stubs.Reflection.V2.Builtins.inspect_ln`.

    Implemented by the compiler. `inspect_ln (pack_ln tv) == tv` holds
    (`FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`), but the other
    round trip is only equal up to `FStar.Reflection.TermSpec.denote_term`.
    The named counterpart is `FStar.Tactics.NamedView.pack`.

    ```fstar
    let unit_tm : term = pack_ln (Tv_Const C_Unit)

    let _ = assert True by (guard (term_eq unit_tm (`())))
    ``` *)
val pack_ln        : term_view -> term

(*| Reveals a computation type as a `FStar.Stubs.Reflection.V2.Data.comp_view`: its effect name, result type and flags.

    Implemented by the compiler. The result precedes `c`. The inverse is
    `FStar.Stubs.Reflection.V2.Builtins.pack_comp`; both round trips are exact
    (`FStar.Stubs.Reflection.V2.Builtins.pack_inspect_comp_inv` and
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_comp_inv`). *)
val inspect_comp   : (c:comp) -> cv:comp_view{cv << c}
(*| Builds a computation type from a `FStar.Stubs.Reflection.V2.Data.comp_view`; the inverse of `FStar.Stubs.Reflection.V2.Builtins.inspect_comp`.

    Implemented by the compiler. Helpers such as
    `FStar.Stubs.Reflection.V2.Data.mk_tot_comp` build common views. *)
val pack_comp      : comp_view -> comp

(*| Reveals a top-level declaration as a `FStar.Stubs.Reflection.V2.Data.sigelt_view`.

    Implemented by the compiler. Declarations the view cannot represent are
    returned as `Unk`. The view drops the attributes, qualifiers, options and
    range of the declaration; read those with
    `FStar.Stubs.Reflection.V2.Builtins.sigelt_attrs`,
    `FStar.Stubs.Reflection.V2.Builtins.sigelt_quals`,
    `FStar.Stubs.Reflection.V2.Builtins.sigelt_opts` and
    `FStar.Stubs.Reflection.V2.Builtins.range_of_sigelt`. Unlike the term view,
    there is no `<<` guarantee on the result. *)
val inspect_sigelt : sigelt -> sigelt_view
(*| Builds a top-level declaration from a `FStar.Stubs.Reflection.V2.Data.sigelt_view` other than `Unk`.

    Implemented by the compiler. The result has no attributes or qualifiers;
    add them with `FStar.Stubs.Reflection.V2.Builtins.set_sigelt_attrs` and
    `FStar.Stubs.Reflection.V2.Builtins.set_sigelt_quals`. Declarations built
    this way are typically returned by a metaprogram run with `%splice`. *)
val pack_sigelt    : sv:sigelt_view{~(Unk? sv)} -> sigelt

(*| Returns the fully qualified name of a top-level name (free variable), as a list of path components.

    Implemented by the compiler. For example, `Prims.int` gives
    `["Prims"; "int"]`. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.pack_fv`. *)
val inspect_fv     : fv -> name
(*| Builds a reference to the top-level name with the given fully qualified path.

    Implemented by the compiler. The name is not looked up in any
    environment. Exact inverse of `FStar.Stubs.Reflection.V2.Builtins.inspect_fv`. *)
val pack_fv        : name -> fv

(*| Reveals a named (free) variable as a `FStar.Stubs.Reflection.V2.Data.namedv_view`: its unique identifier, sealed sort and pretty-printing name.

    Implemented by the compiler. The result precedes `v`. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.pack_namedv`. *)
val inspect_namedv : v:namedv -> nv:namedv_view {nv << v}
(*| Builds a named variable from a `FStar.Stubs.Reflection.V2.Data.namedv_view`.

    Implemented by the compiler. Variables are identified by their `uniq`
    field. Exact inverse of `FStar.Stubs.Reflection.V2.Builtins.inspect_namedv`. *)
val pack_namedv    : namedv_view -> namedv

(*| Reveals a de Bruijn bound variable as a `FStar.Stubs.Reflection.V2.Data.bv_view`: its index, sealed sort and pretty-printing name.

    Implemented by the compiler. The result precedes `v`. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.pack_bv`. *)
val inspect_bv     : v:bv -> bvv:bv_view {bvv << v}
(*| Builds a de Bruijn bound variable from a `FStar.Stubs.Reflection.V2.Data.bv_view`.

    Implemented by the compiler. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.inspect_bv`. *)
val pack_bv        : bv_view -> bv

(*| Reveals a let binding as a `FStar.Stubs.Reflection.V2.Data.lb_view`: the bound name, its universe variables, its type and its definition.

    Implemented by the compiler. The result precedes `lb`. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.pack_lb`. Let bindings come from the
    `Sg_Let` view of a declaration. *)
val inspect_lb     : lb:letbinding -> lbv:lb_view {lbv << lb}
(*| Builds a let binding from a `FStar.Stubs.Reflection.V2.Data.lb_view`.

    Implemented by the compiler. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.inspect_lb`. Use it to build the
    bindings of a `Sg_Let` declaration view. *)
val pack_lb        : lb_view -> letbinding

(*| Reveals a binder as a `FStar.Stubs.Reflection.V2.Data.binder_view`: its sort, qualifier, attributes and pretty-printing name.

    Implemented by the compiler. The result precedes `b`. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.pack_binder`. *)
val inspect_binder : b:binder -> bv:binder_view {bv << b}
(*| Builds a binder from a `FStar.Stubs.Reflection.V2.Data.binder_view`.

    Implemented by the compiler. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.inspect_binder`. With an explicit
    qualifier and no attributes the result is a
    `FStar.Stubs.Reflection.V2.Data.simple_binder`
    (`FStar.Stubs.Reflection.V2.Builtins.simple_binder_defn`). *)
val pack_binder    : binder_view -> binder

(*| Reveals the top-level structure of a universe as a `FStar.Stubs.Reflection.V2.Data.universe_view`.

    Implemented by the compiler. The result precedes `u`. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.pack_universe`. *)
val inspect_universe : u:universe -> uv:universe_view{uv << u}
(*| Builds a universe from a `FStar.Stubs.Reflection.V2.Data.universe_view`.

    Implemented by the compiler. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.inspect_universe`. *)
val pack_universe    : universe_view -> universe

(*| Reveals an identifier as its name and source range.

    Implemented by the compiler. The result precedes `i`. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.pack_ident`. *)
val inspect_ident : i:ident -> iv:ident_view{iv << i}
(*| Builds an identifier from a name and a source range.

    Implemented by the compiler. Exact inverse of
    `FStar.Stubs.Reflection.V2.Builtins.inspect_ident`. *)
val pack_ident    : ident_view -> ident

(* The view exposes all details of the term_view, but is not injective:
   [pack_ln] discards the range (and other non-view data), so
   [pack_ln (inspect_ln t)] is only denotationally equal to [t], not [==].
   See [FStar.Reflection.TermSpec.denote_term]. *)
(*| Inspecting a packed term view gives back the same view.

    Assumed. The converse does not hold with `==`: `pack_ln` discards the
    range and other data outside the view, so `pack_ln (inspect_ln t)` is
    only equal to `t` up to `FStar.Reflection.TermSpec.denote_term`. *)
val inspect_pack_inv : (tv:term_view) -> Lemma (inspect_ln (pack_ln tv) == tv)

(* [comp_view] mirrors [comp_typ] field for field -- an effect name, a result
   type and some flags -- so neither direction of this round trip loses
   anything, and both hold unconditionally. *)
(*| Packing an inspected computation type gives back the same computation type.

    Assumed. A `FStar.Stubs.Reflection.V2.Data.comp_view` mirrors the internal
    computation type field for field, so this round trip is exact. The other
    direction is `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_comp_inv`. *)
val pack_inspect_comp_inv : (c:comp) -> Lemma (pack_comp (inspect_comp c) == c)
(*| Inspecting a packed computation view gives back the same view.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.pack_inspect_comp_inv`. *)
val inspect_pack_comp_inv (cv:comp_view) : Lemma (inspect_comp (pack_comp cv) == cv)

(*| Inspecting a packed named-variable view gives back the same view.

    Assumed. Together with `FStar.Stubs.Reflection.V2.Builtins.pack_inspect_namedv`
    it makes `pack_namedv` and `inspect_namedv` a bijection. *)
val inspect_pack_namedv (xv:namedv_view) : Lemma (inspect_namedv (pack_namedv xv) == xv)
(*| Packing an inspected named variable gives back the same variable.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_namedv`. *)
val pack_inspect_namedv (x:namedv) : Lemma (pack_namedv (inspect_namedv x) == x)

(*| Inspecting a packed bound-variable view gives back the same view.

    Assumed. Together with `FStar.Stubs.Reflection.V2.Builtins.pack_inspect_bv`
    it makes `pack_bv` and `inspect_bv` a bijection. *)
val inspect_pack_bv (xv:bv_view) : Lemma (inspect_bv (pack_bv xv) == xv)
(*| Packing an inspected bound variable gives back the same variable.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_bv`. *)
val pack_inspect_bv (x:bv) : Lemma (pack_bv (inspect_bv x) == x)

(*| Inspecting a packed binder view gives back the same view.

    Assumed. Together with `FStar.Stubs.Reflection.V2.Builtins.pack_inspect_binder`
    it makes `pack_binder` and `inspect_binder` a bijection. *)
val inspect_pack_binder (bview:binder_view) : Lemma (inspect_binder (pack_binder bview) == bview)
(*| Packing an inspected binder gives back the same binder.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_binder`. *)
val pack_inspect_binder (b:binder) : Lemma (pack_binder (inspect_binder b) == b)

(*| Packing the name of a top-level name gives back the same top-level name.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_fv`. *)
val pack_inspect_fv (fv:fv) : Lemma (ensures pack_fv (inspect_fv fv) == fv)
(*| The name of a top-level name built from a path is that path.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.pack_inspect_fv`. *)
val inspect_pack_fv (nm:name) : Lemma (ensures inspect_fv (pack_fv nm) == nm)

(*| Packing an inspected universe gives back the same universe.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_universe`. *)
val pack_inspect_universe (u:universe) : Lemma (pack_universe (inspect_universe u) == u)
(*| Inspecting a packed universe view gives back the same view.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.pack_inspect_universe`. *)
val inspect_pack_universe (uv:universe_view) : Lemma (inspect_universe (pack_universe uv) == uv)

(*| Packing an inspected identifier gives back the same identifier.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_ident`. *)
val pack_inspect_ident (u:ident) : Lemma (pack_ident (inspect_ident u) == u)
(*| Inspecting an identifier built from a name and range gives back that name and range.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.pack_inspect_ident`. *)
val inspect_pack_ident (uv:ident_view) : Lemma (inspect_ident (pack_ident uv) == uv)

(*| Packing an inspected let binding gives back the same let binding.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_lb`. *)
val pack_inspect_lb (lb:letbinding) : Lemma (pack_lb (inspect_lb lb) == lb)
(*| Inspecting a packed let-binding view gives back the same view.

    Assumed. The other direction is
    `FStar.Stubs.Reflection.V2.Builtins.pack_inspect_lb`. *)
val inspect_pack_lb (lbv:lb_view) : Lemma (inspect_lb (pack_lb lbv) == lbv)

(* The sigelt view is likewise not injective: [pack_sigelt] discards the
   attributes/quals/opts/range, so [pack_sigelt (inspect_sigelt se)] is
   only view-equal to [se], not [==]. *)
(*| Inspecting a declaration packed from a view other than `Unk` gives back the same view.

    Assumed. There is no converse with `==`: `pack_sigelt` discards the
    attributes, qualifiers, options and range, so
    `pack_sigelt (inspect_sigelt se)` only has the same view as `se`. *)
val inspect_pack_sigelt (sev:sigelt_view { ~ (Unk? sev) }) : Lemma (inspect_sigelt (pack_sigelt sev) == sev)


(*| A binder is simple exactly when it has an explicit qualifier and no attributes.

    Assumed; this gives meaning to the abstract
    `FStar.Stubs.Reflection.V2.Data.binder_is_simple`. Triggered automatically
    on `binder_is_simple b`. *)
val simple_binder_defn (b:binder) :
  Lemma (binder_is_simple b <==>
          Q_Explicit? (inspect_binder b).qual /\ Nil? (inspect_binder b).attrs)
        [SMTPat (binder_is_simple b)]

(*| Joins the components of a qualified name with dots, as in `["FStar"; "List"]` to `"FStar.List"`.

    Implemented by the compiler. Equivalent to `FStar.String.concat "."`; it is
    a primitive only so that reflection and tactics need not depend on
    `FStar.String`. The inverse is `FStar.Stubs.Reflection.V2.Builtins.explode_qn`. *)
val implode_qn     : list string -> string
(*| Splits a dotted qualified name into its components, as in `"FStar.List"` to `["FStar"; "List"]`.

    Implemented by the compiler. Equivalent to `FStar.String.split ['.']`; it
    is a primitive only so that reflection and tactics need not depend on
    `FStar.String`. The inverse is `FStar.Stubs.Reflection.V2.Builtins.implode_qn`. *)
val explode_qn     : string -> list string
(*| Compares two strings, returning `0` exactly when they are equal.

    Implemented by the compiler, equivalent to `FStar.String.compare`; only the
    equality case is specified. A primitive so that reflection and tactics need
    not depend on `FStar.String`. *)
val compare_string : s1:string -> s2:string -> x:int{x == 0 <==> s1 == s2}

(*| Looks up a top-level declaration by fully qualified name in an environment.

    Implemented by the compiler. Returns `None` when the name is not defined in
    the environment. Despite the name, any kind of declaration is found, not
    only types; inspect the result with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_sigelt`. *)
val lookup_typ            : env -> name -> option sigelt

(*| Compares two de Bruijn bound variables by their index.

    Implemented by the compiler. Deprecated: use
    `FStar.Reflection.V2.Derived.compare_bv`, which compares the `index`
    fields of their views. *)
[@@(deprecated "Use FStar.Reflection.V2.Derived.compare_bv")]
val compare_bv            : bv -> bv -> order

(*| Compares two named variables by their unique identifier.

    Implemented by the compiler. Deprecated: use
    `FStar.Reflection.V2.Derived.compare_namedv`, which compares the `uniq`
    fields of their views. *)
[@@(deprecated "Use FStar.Reflection.V2.Derived.compare_namedv")]
val compare_namedv        : namedv -> namedv -> order

(*| Returns all variable bindings in an environment.

    Implemented by the compiler. Each `FStar.Stubs.Reflection.V2.Data.binding`
    carries the variable's unique identifier and its (unsealed) sort. *)
val vars_of_env           : env -> list binding

(*| Returns the name of the module currently being checked in an environment.

    Implemented by the compiler. *)
val moduleof              : env -> name

(*| Returns all top-level declarations that carry a given attribute.

    Implemented by the compiler. The attribute `attr` must be a top-level name
    (a `Tv_FVar`); a declaration matches if one of its attributes is that name,
    possibly applied to arguments. Inspect the returned declarations to read
    the arguments. Used, for example, to find all typeclass instances and their
    functional dependencies. `FStar.Stubs.Reflection.V2.Builtins.lookup_attr`
    returns just the names. *)
val lookup_attr_ses       : attr:term -> env -> list sigelt

(*| Returns the names of all top-level declarations that carry a given attribute.

    Implemented by the compiler. As
    `FStar.Stubs.Reflection.V2.Builtins.lookup_attr_ses`, but returns names
    instead of declarations. *)
val lookup_attr           : term -> env -> list fv

(*| Returns all top-level names defined in an environment.

    Implemented by the compiler. *)
val all_defs_in_env       : env -> list fv

(*| Returns all top-level names defined in the given module.

    Implemented by the compiler. The module is given by its qualified name,
    for example `["FStar"; "List"; "Tot"; "Base"]`. *)
val defs_in_module        : env -> name -> list fv

(*| Returns the names of all modules opened in the scope of an environment.

    Implemented by the compiler. *)
val env_open_modules      : env -> list name

(*| Extends an environment with a named variable.

    Implemented by the compiler. Useful when traversing a term: after opening a
    binder of an abstraction, match branch and so on, push the resulting
    variable so that the body can be checked or inspected in the extended
    environment. *)
val push_namedv           : env -> namedv -> env

(*| Returns the attributes of a top-level declaration, as terms.

    Implemented by the compiler. These are reflected terms, not values of
    `Prims.attribute`. Set them with
    `FStar.Stubs.Reflection.V2.Builtins.set_sigelt_attrs`. *)
val sigelt_attrs     : sigelt -> list term
(*| Replaces the attributes of a top-level declaration.

    Implemented by the compiler. The previous attributes are discarded; read
    them first with `FStar.Stubs.Reflection.V2.Builtins.sigelt_attrs` to extend
    them. *)
val set_sigelt_attrs : list term -> sigelt -> sigelt

(*| Returns the qualifiers of a top-level declaration.

    Implemented by the compiler. See
    `FStar.Stubs.Reflection.V2.Data.qualifier`, and
    `FStar.Stubs.Reflection.V2.Builtins.set_sigelt_quals` to change them. *)
val sigelt_quals     : sigelt -> list qualifier
(*| Replaces the qualifiers of a top-level declaration.

    Implemented by the compiler. The previous qualifiers are discarded; read
    them first with `FStar.Stubs.Reflection.V2.Builtins.sigelt_quals` to extend
    them. *)
val set_sigelt_quals : list qualifier -> sigelt -> sigelt

(*| Returns the options under which a top-level declaration was typechecked.

    Implemented by the compiler. Returns `None` if the declaration was checked
    without `--record_options`. See `FStar.Stubs.Reflection.V2.Builtins.embed_vconfig`
    to reuse the result. *)
val sigelt_opts : sigelt -> option vconfig

(*| Embeds a `FStar.VConfig.vconfig` as a term.

    Implemented by the compiler. Used, for instance, to build a
    `FStar.VConfig.check_with` attribute from options read with
    `FStar.Stubs.Reflection.V2.Builtins.sigelt_opts`. *)
val embed_vconfig : vconfig -> term

(*| Applies a substitution to a term.

    Implemented by the compiler. See `FStar.Stubs.Syntax.Syntax.subst_elt` for
    the available substitution elements (replacing de Bruijn or named variables
    by terms, renaming between them, and universe substitutions). *)
val subst_term : subst_t -> term -> term

(* TODO: userspace? *)
(*| Applies a substitution to a computation type.

    Implemented by the compiler. The computation-type counterpart of
    `FStar.Stubs.Reflection.V2.Builtins.subst_term`. *)
val subst_comp : subst_t -> comp -> comp

(*| Returns the source range of a term.

    Implemented by the compiler. *)
val range_of_term : term -> range

(*| Returns the source range of a top-level declaration.

    Implemented by the compiler. *)
val range_of_sigelt : sigelt -> range
