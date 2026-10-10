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
module FStar.Stubs.Reflection.Types

include FStar.Range
include FStar.Sealed

(*| A named (free) variable of a reflected term, identified by a unique number.

    Abstract and assumed; the compiler implements it. Inspect it with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_namedv`. Contrast with
    `FStar.Stubs.Reflection.Types.bv`, a variable bound by de Bruijn index. *)
assume new type namedv  // named fresh variable
(*| A bound variable of a reflected term, referred to by its de Bruijn index.

    Abstract and assumed; the compiler implements it. Inspect it with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_bv`. Contrast with
    `FStar.Stubs.Reflection.Types.namedv`. *)
assume new type bv      // db variable
(*| A binder of a reflected abstraction, arrow, refinement or let: a sort with a qualifier, attributes and a pretty-printing name.

    Abstract and assumed; the compiler implements it. Inspect it with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_binder`. *)
assume new type binder

(*| A reflected F\* term, as manipulated by metaprograms.

    Abstract and assumed; it is the compiler's internal syntax. Inspect and
    build terms with `FStar.Stubs.Reflection.V2.Builtins.inspect_ln` and
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, or with the named views of
    `FStar.Tactics.NamedView`. A quotation (an expression preceded by a backquote) has type
    `term`. Equality on terms is not decidable; compare them with
    `FStar.Reflection.TermEq.Simple.term_eq`. *)
assume new type term
(*| A typing environment: the top-level definitions and local variables in scope.

    Abstract and assumed; the compiler implements it. Query it with, for
    example, `FStar.Stubs.Reflection.V2.Builtins.lookup_typ` and
    `FStar.Stubs.Reflection.V2.Builtins.vars_of_env`. *)
assume new type env
(*| A reference to a top-level name (a free variable bound at the top level).

    Abstract and assumed; the compiler implements it. Converted to and from its
    fully qualified `FStar.Stubs.Reflection.Types.name` with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_fv` and
    `FStar.Stubs.Reflection.V2.Builtins.pack_fv`. *)
assume new type fv
(*| A reflected computation type, such as the codomain of an arrow.

    Abstract and assumed; the compiler implements it. Inspect it with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_comp`. *)
assume new type comp
(*| A reflected top-level declaration, called `def` in the Meta-F\* paper.

    Abstract and assumed; the compiler implements it. Inspect it with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_sigelt`. *)
assume new type sigelt // called `def` in the paper, but we keep the internal name here
(*| The internal data of a unification variable together with its delayed substitution.

    Abstract and assumed; the compiler implements it. Appears in the `Tv_Uvar`
    case of `FStar.Stubs.Reflection.V2.Data.term_view` and cannot be inspected
    further. *)
assume new type ctx_uvar_and_subst
(*| A single binding of a top-level let declaration.

    Abstract and assumed; the compiler implements it. Inspect it with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_lb`. *)
assume new type letbinding

(*| An identifier: a name together with its source range.

    Abstract and assumed; the compiler implements it. Inspect it with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_ident`. *)
assume new type ident
(*| A universe unification variable.

    Abstract and assumed; the compiler implements it. Appears in the `Uv_Unif`
    case of `FStar.Stubs.Reflection.V2.Data.universe_view`. *)
assume new type universe_uvar
(*| A reflected universe level.

    Abstract and assumed; the compiler implements it. Inspect it with
    `FStar.Stubs.Reflection.V2.Builtins.inspect_universe`. *)
assume new type universe

(*| A fully qualified name, as the list of its dot-separated components.

    For example `Prims.int` is `["Prims"; "int"]`. Equality is decidable.
    `FStar.Stubs.Reflection.V2.Builtins.implode_qn` and
    `FStar.Stubs.Reflection.V2.Builtins.explode_qn` convert to and from the
    dotted string. *)
type name : eqtype = list string

(*| The name of a universe variable; an alias of `FStar.Stubs.Reflection.Types.ident`. *)
type univ_name = ident
(*| A reflected term used as a type; an alias of `FStar.Stubs.Reflection.Types.term`. *)
type typ     = term
(*| A list of reflected binders. *)
type binders = list binder

(*| A list of reflected top-level declarations, as produced by a metaprogram for `%splice`. *)
type decls = list sigelt
