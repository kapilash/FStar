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
module FStar.Stubs.Reflection.V2.Data

include FStar.Stubs.Syntax.Syntax
include FStar.IntegerLiteral
open FStar.Stubs.Reflection.Types

(*| The type of pretty-printing names attached to variables and binders.

    It is a sealed string (`FStar.Sealed.Inhabited.sealed ""`): the name can be
    observed only by a tactic, and all values of `ppname_t` are provably equal,
    so renaming a variable never changes the logical meaning of a term. Build
    one with `FStar.Stubs.Reflection.V2.Data.as_ppname`. *)
let ppname_t = FStar.Sealed.Inhabited.sealed ""
(*| Seals a string as a pretty-printing name. *)
let as_ppname (x:string) : ppname_t = FStar.Sealed.Inhabited.seal x

(*| The signedness of a machine integer literal: `Signed` or `Unsigned`. *)
type int_signedness =
  | Signed
  | Unsigned

(*| The width of a machine integer literal: `Int8`, `Int16`, `Int32`, `Int64`, or `Sizet` for `FStar.SizeT`. *)
type int_width =
  | Int8
  | Int16
  | Int32
  | Int64
  | Sizet

(*| The view of a constant appearing in a term (`Tv_Const`) or a pattern (`Pat_Constant`).

    Constructors:

    - `C_Unit`: the unit value `()`.
    - `C_Int n base`: a mathematical integer literal.
    - `C_MachineInt n base s w`: a machine integer literal of signedness `s` and width `w`.
    - `C_True` and `C_False`: the boolean literals.
    - `C_String s`: a string literal.
    - `C_Range r`: a source range constant.
    - `C_Reify` and `C_Reflect eff`: the `reify` operator and the `reflect` operator of effect `eff`.
    - `C_Real r`: a real literal, represented exactly (see `FStar.RealLiteral`).
    - `C_Char c`: a character literal.

    The sealed `FStar.IntegerLiteral.int_base` of integer literals records the
    base the literal was written in. It is presentational only and sealed so
    that the logic cannot observe it: `0x10` and `16` are the same constant and
    are provably equal. Metaprograms can read it with
    `FStar.Stubs.Tactics.Unseal.unseal`. *)
noeq
type vconst =
  | C_Unit      : vconst
  | C_Int       : int -> FStar.Sealed.sealed int_base -> vconst
  | C_MachineInt : int -> FStar.Sealed.sealed int_base -> int_signedness -> int_width -> vconst
  (* The [sealed int_base] records the base the literal was written in (see
     FStar.IntegerLiteral). It is presentational metadata only, and is sealed
     precisely so that it cannot be observed in the logical fragment: 0x10 and
     16 are the same constant, and F* proves them equal. Metaprograms can still
     read it with FStar.Tactics.unseal. *)
  | C_True      : vconst
  | C_False     : vconst
  | C_String    : string -> vconst
  | C_Range     : range -> vconst
  | C_Reify     : vconst
  | C_Reflect   : name -> vconst
  | C_Real      : FStar.RealLiteral.real_literal -> vconst
  (* Real literals are represented exactly, by their (canonical)
     mantissa and exponent: see FStar.RealLiteral. *)
  | C_Char      : Char.char -> vconst
  (* TODO: complete *)

(*| A list of reflected universes. *)
type universes = list universe

(*| The view of an identifier: its name and its source range.

    See `FStar.Stubs.Reflection.V2.Builtins.inspect_ident`. *)
type ident_view = string & range

(*| The view of a pattern in a `match` branch.

    Constructors:

    - `Pat_Constant c`: matches the constant `c`.
    - `Pat_Cons head univs subpats`: a fully applied constructor `head`, optionally with explicit universes.
    - `Pat_Var sort ppname`: a pattern-bound variable.
    - `Pat_Dot_Term t`: a dot pattern, whose value is determined by the rest of the pattern and the type.

    Each sub-pattern of `Pat_Cons` is paired with a boolean that marks whether
    it is an explicitly provided implicit argument. A `Pat_Var` carries no
    variable: the variable is referred to by its de Bruijn index in the branch
    body, and its sort is sealed. The sort is ignored by the typechecker but
    can guide a metaprogram heuristically; all `Pat_Var` patterns are
    provably equal. *)
noeq
type pattern =
 // A built-in constant
 | Pat_Constant :
     c : vconst ->
     pattern

 // A fully applied constructor, each boolean marks whether the
 // argument was an explicitly-provided implicit argument
 | Pat_Cons :
     head    : fv ->
     univs   : option universes ->
     subpats : list (pattern & bool) ->
     pattern

 // A pattern-bound variable. It has a sealed sort in it.
 // This sort is ignored by the typechecker, but may be useful
 // for metaprogram to look at heuristically. There is nothing
 // else here but a ppname, the variable is referred to by its DB index.
 // This means all Pat_Var are provably equal.
 | Pat_Var :
     sort   : sealed term ->
     ppname : ppname_t ->
     pattern

 // Dot pattern: resolved by other elements in the pattern and type
 | Pat_Dot_Term :
     t : option term ->
     pattern

(*| A `match` branch: a pattern and the body it guards.

    The variables bound by the pattern are de Bruijn indices in the body. *)
type branch = pattern & term  // | pattern -> term

(*| The qualifier of a binder or an argument.

    Constructors:

    - `Q_Explicit`: an ordinary explicit argument.
    - `Q_Implicit`: an implicit argument, written with `#`.
    - `Q_Equality`: an argument that must be resolved by unification up to equality, written with `$`.
    - `Q_Meta t`: an implicit argument solved by running the tactic `t`, written `#[t]`. *)
noeq
type aqualv =
  | Q_Implicit
  | Q_Explicit
  | Q_Equality
  | Q_Meta of term

(*| An argument of an application: a term and its qualifier. *)
type argv = term & aqualv

(*| The view of a named variable: its unique identifier `uniq`, its sealed sort and its pretty-printing name.

    Variables are distinguished by `uniq` only; the sealed sort and name are
    for metaprograms and printing. See
    `FStar.Stubs.Reflection.V2.Builtins.inspect_namedv`. *)
noeq
type namedv_view = {
  uniq   : nat;
  sort   : sealed typ; // REMOVE?
  ppname : ppname_t;
}

(*| The view of a de Bruijn bound variable: its `index`, its sealed sort and its pretty-printing name.

    See `FStar.Stubs.Reflection.V2.Builtins.inspect_bv`. *)
noeq
type bv_view = {
  index  : nat;
  sort   : sealed typ; // REMOVE?
  ppname : ppname_t;
}

(*| The view of a binder: its `sort`, qualifier `qual`, attributes `attrs` and pretty-printing name `ppname`.

    See `FStar.Stubs.Reflection.V2.Builtins.inspect_binder`. *)
noeq
type binder_view = {
  sort   : typ;
  qual   : aqualv;
  attrs  : list term;
  ppname : ppname_t;
}

(*| A variable in a typing environment: like a named variable, but with an unsealed sort.

    Fields: the unique identifier `uniq`, the `sort` and the pretty-printing
    name `ppname`. See `FStar.Stubs.Reflection.V2.Builtins.vars_of_env`. *)
noeq
type binding = {
  uniq   : nat;
  sort   : typ;
  ppname : ppname_t;
}
(*| A list of environment bindings. *)
type bindings = list binding

(*| Holds of binders that have an explicit qualifier and no attributes.

    Binders are also used in let bindings and refinements, where qualifiers and
    attributes cannot appear; such binders are called simple. The predicate is
    abstract here; its meaning is given by
    `FStar.Stubs.Reflection.V2.Builtins.simple_binder_defn`, once
    `FStar.Stubs.Reflection.V2.Builtins.inspect_binder` is in scope. *)
val binder_is_simple : binder -> Tot bool

(*| A binder with an explicit qualifier and no attributes, as used in let bindings and refinements.

    See `FStar.Stubs.Reflection.V2.Data.binder_is_simple`. *)
type simple_binder = b:binder{binder_is_simple b}

(*| The view of a universe level, one constructor deep.

    Constructors:

    - `Uv_Zero`: universe 0.
    - `Uv_Succ u`: the successor of `u`.
    - `Uv_Max us`: the maximum of the universes `us`.
    - `Uv_BVar n`: a bound universe variable, by de Bruijn index.
    - `Uv_Name id`: a named universe variable.
    - `Uv_Unif uv`: a universe unification variable.
    - `Uv_Unk`: an unknown universe.

    See `FStar.Stubs.Reflection.V2.Builtins.inspect_universe`. *)
noeq
type universe_view =
  | Uv_Zero : universe_view
  | Uv_Succ : universe -> universe_view
  | Uv_Max  : universes -> universe_view
  | Uv_BVar : nat -> universe_view
  | Uv_Name : univ_name -> universe_view
  | Uv_Unif : universe_uvar -> universe_view
  | Uv_Unk  : universe_view

(*| The locally nameless view of a term, one constructor deep, as returned by `FStar.Stubs.Reflection.V2.Builtins.inspect_ln`.

    Constructors:

    - `Tv_Var v`: a named (free) variable.
    - `Tv_BVar v`: a variable bound by de Bruijn index.
    - `Tv_FVar v`: a top-level name.
    - `Tv_UInst v us`: a top-level name instantiated with universes `us`.
    - `Tv_App hd a`: the application of `hd` to one argument `a`.
    - `Tv_Abs bv body`: a lambda abstraction.
    - `Tv_Arrow bv c`: an arrow type with codomain computation type `c`.
    - `Tv_Type u`: the universe `Type u`.
    - `Tv_Refine b ref`: the refinement of the sort of `b` by `ref`.
    - `Tv_Const c`: a constant.
    - `Tv_Uvar n u`: a unification variable.
    - `Tv_Let recf attrs b def body`: a local, possibly recursive, let binding.
    - `Tv_Match scrutinee ret brs`: a pattern match, with an optional return annotation.
    - `Tv_AscribedT e t tac use_eq`: `e` ascribed with type `t`, optionally with a tactic.
    - `Tv_AscribedC e c tac use_eq`: `e` ascribed with computation type `c`, optionally with a tactic.
    - `Tv_Unknown`: an underscore to be inferred.
    - `Tv_Unsupp`: a term that could not be inspected because the view does not support it.

    Bodies of binding forms refer to the bound variable by de Bruijn index.
    Applications are binary; nested `Tv_App` nodes represent multiple
    arguments. Metaprograms usually work instead with the named view
    `FStar.Tactics.NamedView.named_term_view`, which opens binders with fresh
    names.

    ```fstar
    let is_fvar_named (t:term) (qn:name) : bool =
      match inspect_ln t with
      | Tv_FVar fv -> inspect_fv fv = qn
      | _ -> false

    let _ = assert True by (guard (is_fvar_named (`Prims.int) int_lid))
    ``` *)
noeq
type term_view =
  | Tv_Var    : v:namedv -> term_view
  | Tv_BVar   : v:bv -> term_view
  | Tv_FVar   : v:fv -> term_view
  | Tv_UInst  : v:fv -> us:universes -> term_view
  | Tv_App    : hd:term -> a:argv -> term_view
  | Tv_Abs    : bv:binder -> body:term -> term_view
  | Tv_Arrow  : bv:binder -> c:comp -> term_view
  | Tv_Type   : universe -> term_view
  | Tv_Refine : b:simple_binder -> ref:term -> term_view
  | Tv_Const  : vconst -> term_view
  | Tv_Uvar   : nat -> ctx_uvar_and_subst -> term_view
  | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> term_view
  | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> term_view
  | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> term_view
  | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> term_view
  | Tv_Unknown  : term_view // An underscore: _
  | Tv_Unsupp : term_view // failed to inspect, not supported

(*| Holds of term views that are not ascriptions (`Tv_AscribedT` or `Tv_AscribedC`). *)
let notAscription (tv:term_view) : bool =
  not (Tv_AscribedT? tv) && not (Tv_AscribedC? tv)

// Very basic for now
(*| A `decreases` clause.

    Constructors:

    - `Decreases_lex ts`: the lexicographic ordering on the list of terms `ts`.
    - `Decreases_wf rel e`: the term `e` decreasing according to the well-founded relation `rel`.

    Mirrors the compiler's internal `decreases_order`. *)
noeq
type decreases_order =
  | Decreases_lex : list term -> decreases_order
  | Decreases_wf  : term -> term -> decreases_order

(*| A flag attached to a computation type.

    Constructors:

    - `SMTPAT t`: the SMT patterns of a `Lemma`, as a list literal `t`.
    - `DECREASES d`: a `decreases` clause.

    Mirrors the compiler's internal `cflag`. *)
noeq
type cflag =
  | SMTPAT    : term -> cflag   (* a [Lemma]'s SMT patterns, as a list literal *)
  | DECREASES : decreases_order -> cflag

(*| The view of a computation type: an effect name, a result type and flags.

    Fields:

    - `effect_name`: the root effect, after resolving effect abbreviations.
    - `result_typ`: the result type.
    - `flags`: the flags, see `FStar.Stubs.Reflection.V2.Data.cflag`.
    - `source_effect_name`: the effect name as written, for presentation only.

    This mirrors the compiler's internal computation type field for field, so
    `FStar.Stubs.Reflection.V2.Builtins.inspect_comp` and
    `FStar.Stubs.Reflection.V2.Builtins.pack_comp` are exact inverses.

    A computation type carries no logical content of its own. A precondition is
    an implicit `squash` binder on the arrow and a postcondition is a
    refinement of `result_typ`; there are no weakest-precondition transformers
    and no effect indices. To read back a specification in the shape a user
    wrote it, look for a trailing implicit `squash` binder on the arrow and for
    a refinement on `result_typ`. An effect abbreviation such as `Lemma` is
    resolved away in `effect_name`; `source_effect_name` keeps the written name
    and equals `effect_name` when no abbreviation was used. See
    `doc/ref/simplified_effect_system.md`. *)
noeq
type comp_view = {
  effect_name : name;
  result_typ  : typ;
  flags       : list cflag;
  (* The effect name as it was *written*.  An effect abbreviation is a bare
     alias of one effect name for another ([effect Lemma = Tot]), and the
     desugarer resolves it away, so [effect_name] is always the *root* effect.
     The name the user wrote is kept here, for presentation only; it equals
     [effect_name] whenever no abbreviation was used. *)
  source_effect_name : name;
}

(*| The name of the `Tot` effect, `["Prims"; "Tot"]`.

    This is the effect the desugarer gives to an arrow with no effect
    annotation. Effect abbreviations are resolved before they reach a
    computation type, so this root name can be compared literally; see
    `FStar.Stubs.Reflection.V2.Data.is_tot_comp`. *)
let tot_effect_name  : name = ["Prims"; "Tot"]
(*| The name of the `GTot` effect, `["Prims"; "GTot"]`.

    Effect abbreviations are resolved before they reach a computation type, so
    this root name can be compared literally; see
    `FStar.Stubs.Reflection.V2.Data.is_gtot_comp`. *)
let gtot_effect_name : name = ["Prims"; "GTot"]

(*| Builds the view of a computation type with the given effect and result type, no flags, and the same source effect name. *)
let mk_comp_view (eff:name) (res:typ) : comp_view =
  { effect_name = eff; result_typ = res; flags = []; source_effect_name = eff }

(*| Builds the view of a `Tot` computation type with the given result type.

    ```fstar
    let _ = assert_norm (is_tot_comp (mk_tot_comp (`int)))
    ``` *)
let mk_tot_comp  (res:typ) : comp_view = mk_comp_view tot_effect_name res
(*| Builds the view of a `GTot` computation type with the given result type. *)
let mk_gtot_comp (res:typ) : comp_view = mk_comp_view gtot_effect_name res

(*| Tests whether a computation view has the `Tot` effect.

    Compares `effect_name` with `FStar.Stubs.Reflection.V2.Data.tot_effect_name`,
    so a computation written with an abbreviation of `Tot` also qualifies. *)
let is_tot_comp  (cv:comp_view) : bool = cv.effect_name = tot_effect_name
(*| Tests whether a computation view has the `GTot` effect.

    Compares `effect_name` with `FStar.Stubs.Reflection.V2.Data.gtot_effect_name`. *)
let is_gtot_comp (cv:comp_view) : bool = cv.effect_name = gtot_effect_name
(*| Tests whether a computation view has the `Tot` or the `GTot` effect. *)
let is_tot_or_gtot_comp (cv:comp_view) : bool = is_tot_comp cv || is_gtot_comp cv

(*| A constructor of an inductive type: its fully qualified name and its type.

    In `Sg_Inductive`, the constructor type is already opened with the
    universe variables and applied to the parameters of the type. *)
type ctor = name & typ

(*| The view of a top-level let binding.

    Fields: the bound name `lb_fv`, its universe variables `lb_us`, its type
    `lb_typ` and its definition `lb_def`. See
    `FStar.Stubs.Reflection.V2.Builtins.inspect_lb`. *)
noeq
type lb_view = {
    lb_fv : fv;
    lb_us : list univ_name;
    lb_typ : typ;
    lb_def : term
}

(*| The view of a top-level declaration, as returned by `FStar.Stubs.Reflection.V2.Builtins.inspect_sigelt`.

    Constructors:

    - `Sg_Let r lbs`: a let declaration with bindings `lbs`, recursive when `r` is true.
    - `Sg_Inductive nm univs params typ cts`: an inductive type and its constructors.
    - `Sg_Val nm univs typ`: a `val` declaration.
    - `Unk`: any other declaration, which the view does not support.

    In `Sg_Inductive`, `nm` is the name of the type, `univs` its universe
    variables, `params` its parameters, `typ` its type after the parameters
    (the indices and the resulting `Type`), and `cts` its constructors, opened
    with `univs` and applied to `params`. Internally a type and its
    constructors are split into a bundle; the view coalesces them, which is
    more convenient for metaprograms. Mutually inductive types are not
    supported. *)
noeq
type sigelt_view =
  | Sg_Let :
      (r:bool) ->
      (lbs:list letbinding) ->
      sigelt_view

  // Sg_Inductive basically coalesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive :
      (nm:name) ->              // name of the inductive type being defined
      (univs:list univ_name) -> // universe variables
      (params:binders) ->       // parameters
      (typ:typ) ->              // the type annotation for the inductive, i.e., indices -> Type #u
      (cts:list ctor) ->        // the constructors, opened with univs and applied to params already
      sigelt_view

  | Sg_Val :
      (nm:name) ->
      (univs:list univ_name) ->
      (typ:typ) ->
      sigelt_view

  | Unk

(*| A qualifier on a top-level declaration, as read by `FStar.Stubs.Reflection.V2.Builtins.sigelt_quals`.

    The constructors mirror the compiler's internal qualifiers. Those a user
    can write:

    - `Assumption`: declared without definition (`assume`).
    - `New`: a fresh type constant, distinct from all others (`new`).
    - `Private`: invisible outside the module.
    - `Unfold_for_unification_and_vcgen`: always unfolded by the normalizer (`unfold`).
    - `Irreducible`: never unfolded by the normalizer.
    - `Inline_for_extraction`: unfolded when compiling the program.
    - `NoExtract`: not extracted.
    - `Noeq` and `Unopteq`: how the decidable-equality predicate of a type is generated.
    - `TotalEffect`: an effect that forbids non-termination (`total`).
    - `Logic`: intended for use in the refinement logic.
    - `Reifiable` and `Reflectable eff`: effect qualifiers.

    The others are internal and added by the compiler: `Visible_default`,
    `Discriminator`, `Projector`, `RecordType`, `RecordConstructor` (record
    namespace and field names), `Action` (an effect action),
    `ExceptionConstructor` (a constructor of `exn`), `HasMaskedEffect` (a let
    binding that may have a top-level effect), `Effect` (a name that
    corresponds to an effect), `OnlyName` (a placeholder for name resolution)
    and `InternalAssumption` (an assumption generated by F\*, such as a
    `hasEq` axiom). *)
noeq
type qualifier =
  | Assumption
  | InternalAssumption
  | New
  | Private
  | Unfold_for_unification_and_vcgen
  | Visible_default
  | Irreducible
  | Inline_for_extraction
  | NoExtract
  | Noeq
  | Unopteq
  | TotalEffect
  | Logic
  | Reifiable
  | Reflectable       of name
  | Discriminator     of name
  | Projector         of name & ident
  | RecordType        of list ident & list ident
  | RecordConstructor of list ident & list ident
  | Action            of name
  | ExceptionConstructor
  | HasMaskedEffect
  | Effect
  | OnlyName

(* Should remove, but there are clients using it. *)
(*| Natural numbers used as variable identifiers. Kept for compatibility with existing clients. *)
let var : eqtype = nat
