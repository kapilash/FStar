(*
   Copyright 2008-2023 Microsoft Research

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
module FStar.Tactics.NamedView

open FStar.Tactics.Effect
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
module R = FStar.Stubs.Reflection.Types
module RD = FStar.Stubs.Reflection.V2.Data
module RB = FStar.Stubs.Reflection.V2.Builtins

(* Re export the syntax types. Expose variables as their views, users do
not need to pack/inspect these if they are using the named view. *)
(*| A named variable, exposed directly as its view
    `FStar.Stubs.Reflection.V2.Data.namedv_view`: unique number, sealed sort
    and pretty-printing name.

    Named variables are the free variables of a term; the named view opens
    binders into them. No packing or inspection is needed, and
    `FStar.Tactics.NamedView.inspect_namedv` and `pack_namedv` are identities. *)
type namedv   = RD.namedv_view
(*| A bound variable (de Bruijn index), exposed directly as its view
    `FStar.Stubs.Reflection.V2.Data.bv_view`.

    `FStar.Tactics.NamedView.inspect` opens binders, so `Tv_BVar` only shows
    up for a term with loose de Bruijn indices. *)
type bv       = RD.bv_view
(*| A computation type, exposed directly as its view
    `FStar.Stubs.Reflection.V2.Data.comp_view`.

    Arrows of `FStar.Tactics.NamedView.named_term_view` carry this view. Use
    `FStar.Stubs.Reflection.V2.Builtins.pack_comp` to get the abstract
    `FStar.Stubs.Reflection.Types.comp`. *)
type comp     = RD.comp_view
(*| A variable bound in a typing environment, the record
    `FStar.Stubs.Reflection.V2.Data.binding` of unique number, sort and
    pretty-printing name.

    Introduction tactics such as `FStar.Stubs.Tactics.V2.Builtins.intro` return
    bindings. `FStar.Tactics.V2.SyntaxCoercions` coerces them to terms, and
    `FStar.Tactics.NamedView.binding_to_binder` makes a binder from one. *)
type binding  = RD.binding (* already good *)
(* Terms and universes are still *deep*, so we do not change their
representation, and the user needs to pack/inspect. *)
(*| Reflected terms, the abstract type `FStar.Stubs.Reflection.Types.term`.

    Terms keep their internal representation; use
    `FStar.Tactics.NamedView.inspect` and `FStar.Tactics.NamedView.pack` to
    convert from and to the named view. *)
type term     = R.term
(*| Reflected universes, the abstract type
    `FStar.Stubs.Reflection.Types.universe`; see
    `FStar.Tactics.NamedView.inspect_universe`. *)
type universe = R.universe

(*| A named binder: the binding occurrence of a variable in an abstraction,
    arrow, refinement or `let`, as seen in the named view.

    The fields are:

    - `uniq`, the unique number of the bound variable
    - `ppname`, its pretty-printing name
    - `sort`, its type
    - `qual`, its qualifier (explicit, implicit, equality or meta)
    - `attrs`, its attributes

    When `FStar.Tactics.NamedView.inspect` opens a binder it chooses a fresh
    `uniq`, and the body refers to the variable as `Tv_Var` with that number.
    Contrast with the locally nameless `FStar.Stubs.Reflection.Types.binder`,
    whose body refers to it by de Bruijn index. *)
[@@plugin]
noeq
type binder = {
  uniq   : nat;

  ppname : ppname_t;
  sort   : R.typ;
  qual   : aqualv;
  attrs  : list term;
}
(*| A list of named binders. *)
type binders = list binder

(*| Holds when a binder is explicit and has no attributes, as the binders of
    refinements and `let` must be. *)
let is_simple_binder (b:binder) = Q_Explicit? b.qual /\ Nil? b.attrs
(*| A binder that is explicit and has no attributes; see
    `FStar.Tactics.NamedView.is_simple_binder`. *)
type simple_binder = b:binder{is_simple_binder b}

(*| A universe variable name, opened to a string and the range where it occurs. *)
type univ_name = string & Range.range

(*| A view of the top-level structure of a universe, with universe names
    opened.

    It mirrors `FStar.Stubs.Reflection.V2.Data.universe_view`, but `Uv_Name`
    carries a `FStar.Tactics.NamedView.univ_name` instead of an identifier. The
    constructors are `Uv_Zero`, `Uv_Succ u`, `Uv_Max us`, `Uv_BVar n` (a bound
    universe variable), `Uv_Name n`, `Uv_Unif uv` (a unification variable) and
    `Uv_Unk` (unknown). Subuniverses stay abstract. *)
[@@plugin]
noeq
type named_universe_view =
  | Uv_Zero : named_universe_view
  | Uv_Succ : universe -> named_universe_view
  | Uv_Max  : universes -> named_universe_view
  | Uv_BVar : nat -> named_universe_view
  | Uv_Name : univ_name -> named_universe_view
  | Uv_Unif : R.universe_uvar -> named_universe_view
  | Uv_Unk  : named_universe_view

(*| Patterns of `match` branches in the named view, where pattern variables are
    named.

    The constructors are records:

    - `Pat_Constant { c }`, a constant
    - `Pat_Cons { head; univs; subpats }`, a fully applied constructor
    - `Pat_Var { v; sort }`, a pattern-bound named variable and its sealed sort
    - `Pat_Dot_Term { t }`, a dot pattern, determined by the rest of the match

    In `Pat_Cons`, the boolean paired with each subpattern marks an implicit
    argument that was written explicitly. The body of a branch refers to the
    variables of `Pat_Var` by their unique numbers. *)
[@@plugin]
noeq
type pattern =
 // A built-in constant
 | Pat_Constant {
     c : vconst
   }

 // A fully applied constructor, each boolean marks whether the
 // argument was an explicitly-provided implicit argument
 | Pat_Cons {
     head    : fv;
     univs   : option universes;
     subpats : list (pattern & bool)
   }

 // A pattern-bound *named* variable.
 | Pat_Var {
     v    : namedv;
     sort : sealed typ;
   }

 // Dot pattern: resolved by other elements in the pattern and type
 | Pat_Dot_Term {
     t : option term;
   }

(*| A `match` branch in the named view: a pattern and the body, which refers to
    the pattern variables as named variables. *)
type branch = pattern & term
(*| The return annotation of a `match` in the named view.

    It is a named binder for the scrutinee, then either a type (`Inl`) or a
    computation type (`Inr`), an optional tactic to solve it, and a boolean that
    is `true` for a `returns$` annotation, checked with type equality. *)
type match_returns_ascription = binder & (either term comp & option term & bool)

(*| A view of the top-level structure of a term in which binders are opened
    into named variables.

    It mirrors `FStar.Stubs.Reflection.V2.Data.term_view` constructor by
    constructor, but binders are `FStar.Tactics.NamedView.binder` records, and
    the bodies of `Tv_Abs`, `Tv_Arrow`, `Tv_Refine`, `Tv_Let` and match
    branches refer to the bound variable with `Tv_Var`, not with a de Bruijn
    index. The constructors are:

    - `Tv_Var v`, a named variable, and `Tv_BVar v`, a bound variable
    - `Tv_FVar v` and `Tv_UInst v us`, top-level names, without and with universes
    - `Tv_App hd a`, an application of `hd` to one argument with its qualifier
    - `Tv_Abs b body` and `Tv_Arrow b c`, abstractions and arrows
    - `Tv_Type u`, a universe of types
    - `Tv_Refine b ref`, a refinement over a simple binder
    - `Tv_Const c`, a constant
    - `Tv_Uvar n ctx`, a unification variable
    - `Tv_Let recf attrs b def body`, a possibly recursive `let`
    - `Tv_Match scrutinee ret brs`, a match with an optional return annotation
    - `Tv_AscribedT e t tac use_eq` and `Tv_AscribedC e c tac use_eq`, ascriptions
    - `Tv_Unknown`, the unknown term written `_`
    - `Tv_Unsupp`, syntax that reflection does not support

    Use `FStar.Tactics.NamedView.inspect` and `FStar.Tactics.NamedView.pack` to
    convert. Opening `FStar.Tactics.V2` brings these constructors into scope,
    shadowing those of `FStar.Stubs.Reflection.V2.Data`. *)
[@@plugin]
noeq
type named_term_view =
  | Tv_Var    : v:namedv -> named_term_view
  | Tv_BVar   : v:bv -> named_term_view
  | Tv_FVar   : v:fv -> named_term_view
  | Tv_UInst  : v:fv -> us:universes -> named_term_view
  | Tv_App    : hd:term -> a:argv -> named_term_view
  | Tv_Abs    : b:binder -> body:term -> named_term_view
  | Tv_Arrow  : b:binder -> c:comp -> named_term_view
  | Tv_Type   : universe -> named_term_view
  | Tv_Refine : b:simple_binder -> ref:term -> named_term_view
  | Tv_Const  : vconst -> named_term_view
  | Tv_Uvar   : nat -> ctx_uvar_and_subst -> named_term_view
  | Tv_Let    : recf:bool -> attrs:(list term) -> b:simple_binder -> def:term -> body:term -> named_term_view
  | Tv_Match  : scrutinee:term -> ret:option match_returns_ascription -> brs:(list branch) -> named_term_view
  | Tv_AscribedT : e:term -> t:term -> tac:option term -> use_eq:bool -> named_term_view
  | Tv_AscribedC : e:term -> c:comp -> tac:option term -> use_eq:bool -> named_term_view
  | Tv_Unknown  : named_term_view // An underscore: _
  | Tv_Unsupp : named_term_view // failed to inspect, not supported

(* Relating constructors between old and new view. Both flavors of
functions usually behave the same wrt the top-level constructor
of the terms involved. *)
(*| Holds when a named view and a locally nameless view have the same top-level
    constructor.

    `FStar.Tactics.NamedView.pack_ctor_matches` proves it for
    `FStar.Tactics.NamedView.pack`. *)
let ctor_matches (v1:named_term_view) (v2:RD.term_view) : prop =
  match v1, v2 with
  | Tv_Var _             , RD.Tv_Var _             -> True
  | Tv_BVar _            , RD.Tv_BVar _            -> True
  | Tv_FVar _            , RD.Tv_FVar _            -> True
  | Tv_UInst _ _         , RD.Tv_UInst _ _         -> True
  | Tv_App _ _           , RD.Tv_App _ _           -> True
  | Tv_Abs _ _           , RD.Tv_Abs _ _           -> True
  | Tv_Arrow _ _         , RD.Tv_Arrow _ _         -> True
  | Tv_Type _            , RD.Tv_Type _            -> True
  | Tv_Refine _ _        , RD.Tv_Refine _ _        -> True
  | Tv_Const _           , RD.Tv_Const _           -> True
  | Tv_Uvar _ _          , RD.Tv_Uvar _ _          -> True
  | Tv_Let _ _ _ _ _     , RD.Tv_Let _ _ _ _ _     -> True
  | Tv_Match _ _ _       , RD.Tv_Match _ _ _       -> True
  | Tv_AscribedT _ _ _ _ , RD.Tv_AscribedT _ _ _ _ -> True
  | Tv_AscribedC _ _ _ _ , RD.Tv_AscribedC _ _ _ _ -> True
  | Tv_Unknown           , RD.Tv_Unknown           -> True
  | Tv_Unsupp            , RD.Tv_Unsupp            -> True
  | _ -> False

// Repeat from FStar.R.Data
(*| Tests whether a named view is neither `Tv_AscribedT` nor `Tv_AscribedC`.

    Counterpart of `FStar.Stubs.Reflection.V2.Data.notAscription`; see
    `FStar.Tactics.V2.SyntaxHelpers.inspect_unascribe`. *)
let notAscription (tv:named_term_view) : bool =
  not (Tv_AscribedT? tv) && not (Tv_AscribedC? tv)

(*| A top-level let binding in the named view.

    The fields are `lb_fv`, the name being defined; `lb_us`, its universe
    variables, opened; `lb_typ`, its type; and `lb_def`, its definition. *)
[@@plugin]
noeq
type letbinding = {
  lb_fv : fv;
  lb_us : list univ_name; (* opened *)
  lb_typ : typ;
  lb_def : term;
}

(*| A view of a top-level declaration in which universe variables and
    parameters are opened.

    The constructors are records:

    - `Sg_Let { isrec; lbs }`, a possibly recursive group of let bindings
    - `Sg_Inductive { nm; univs; params; typ; ctors }`, an inductive type
    - `Sg_Val { nm; univs; typ }`, a `val` declaration
    - `Unk`, any other declaration

    For `Sg_Inductive`, `params` are the opened parameters, `typ` is the type
    of the inductive after them (indices to a universe), and `ctors` are the
    constructors, whose types no longer abstract over the parameters but refer
    to the opened ones. Mutually inductive types are not supported. Use
    `FStar.Tactics.NamedView.inspect_sigelt` and
    `FStar.Tactics.NamedView.pack_sigelt` to convert. *)
[@@plugin]
noeq
type named_sigelt_view =
  | Sg_Let {
      isrec : bool;
      lbs   : list letbinding;
    }

  // Sg_Inductive basically coalesces the Sig_bundle used internally,
  // where the type definition and its constructors are split.
  // While that might be better for typechecking, this is probably better for metaprogrammers
  // (no mutually defined types for now)
  | Sg_Inductive {
      nm     : name;             // name of the inductive type being defined
      univs  : list univ_name;   // named universe variables
      params : binders;          // parameters
      typ    : typ;              // the type annotation for the inductive, i.e., indices -> Type #u
      ctors  : list ctor;        // the constructors, opened with univs and applied to params already
    }

  | Sg_Val {
      nm    : name;
      univs : list univ_name;
      typ   : typ;
    }

  | Unk

(* Some helpers. The latter two are not marked coercions as they make a
choice to not add qualifiers/attrs, so we let the user call them. *)
(*| Converts a named binder to a binding, dropping its qualifier and
    attributes.

    Declared as a coercion, so a binder can be used where a binding is
    expected. *)
[@@coercion]
let binder_to_binding (b : binder) : binding =
  {
      ppname = b.ppname;
      uniq   = b.uniq;
      sort   = b.sort;
  }
(*| Converts a binding to an explicit named binder with no attributes.

    Not a coercion, since it chooses the qualifier and attributes. See
    `FStar.Tactics.NamedView.binder_to_binding` for the other direction. *)
let binding_to_binder (bnd : binding) : binder =
  {
      ppname = bnd.ppname;
      uniq   = bnd.uniq;
      sort   = bnd.sort;
      qual   = Q_Explicit;
      attrs  = []
  }
(*| Builds an explicit named binder with no attributes for a named variable,
    with the given sort.

    The sort is passed separately because the sort of a named variable is
    sealed. *)
let namedv_to_binder (v : namedv) (sort : term) : binder =
  {
    uniq   = v.uniq;
    sort   = sort;
    ppname = v.ppname;
    qual   = Q_Explicit;
    attrs  = [];
  }

(*| Inspects the top-level structure of a universe, with universe names opened.

    The universe is compressed first, so solved universe unification variables
    show their solutions. Declared as a coercion. The inverse of
    `FStar.Tactics.NamedView.pack_universe`. *)
[@@plugin; coercion]
val inspect_universe (u:universe) : Tac named_universe_view

(*| Builds a universe from its named view; the inverse of
    `FStar.Tactics.NamedView.inspect_universe`.

    Total, and declared as a coercion. *)
[@@plugin; coercion]
val pack_universe (uv:named_universe_view) : Tot universe

(*| Abstracts the named variable of a binder in a term, giving the locally
    nameless binder and the term with the variable replaced by de Bruijn
    index 0.

    The inverse of the opening done by `FStar.Tactics.NamedView.inspect`, for
    building locally nameless syntax with `FStar.Stubs.Reflection.V2.Builtins`
    from named binders. *)
[@@plugin]
val close_term (b:binder) (t:term) : Tot (R.binder & term)

(*| Inspects the top-level structure of a term, opening its binders into fresh
    named variables.

    The term is compressed first, so a solved unification variable shows its
    solution. If the term binds a variable (an abstraction, arrow, refinement,
    `let`, or match branch), the binder gets a fresh unique number and the body
    refers to it with `Tv_Var`. Because of the compression, the result need not
    have the same constructor as the term's locally nameless view. Declared as
    a coercion. The inverse of `FStar.Tactics.NamedView.pack`; for the locally
    nameless view use `FStar.Stubs.Reflection.V2.Builtins.inspect_ln`.

    ```fstar
    let _ = assert True by (
      match inspect (`(fun (x:int) -> x)) with
      | Tv_Abs b body -> guard (Tv_Var? (inspect body))
      | _ -> fail "expected an abstraction")
    ``` *)
[@@plugin; coercion]
val inspect (t:term) : Tac named_term_view

(*| Builds a term from its named view, closing named binders back into de
    Bruijn indices.

    Total, and declared as a coercion. The result has the same top-level
    constructor as the view, by `FStar.Tactics.NamedView.pack_ctor_matches`.
    The inverse of `FStar.Tactics.NamedView.inspect`. *)
[@@plugin; coercion]
val pack (tv:named_term_view) : Tot term

(*| `FStar.Tactics.NamedView.pack` preserves the top-level constructor: the
    locally nameless view of `pack tv` has the constructor of `tv`.

    Triggered automatically on `pack tv`. There is no such guarantee for
    `FStar.Tactics.NamedView.inspect`. *)
val pack_ctor_matches (tv:named_term_view)
  : Lemma (ctor_matches tv (RB.inspect_ln (pack tv)))
          [SMTPat (pack tv)]

(*| Inspects a top-level declaration, opening its universe variables and, for
    an inductive type, its parameters.

    Unsupported declarations give `Unk`. Declared as a coercion. The inverse of
    `FStar.Tactics.NamedView.pack_sigelt`. *)
[@@plugin; coercion]
val inspect_sigelt (s : sigelt) : Tac named_sigelt_view

(*| Builds a top-level declaration from its named view, closing universe
    variables and parameters.

    The view must not be `Unk`. Declared as a coercion. The inverse of
    `FStar.Tactics.NamedView.inspect_sigelt`. *)
[@@plugin; coercion]
val pack_sigelt (sv:named_sigelt_view{~(Unk? sv)}) : Tac sigelt

(* Some primitives mention `R.comp`, wrap them to use `ThisModule.comp = R.comp_view` *)
(*| Typechecks a term in an environment and returns its computation type as a
    named view.

    Wraps `FStar.Stubs.Tactics.V2.Builtins.tcc`, and fails the tactic if the
    term does not typecheck. *)
[@@plugin]
val tcc (e:env) (t:term) : Tac comp
(*| Prints a computation type, given as a named view, with the F\* pretty
    printer.

    Wraps `FStar.Stubs.Tactics.V2.Builtins.comp_to_string`. *)
[@@plugin]
val comp_to_string (c:comp) : Tac string

(* Clients of this module use the named view. *)
(*| The named universe view, so that `universe_view` means
    `FStar.Tactics.NamedView.named_universe_view` for clients of this module. *)
let universe_view = named_universe_view
(*| The named term view, so that `term_view` means
    `FStar.Tactics.NamedView.named_term_view` for clients of this module. *)
let term_view     = named_term_view
(*| The named declaration view, so that `sigelt_view` means
    `FStar.Tactics.NamedView.named_sigelt_view` for clients of this module. *)
let sigelt_view   = named_sigelt_view

(* Temporary adapters, to avoid breaking existing code too much. *)
(*| The identity on `FStar.Tactics.NamedView.namedv`, kept as a temporary adapter
    for code written against the inspection functions of
    `FStar.Stubs.Reflection.V2.Builtins`.

    In the named view a `namedv` is already its own view, so there is nothing to
    inspect. *)
let inspect_namedv   = id #namedv
(*| The identity on `FStar.Tactics.NamedView.namedv`, kept as a temporary adapter
    for code written against the packing functions of
    `FStar.Stubs.Reflection.V2.Builtins`.

    In the named view a `namedv` is already its own view, so there is nothing to
    pack. *)
let pack_namedv      = id #namedv
(*| The identity on `FStar.Tactics.NamedView.bv`, kept as a temporary adapter
    for code written against the inspection functions of
    `FStar.Stubs.Reflection.V2.Builtins`.

    In the named view a `bv` is already its own view, so there is nothing to
    inspect. *)
let inspect_bv       = id #bv
(*| The identity on `FStar.Tactics.NamedView.bv`, kept as a temporary adapter
    for code written against the packing functions of
    `FStar.Stubs.Reflection.V2.Builtins`.

    In the named view a `bv` is already its own view, so there is nothing to
    pack. *)
let pack_bv          = id #bv
(*| The identity on `FStar.Tactics.NamedView.comp`, kept as a temporary adapter
    for code written against the inspection functions of
    `FStar.Stubs.Reflection.V2.Builtins`.

    In the named view a `comp` is already its own view, so there is nothing to
    inspect. *)
let inspect_comp     = id #comp
(*| The identity on `FStar.Tactics.NamedView.comp`, kept as a temporary adapter
    for code written against the packing functions of
    `FStar.Stubs.Reflection.V2.Builtins`.

    In the named view a `comp` is already its own view, so there is nothing to
    pack. *)
let pack_comp        = id #comp

(*| Returns the name of the top-level constructor of the named view of a term,
    such as `"Tv_App"`, for debugging. *)
[@@plugin]
val tag_of (t:term) : Tac string
