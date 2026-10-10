module FStar.Stubs.Syntax.Syntax
open FStar.Stubs.Reflection.Types

(*| An element of a substitution on reflected terms, mirroring the compiler's internal representation.

    The constructors pair de Bruijn indices, named variables, terms and universes:

    - `DB i x`: replace the bound variable with index `i` by the name `x`
    - `DT i t`: replace the bound variable with index `i` by the term `t`
    - `NM x i`: replace the name `x` by the bound variable with index `i`
    - `NT x t`: replace the name `x` by the term `t`
    - `UN i u`: replace the universe variable with index `i` by the universe `u`
    - `UD n i`: replace the universe name `n` by the universe variable with index `i`

    Equality is not decidable (the type is `noeq`). Used by `FStar.Stubs.Reflection.V2.Builtins.subst_term`. *)
noeq
type subst_elt =
  | DB : int -> namedv -> subst_elt
  | DT : int -> term -> subst_elt
  | NM : namedv -> int -> subst_elt
  | NT : namedv -> term -> subst_elt
  | UN : int -> universe -> subst_elt
  | UD : ident -> int -> subst_elt
(*| A substitution: a list of `FStar.Stubs.Syntax.Syntax.subst_elt` applied together. *)
type subst_t = list subst_elt


(*| The `as x returns t` annotation of a reflected `match`: a binder for the scrutinee, then either a type or a computation type, an optional tactic to prove it with, and a boolean.

    The boolean is false for `returns` and true for `returns$`, which uses type equality instead of subtyping. *)
type match_returns_ascription = binder & (either term comp & option term & bool)
