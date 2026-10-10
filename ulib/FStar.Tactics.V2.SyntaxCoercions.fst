module FStar.Tactics.V2.SyntaxCoercions

open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.NamedView
open FStar.Sealed

(*| The term `Tv_Var x` for a named variable.

    Declared as a coercion, so a named variable can be used where a term is
    expected. *)
[@@coercion]
let namedv_to_term (x : namedv) : Tot term =
  pack (Tv_Var x)

(*| The named variable bound by a named binder, keeping its unique number,
    sort (sealed) and pretty-printing name.

    Declared as a coercion. *)
[@@coercion]
let binder_to_namedv (b : binder) : Tot namedv =
  {
    ppname = b.ppname;
    uniq   = b.uniq;
    sort   = seal b.sort;
  }

(*| The term for the variable bound by a named binder, as `Tv_Var`.

    Declared as a coercion, so a binder obtained by
    `FStar.Tactics.NamedView.inspect` can be used directly as a term. *)
[@@coercion]
let binder_to_term (b : binder) : Tot term =
  pack (Tv_Var (binder_to_namedv b))

(*| The named variable of a binding, keeping its unique number, sort (sealed)
    and pretty-printing name.

    Declared as a coercion. *)
[@@coercion]
let binding_to_namedv (b : binding) : Tot namedv =
  {
    ppname = b.ppname;
    sort   = seal b.sort;
    uniq   = b.uniq
  }

(*| The term for the variable of a binding, as `Tv_Var`.

    Declared as a coercion, so the result of introduction tactics such as
    `FStar.Stubs.Tactics.V2.Builtins.intro` can be used directly as a term. *)
[@@coercion]
let binding_to_term (x : binding) : Tot term =
  namedv_to_term (binding_to_namedv x)
