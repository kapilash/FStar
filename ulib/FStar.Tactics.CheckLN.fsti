module FStar.Tactics.CheckLN

open FStar.Tactics.V2.Bare

(* Checks if a term is locally nameless. *)
(*| Checks whether a term is locally nameless, i.e. has no loose de Bruijn indices (bound variables escaping their binder).

    The check is conservative: it returns `false` on unification variables
    (of terms or universes) and on universe variables bound by index. Some subterms
    are not checked: the patterns and return annotation of a `match`, and the
    type annotation of a `let` binder. *)
[@@plugin]
val check_ln (t:term) : Tac bool
