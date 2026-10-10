module FStar.Tactics.Print

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Tactics.Effect
open FStar.Tactics.NamedView

(*| Prints a named variable as its pretty-printing name followed by `#` and its unique number, for instance `x#42`. *)
[@@plugin]
val namedv_to_string (x:Stubs.Reflection.Types.namedv) : Tac string

(*| Prints the abstract syntax of a universe, using the constructor names of `FStar.Stubs.Reflection.V2.Data.universe_view`, for instance `Uv_Succ(Uv_Zero)`.

    Unification variables are printed as `Uv_Unif`, without their identity. *)
[@@plugin]
val universe_to_ast_string (u:universe) : Tac string

(*| Prints a list of universes with `FStar.Tactics.Print.universe_to_ast_string`, between brackets and separated by semicolons. *)
[@@plugin]
val universes_to_ast_string (us:universes) : Tac string

(*| Prints the abstract syntax of a term, using the constructor names of its named view `FStar.Tactics.NamedView.named_term_view` (`Tv_App`, `Tv_Abs`, `Tv_Const` and so on), which helps to see how a term is represented.

    Compare `FStar.Stubs.Tactics.V2.Builtins.term_to_string`, which prints concrete syntax. The output is meant for debugging and is not complete: patterns of match branches are printed as `_pat`, unknown terms as `_` and unsupported ones as `<Tv_Unsupp>`, and only the effect name and result type of computation types are shown.

    ```fstar
    let _ = assert True by (guard (term_to_ast_string (`1) = "C_Int 1"); trivial ())
    ``` *)
[@@plugin]
val term_to_ast_string (t:term) : Tac string

(*| Prints the optional `returns` annotation of a match: its binder, then its type or computation type in abstract syntax, followed by `by` and the tactic if there is one.

    Prints the empty string when there is no annotation. *)
[@@plugin]
val match_returns_to_string (ret_opt:option match_returns_ascription) : Tac string

(*| Prints a list of match branches with `FStar.Tactics.Print.branch_to_ast_string`, between brackets and separated by semicolons. *)
[@@plugin]
val branches_to_ast_string (brs:list branch) : Tac string

(*| Prints a match branch as a pair of `_pat`, standing for its pattern (which is not printed), and its body in abstract syntax. *)
[@@plugin]
val branch_to_ast_string (b:branch) : Tac string

(*| Prints a computation type as `Effect` followed by its effect name and its result type in abstract syntax.

    The effect arguments and decreases clauses are not printed. *)
[@@plugin]
val comp_to_ast_string (c:comp) : Tac string

(*| Prints a constant using the constructor names of `FStar.Stubs.Reflection.V2.Data.vconst`, for instance `C_Int 1` or `C_String s`.

    Machine integers show their signedness and width, and ranges are printed as `C_Range _`. *)
[@@plugin]
val const_to_ast_string (c:vconst) : Tac string
