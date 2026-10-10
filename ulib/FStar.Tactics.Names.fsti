module FStar.Tactics.Names

open FStar.Stubs.Reflection.Types
open FStar.Tactics.Effect

(*| Decides whether the top-level name `nm` syntactically appears in the term `t`.

    It visits `t` with `FStar.Tactics.Visit.visit_tm` and looks for a free
    variable (`Tv_FVar`) whose name is `nm`. Names that only appear after
    unfolding definitions are not found. *)
[@@plugin]
val name_appears_in (nm:name) (t:term) : Tac bool
