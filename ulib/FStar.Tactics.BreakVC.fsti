module FStar.Tactics.BreakVC

open FStar.Tactics

(* See FStar.Pure.BreakVC: VC-breaking cannot be expressed with pre- and
   postconditions alone, so this is a no-op kept for source compatibility. *)
(*| Tactic that does nothing; kept only for source compatibility.

    It previously split the verification condition of its continuation
    into a separate query. See `FStar.Pure.BreakVC.break_vc`, which is also a
    no-op now. *)
val break_vc (_:unit) : Tac unit
