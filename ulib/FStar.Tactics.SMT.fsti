module FStar.Tactics.SMT

open FStar.Tactics.Effect

(* Alias to just use the current vconfig *)
(*| Tries to solve the current goal with the SMT solver right away, using the goal's current `vconfig`; fails if SMT cannot prove it.

    This calls `FStar.Stubs.Tactics.V2.Builtins.t_smt_sync` with the result of `FStar.Stubs.Tactics.V2.Builtins.get_vconfig`. Unlike `FStar.Tactics.V2.Derived.smt`, which only defers the goal to SMT at the end of the tactic run, the goal is discharged (or the tactic fails) immediately. See also `FStar.Tactics.SMT.smt_sync'`. *)
[@@plugin]
val smt_sync () : Tac unit

(* smt_sync': as smt_sync, but using a particular fuel/ifuel *)
(*| Like `FStar.Tactics.SMT.smt_sync`, but runs the SMT query with both initial and maximum fuel set to `fuel` and both initial and maximum ifuel set to `ifuel`.

    The other settings come from the current goal's `vconfig`; the goal's stored configuration itself is not changed. *)
[@@plugin]
val smt_sync' (fuel ifuel : nat) : Tac unit

(* Getting/setting solver configuration *)

(*| Returns the `z3rlimit` of the current goal's `vconfig`.

    See `FStar.Tactics.SMT.set_rlimit`. *)
[@@plugin]
val get_rlimit () :               Tac int 
(*| Sets the `z3rlimit` in the current goal's `vconfig`, which is used when that goal is later sent to SMT.

    Implemented with `FStar.Stubs.Tactics.V2.Builtins.set_vconfig`; the other settings are unchanged. *)
[@@plugin]
val set_rlimit (v : int) :        Tac unit

(*| Returns the `initial_fuel` of the current goal's `vconfig`. *)
[@@plugin]
val get_initial_fuel  () :        Tac int 
(*| Returns the `initial_ifuel` of the current goal's `vconfig`. *)
[@@plugin]
val get_initial_ifuel () :        Tac int 
(*| Returns the `max_fuel` of the current goal's `vconfig`. *)
[@@plugin]
val get_max_fuel  () :            Tac int 
(*| Returns the `max_ifuel` of the current goal's `vconfig`. *)
[@@plugin]
val get_max_ifuel () :            Tac int 

(*| Sets the `initial_fuel` in the current goal's `vconfig`, leaving the other settings unchanged.

    See `FStar.Tactics.SMT.set_fuel` to set initial and maximum fuel together. *)
[@@plugin]
val set_initial_fuel  (v : int) : Tac unit
(*| Sets the `initial_ifuel` in the current goal's `vconfig`, leaving the other settings unchanged.

    See `FStar.Tactics.SMT.set_ifuel` to set initial and maximum ifuel together. *)
[@@plugin]
val set_initial_ifuel (v : int) : Tac unit
(*| Sets the `max_fuel` in the current goal's `vconfig`, leaving the other settings unchanged. *)
[@@plugin]
val set_max_fuel  (v : int) :     Tac unit
(*| Sets the `max_ifuel` in the current goal's `vconfig`, leaving the other settings unchanged. *)
[@@plugin]
val set_max_ifuel (v : int) :     Tac unit

(* Set both min and max *)
(*| Sets both `initial_fuel` and `max_fuel` of the current goal's `vconfig` to `v`.

    The effect is like `--fuel v` for the SMT query of this goal. *)
[@@plugin]
val set_fuel  (v : int) :         Tac unit
(*| Sets both `initial_ifuel` and `max_ifuel` of the current goal's `vconfig` to `v`.

    The effect is like `--ifuel v` for the SMT query of this goal. *)
[@@plugin]
val set_ifuel (v : int) :         Tac unit
