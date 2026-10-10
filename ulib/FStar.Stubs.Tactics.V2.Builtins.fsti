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
(**
Every tactic primitive, i.e., those built into the compiler
@summary Tactic primitives
*)
module FStar.Stubs.Tactics.V2.Builtins

open FStar.VConfig
open FStar.Stubs.Reflection.Types
open FStar.Reflection.Const
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.Types
open FStar.Stubs.Tactics.Types.Reflection
open FStar.Reflection.TermSpec
include FStar.Stubs.Tactics.Unseal

(*| Returns the current proof state, a snapshot of the goals and the rest of the tactic engine state.

    The goals can be read with `FStar.Stubs.Tactics.Types.goals_of` and `FStar.Stubs.Tactics.Types.smt_goals_of`; `FStar.Tactics.V2.Derived.goals` and `FStar.Tactics.V2.Derived.smt_goals` do exactly that. Implemented by the compiler. *)
val get ()
  : Tac proofstate

(*| Adjusts a source range before it is used to report an error, as the compiler does for its own error ranges.

    Implemented by the compiler (it calls the error module's range bounding function); the exact adjustment is internal and not specified here. Does not change the proof state. *)
val fixup_range : Range.range -> TacRO Range.range

(*| Resolves the unification variable indirections at the top of a term, so that its head shows the current solution of any solved uvar.

    Only the top of the term is compressed, not its subterms. See `FStar.Stubs.Tactics.V2.Builtins.compress_univ` for universes. Implemented by the compiler. *)
val compress : term -> TacRO term

(*| Resolves the unification variable indirections at the top of a universe.

    The universe analogue of `FStar.Stubs.Tactics.V2.Builtins.compress`. Implemented by the compiler. *)
val compress_univ : universe -> TacRO universe

(*| Returns the environment in which the tactic started running.

    This works even when there are no goals left, unlike `FStar.Tactics.V2.Derived.cur_env`, which returns the environment of the current goal. *)
val top_env : unit -> TacRO env

(*| Returns a fresh natural number, obtained by incrementing an internal counter.

    The counter is not reset when a failure is caught by `FStar.Stubs.Tactics.V2.Builtins.catch`, so numbers are not reused after backtracking. *)
val fresh : unit -> Tac nat

(*| Splits a goal whose type is a refinement `x:t{phi}` into a goal of type `t` and a goal for `phi` with `x` replaced by the witness of the first goal.

    Acts on the current goal and replaces it by the two new goals. *)
val refine_intro : unit -> Tac unit

(*| Returns the type of a term in the given environment, failing the tactic if the term does not typecheck.

    See `FStar.Stubs.Tactics.V2.Builtins.tcc` for the full computation type, and `FStar.Stubs.Tactics.V2.Builtins.core_compute_term_type` for the core typechecker variant that returns a typing token. *)
val tc : env -> term -> Tac term

(*| Like `FStar.Stubs.Tactics.V2.Builtins.tc`, but returns the full computation type of the term, including its effect label and effect arguments (such as WPs).

    Fails the tactic if the term does not typecheck. *)
val tcc : env -> term -> Tac comp

(*| Turns a unification variable into a goal, so that it can be solved explicitly.

    Use it when the engine did not present a goal for a uvar but you want one, for instance for a uvar created with `FStar.Stubs.Tactics.V2.Builtins.uvar_env` or `FStar.Tactics.V2.Derived.fresh_uvar`. The new goal is added to the goals. Fails with "not a uvar" if the head of the term is not a unification variable. *)
val unshelve : term -> Tac unit

(*| Turns a quoted term into an actual value of type `a`, the inverse of quotation.

    The term is typechecked at type `a` in the environment of the current goal, so a goal must be present; the tactic fails at run time if the term does not typecheck at that type. *)
val unquote : #a:Type -> term -> Tac a

(*| Runs a tactic and recovers from its failure, returning `Inr x` if it succeeds with `x` and `Inl e` if it raises the exception `e`.

    On failure, all unification (union-find) effects of the failed tactic are reverted. The counter of `FStar.Stubs.Tactics.V2.Builtins.fresh` and the references of `FStar.Stubs.Tactics.V2.Builtins.alloc` are not reverted. See `FStar.Tactics.V2.Derived.try_with`, `FStar.Tactics.V2.Derived.trytac` and `FStar.Tactics.V2.Derived.or_else` for more convenient wrappers.

    ```fstar
    let recover () : Tac unit =
      match catch (fun () -> fail "boom") with
      | Inl _ -> trivial ()
      | Inr () -> trivial ()
    ``` *)
val catch : #a:Type -> (unit -> Tac a) -> TacS (either exn a)

(*| Raises an exception, aborting the tactic unless the exception is caught by `FStar.Stubs.Tactics.V2.Builtins.catch`.

    The primitive returns `unit`; `FStar.Stubs.Tactics.V2.Builtins.raise` is the polymorphic version that most code uses. Its postcondition `False` records that it never returns. *)
val raise_core (e:exn) : TacH unit (requires True) (ensures fun _ -> False)
(*| Raises an exception at any result type, aborting the tactic unless it is caught by `FStar.Stubs.Tactics.V2.Builtins.catch`.

    Defined from `FStar.Stubs.Tactics.V2.Builtins.raise_core`. To fail with a message, use `FStar.Tactics.V2.Derived.fail`, which raises a `TacticFailure`. *)
inline_for_extraction
let raise #a (e:exn) : TacH a (requires True) (ensures fun _ -> False) =
    raise_core e; magic ()

(*| Normalizes the type and the witness of the current goal using the given reduction steps.

    The steps are values of `FStar.NormSteps.norm_step`, for example:

    - `simplify`: logical simplifications
    - `weak`: do not reduce under binders
    - `hnf`: reduce only to head normal form
    - `primops`: primitive reductions such as arithmetic and string operations
    - `delta`: unfold names
    - `zeta`: unroll recursive definitions, with heuristics to avoid loops
    - `zeta_full`: unroll recursive definitions fully
    - `iota`: reduce matches on constructors
    - `delta_only`: unfold only the listed fully qualified names

    See `FStar.Stubs.Tactics.V2.Builtins.norm_term_env` to normalize an arbitrary term.

    ```fstar
    let _ = assert (1 + 1 == 2) by (norm [primops]; trefl ())
    ``` *)
val norm  : list norm_step -> Tac unit

(*| Normalizes a term in the given environment, using the given reduction steps.

    The steps have the same meaning as for `FStar.Stubs.Tactics.V2.Builtins.norm`. The proof state is not changed. `FStar.Tactics.V2.Derived.norm_term` uses the environment of the current goal. See also `FStar.Stubs.Tactics.V2.Builtins.norm_well_typed_term`, which returns an equivalence token. *)
val norm_term_env  : env -> list norm_step -> term -> Tac term

(*| Normalizes the type of a binding in the context of the current goal, using the given reduction steps.

    This cannot be done with `FStar.Stubs.Tactics.V2.Builtins.var_retype` followed by `FStar.Stubs.Tactics.V2.Builtins.norm`, because uvars may be resolved to lambda-abstractions. *)
val norm_binding_type  : list norm_step -> binding -> Tac unit

(*| Introduces the first argument of an arrow goal, turning `Gamma |- ?u : x:a -> b` into `Gamma, x:a |- ?u' : b`, and returns the new binding.

    Fails if the goal is not an arrow. It does not introduce logical implications or universal quantifiers stated as propositions; use `FStar.Tactics.V2.Logic.implies_intro` and `FStar.Tactics.V2.Logic.forall_intro` for those. See `FStar.Stubs.Tactics.V2.Builtins.intros` for several binders at once.

    ```fstar
    let id_int : int -> int = _ by (let x = intro () in exact (binding_to_term x))
    ``` *)
val intro : unit -> Tac binding

(*| Introduces several binders of an arrow goal at once, returning the new bindings.

    The goal must be a literal arrow: it is neither normalized nor unfolded. This can be faster than calling `FStar.Stubs.Tactics.V2.Builtins.intro` repeatedly, and it solves the witness with a single flat abstraction instead of many nested ones. The argument `max` bounds the number of binders introduced when `max >= 0`; use `-1` for no limit, as `FStar.Tactics.V2.Derived.intros` does. *)
val intros (max:int) : Tac (list binding)

(*| Like `FStar.Stubs.Tactics.V2.Builtins.intro`, but builds a recursive function, returning the binding for the function itself and the one for its argument.

    The original comment says this primitive is currently broken (see F\* issue 1103). *)
val intro_rec  : unit -> Tac (binding & binding)

(*| Renames a binding to the given name in the environment, goal and witness, and returns the new binding.

    The old binding no longer exists after the call. This only makes goals and terms more readable; it has no logical effect. *)
val rename_to  : binding -> string -> Tac binding

(*| Moves the last binder of the current goal's environment back into the goal type, the inverse of `FStar.Stubs.Tactics.V2.Builtins.intro`.

    Fails if the context is empty. *)
val revert  : unit -> Tac unit

(*| Changes the type of a variable in the context of the current goal.

    Given a binding of type `t`, it creates a goal `t == ?u` to be solved first, followed by the original goal in which the type of the binding is replaced by `?u`. *)
val var_retype  : binding -> Tac unit

(*| Removes the last binder from the environment of the current goal.

    Fails if the context is empty; the goal must not depend on the removed binder. See `FStar.Stubs.Tactics.V2.Builtins.clear`. *)
val clear_top : unit -> Tac unit

(*| Removes the given binding from the context of the current goal, provided nothing depends on it. *)
val clear : binding -> Tac unit

(*| Given a binding of type `v == r` where `v` is a variable, replaces `v` by `r` everywhere in the current goal's type and witness.

    See `FStar.Stubs.Tactics.V2.Builtins.grewrite` to rewrite an arbitrary term, and `FStar.Tactics.V2.Derived.rewrite_eqs_from_context`. *)
val rewrite : binding -> Tac unit

(*| Rewrites every occurrence of `t1` in the current goal into `t2`, and adds a goal `t1 == t2` after the current one. *)
val grewrite (t1 t2 : term) : Tac unit

(*| Solves the current goal with the given term; the low-level primitive behind `FStar.Tactics.V2.Derived.exact`.

    The first boolean says whether to try introducing a refinement before solving, in which case a goal for the refinement formula is added. The second says whether to set the expected type internally while typechecking the term. Prefer the wrappers: `FStar.Tactics.V2.Derived.exact` uses `t_exact true false`, `FStar.Tactics.V2.Derived.exact_with_ref` uses `t_exact true true`, and `FStar.Tactics.V2.Derived.exact_guard` is like `exact` but turns guards into goals.

    ```fstar
    let forty_two : int = _ by (exact (`42))
    ``` *)
val t_exact : maybe_refine:bool -> set_expected_typ:bool -> term -> Tac unit

(*| Solves the current goal by applying a function, creating goals for its arguments; the low-level primitive behind `FStar.Tactics.V2.Derived.apply`.

    The three booleans are:

    - `uopt`: do not ask for implicits that appear free in later goals
    - `noinst`: forbid instantiating uvars of the goal
    - `tc_resolved_uvars`: typecheck the uvars resolved by unification now

    When `uopt` is true, applying transitivity to `a = c` gives the two goals `a = ?u` and `?u = c` without asking to instantiate `?u`, since it will likely be constrained by solving them; the engine still fails if `?u` is never solved. When `noinst` is true, applying a function returning `1 = 2` to a goal `1 = ?u` fails, because it would instantiate `?u`; typeclass resolution uses this. When `tc_resolved_uvars` is false, the resolved uvars are typechecked at the end by the tactic engine.

    `FStar.Tactics.V2.Derived.apply` is `t_apply true false false`, `FStar.Tactics.V2.Derived.apply_noinst` is `t_apply true true false`, and `FStar.Tactics.V2.Derived.apply_raw` is `t_apply false false false`. *)
val t_apply : uopt:bool -> noinst:bool -> tc_resolved_uvars:bool -> term -> Tac unit

(*| Solves a goal `squash phi` by applying a lemma `l` that ensures `phi`, adding goals for the arguments of `l` and its precondition.

    As a small optimization, `unit` arguments are discharged by the engine. The `noinst` flag forbids instantiating uvars in the goal, as for `FStar.Stubs.Tactics.V2.Builtins.t_apply`. The `noinst_lhs` flag forbids instantiating uvars only on the left side of an equality goal, which is useful for rewriting goals of the shape `X = ?u`; it is ignored when `noinst` is set. `FStar.Tactics.V2.Derived.apply_lemma`, `FStar.Tactics.V2.Derived.apply_lemma_noinst` and `FStar.Tactics.V2.Derived.apply_lemma_rw` set these flags to `(false, false)`, `(true, false)` and `(false, true)`. *)
val t_apply_lemma : noinst:bool -> noinst_lhs:bool -> term -> Tac unit
// TODO: do the unit thing too for [apply].

(*| Prints a string on the compiler's standard output, without changing the proof state.

    See `FStar.Stubs.Tactics.V2.Builtins.dump` to print the proof state too, and `FStar.Tactics.V2.Derived.debug` to print only when debugging. *)
val print : string -> TacRO unit

(*| Returns true if tactic debugging is enabled for the current module, that is, when F\* runs with `--debug Tac`. *)
val debugging : unit -> TacRO bool

(*| Returns true if F\* is running in interactive (IDE) mode.

    Meant only for printing diagnostics in interactive mode but not in batch mode; tactics should not otherwise behave differently in the two modes. *)
val ide : unit -> TacRO bool

(*| Prints a message together with a text representation of the proof state (the goals and SMT goals).

    See `FStar.Stubs.Tactics.V2.Builtins.print` for a message alone, `FStar.Stubs.Tactics.V2.Builtins.dump_all` to also see every unsolved implicit, and `FStar.Tactics.V2.Derived.dump1` for the current goal only. *)
val dump : string -> TacRO unit

(*| Like `FStar.Stubs.Tactics.V2.Builtins.dump`, but prints every unsolved implicit of the proof state, not only the visible goals.

    When `print_resolved` is true it also prints every solved goal. The output can be very large. *)
val dump_all : print_resolved:bool -> string -> TacRO unit

(*| Prints a goal for every unresolved implicit (unification variable) in the given goal, preceded by the message. *)
val dump_uvars_of : goal -> string -> TacRO unit

(*| Solves a goal `squash (l == r)` by unifying `l` with `r`.

    It exists mainly because of universe problems when applying a reflexivity lemma. When `allow_guards` is true, some guards may be raised during unification and are added as a single goal to be discharged later; currently the only allowed guards come from equating refinement types such as `x:int{x>0}` and `x:int{0<x}`. Fails if the terms do not unify. `FStar.Tactics.V2.Derived.trefl` and `FStar.Tactics.V2.Derived.trefl_guard` call it with `false` and `true`. *)
val t_trefl : allow_guards:bool -> Tac unit

(*| Proves the equality between a match applied to arguments and the match whose branches are applied to these arguments, that is `(match e with p -> b) a1 .. an == (match e with p -> b a1 .. an)` for every branch.

    Useful to rewrite the left side to the right side when the right side is a unification variable. Wrapped by `FStar.Tactics.V2.Derived.commute_applied_match`. *)
val t_commute_applied_match : unit -> Tac unit

(*| Deprecated: turns the non-trivial typing guards of goals that are already solved into explicit goals, solving the trivial ones by simplification.

    Since the core typechecker was introduced (November 2022) this should not be needed; use the compat pre-core options or `FStar.Stubs.Tactics.V2.Builtins.with_compat_pre_core` if code breaks without it. See `tests/bug-reports/Bug2635.fst` for examples. *)
[@@deprecated "This will soon be removed, please use compat pre core settings if needed"]
val gather_or_solve_explicit_guards_for_resolved_goals : unit -> Tac unit

(*| Traverses the current goal and rewrites selected subterms, calling a control function on each subterm and a rewriting tactic on the selected ones.

    For each subterm `t`, `ctrl t` returns a pair. If its first component is true, the tactic `rw` is called on a new goal `t == ?u`, and once that goal is solved, `t` is replaced by the solution of `?u`; if it is false, no goal is created. The second component, of type `FStar.Stubs.Tactics.Types.ctrl_flag`, says how to continue:

    - `Continue`: keep going with further subterms
    - `Skip`: stop descending into this subtree
    - `Abort`: stop everything

    The direction, `TopDown` or `BottomUp`, says whether the term is traversed in preorder or in postorder. With `BottomUp`, `Skip` stops rewriting from the current node up to the root but still considers its siblings, so `ctrl_rewrite BottomUp (fun _ -> (true, Skip)) t` calls `t` on every leaf. See `FStar.Tactics.V2.Derived.pointwise` and `FStar.Tactics.V2.Derived.topdown_rewrite` for friendlier versions. *)
val ctrl_rewrite :
    direction ->
    (ctrl : term -> Tac (bool & ctrl_flag)) ->
    (rw:unit -> Tac unit) ->
    Tac unit

(*| Duplicates the current goal so that its witness can be changed: the goal `Gamma |- w : t` becomes `Gamma |- ?u : t` followed by `Gamma |= ?u == w`.

    One can then pick `?u`, for instance with `FStar.Tactics.V2.Derived.exact`, and prove the equality. *)
val dup : unit -> Tac unit

// Proof namespace management
(*| Stops encoding the definitions of the given namespace to the SMT solver for the current goal.

    The string is a namespace prefix matched on whole module name components: `prune "A.B.C"` covers module `A.B.C` and its submodules, `prune ""` covers everything, and `prune "FStar.S"` does not cover `FStar.Set`. `FStar.Stubs.Tactics.V2.Builtins.addns` is the opposite operation; the latest call takes precedence. *)
val prune : string -> Tac unit

(*| Adds a namespace back to the SMT encoding of the current goal, the opposite of `FStar.Stubs.Tactics.V2.Builtins.prune`.

    The latest of `prune` and `addns` takes precedence. *)
val addns : string -> Tac unit

(*| Case-analyzes a term of an inductive type, replacing the current goal by one goal per constructor.

    The generated match has one branch for each constructor, so it is exhaustive and no verification condition is generated for that. Returns the constructors with their arities, in the order of the new goals. `FStar.Tactics.V2.Derived.destruct` discards the result. *)
val t_destruct : term -> Tac (list (fv & nat))

(*| Sets command-line options for the current goal only, for example `set_options "--z3rlimit 20"`.

    Mostly useful for SMT options. Fails if the options cannot be parsed or set. *)
val set_options : string -> Tac unit

(*| Creates a new unconstrained unification variable in the given environment, with the given type or, if `None`, with a type that is itself a new uvar.

    No goal is created for it; see `FStar.Stubs.Tactics.V2.Builtins.unshelve`. `FStar.Tactics.V2.Derived.fresh_uvar` uses the current goal's environment. *)
val uvar_env : env -> option typ -> Tac term

(*| Creates a new unconstrained unification variable of the given type in the given environment, which can be solved by a ghost term.

    Compare `FStar.Stubs.Tactics.V2.Builtins.uvar_env`. *)
val ghost_uvar_env : env -> typ -> Tac term

(*| Creates a new universe unification variable `?u` and returns the term `Type u#?u`. *)
val fresh_universe_uvar : unit -> Tac term

(*| Calls the unifier on two terms in the given environment, returning whether they could be unified.

    On success the terms are unified and uvars are instantiated as needed; on failure no uvar is changed. See `FStar.Stubs.Tactics.V2.Builtins.unify_guard_env` and `FStar.Stubs.Tactics.V2.Builtins.match_env`, and `FStar.Tactics.V2.Derived.unify` for the version using the current goal's environment. *)
val unify_env : env -> t1:term -> t2:term -> Tac bool

(*| Like `FStar.Stubs.Tactics.V2.Builtins.unify_env`, but allows some guards to be raised during unification, and adds a new goal for them.

    See `FStar.Stubs.Tactics.V2.Builtins.t_trefl` for which guards are allowed. *)
val unify_guard_env : env -> t1:term -> t2:term -> Tac bool

(*| Checks whether `t2` matches `t1`, that is, whether instantiating the uvars of `t2` alone makes it unify with `t1`.

    On success uvars are instantiated as needed; on failure no uvar is changed. `FStar.Tactics.V2.Derived.tmatch` uses the current goal's environment. *)
val match_env : env -> t1:term -> t2:term -> Tac bool

(*| Runs an external program with the given arguments and standard input, and returns its output.

    For security reasons this is only allowed when F\* was run with `--unsafe_tactic_exec`; otherwise the tactic fails. *)
val launch_process : string -> list string -> string -> Tac string

(** Get a fresh bv of some name and type. The name is only useful
for pretty-printing, since there is a fresh inaccessible integer within
the bv too. *)
(* val fresh_bv_named : string -> Tac bv *)

(*| Replaces the type of the current goal by the given type, provided they are convertible.

    The new type is typechecked and unified with the goal type; if that fails, both are fully normalized and unified again. Fails if they are not convertible. *)
val change : typ -> Tac unit

(*| Returns the current guard policy, which says what to do with verification conditions raised internally by the tactic engine.

    See `FStar.Stubs.Tactics.Types.guard_policy` for the possible policies (add guards as goals or SMT goals, send them to SMT or force them immediately, or drop them). Set it with `FStar.Stubs.Tactics.V2.Builtins.set_guard_policy`. *)
val get_guard_policy : unit -> TacRO guard_policy

(*| Sets the guard policy, which says what to do with verification conditions raised internally by the tactic engine.

    See `FStar.Stubs.Tactics.Types.guard_policy`. `FStar.Tactics.V2.Derived.with_policy` sets it only while running a tactic. *)
val set_guard_policy : guard_policy -> Tac unit

(*| Returns true when the tactic runs in an environment that admits verification conditions instead of proving them.

    Implemented by the compiler: it reads the admit flag of the main environment. The original comment ties this to `--admit_smt_queries true`. *)
val lax_on : unit -> TacRO bool

(*| Admits the current goal, setting its witness to the given term, and logs a warning.

    This is unsound. See `FStar.Tactics.V2.Derived.tadmit` and `FStar.Tactics.V2.Derived.admit_all`. *)
val tadmit_t : term -> Tac unit

(*| Merges the first two goals, which must be irrelevant (propositions), into a single goal.

    It finds a maximal common prefix of their environments and reverts the rest. Useful to reduce the number of SMT queries when they share obligations. Fails if there are fewer than two goals. See `FStar.Tactics.V2.Derived.join_all_smt_goals`. *)
val join : unit -> Tac unit

(*| Looks up a value in the local metastate, a map from strings to values of any type.

    Fails if there is no value for the key or if the value does not typecheck at the requested type. Values are stored with `FStar.Stubs.Tactics.V2.Builtins.lset`. *)
val lget     : #a:Type -> string -> TacRO a
(*| Stores a value under a string key in the local metastate, a map from strings to values of any type.

    Read it back with `FStar.Stubs.Tactics.V2.Builtins.lget`. *)
val lset     : #a:Type -> string -> a -> Tac unit

(*| Replaces the list of active goals by the given list.

    Goals that are dropped are not solved: their obligations remain in the implicits. See `FStar.Stubs.Tactics.V2.Builtins.set_smt_goals`. *)
val set_goals     : list goal -> Tac unit

(*| Replaces the list of SMT goals by the given list.

    Goals that are dropped are not solved: their obligations remain in the implicits. Despite the name, nothing about these goals is specific to SMT; they are just goals set aside, which are sent to SMT if they remain at the end. See `FStar.Stubs.Tactics.V2.Builtins.set_goals`. *)
val set_smt_goals : list goal -> Tac unit

(*| Returns the current wall-clock time in milliseconds. *)
val curms : unit -> TacRO int

(*| Sets the urgency of the error messages raised afterwards.

    Usually called just before raising an exception, as `FStar.Tactics.V2.Derived.fail_silently` does with urgency `0`. *)
val set_urgency : int -> TacS unit

(*| Controls whether the engine dumps the proof state when the tactic fails with an exception.

    This is true by default; set it to false for less verbose failures. *)
val set_dump_on_failure : bool -> TacS unit

(*| Parses a string into a term, resolving names in the given environment.

    The term is only parsed and desugared, not typechecked. Fails on a parse or desugaring error. *)
val string_to_term : env -> string -> TacRO term

(*| Adds an identifier to the name-resolution environment of `e`, returning the new environment and the binding for the identifier.

    Useful to parse, with `FStar.Stubs.Tactics.V2.Builtins.string_to_term`, terms that refer to a new local name. *)
val push_bv_dsenv : env -> string -> Tac (env & binding)

(*| Prints a term with the F\* pretty-printer.

    This is effectful because the result depends on the current options, and because it could expose details of the term representation that the term views hide (which would break the `pack`/`inspect` inversion lemmas). See `FStar.Stubs.Tactics.V2.Builtins.term_to_doc` for an unrendered document and `FStar.Tactics.Print.term_to_ast_string` for the abstract syntax. *)
val term_to_string : term -> TacRO string

(*| Prints a computation type with the F\* pretty-printer.

    See `FStar.Stubs.Tactics.V2.Builtins.term_to_string` for why this is effectful. *)
val comp_to_string : comp -> TacRO string

(*| Like `FStar.Stubs.Tactics.V2.Builtins.term_to_string`, but returns an unrendered pretty-printing document. *)
val term_to_doc : term -> TacRO Pprint.document

(*| Like `FStar.Stubs.Tactics.V2.Builtins.comp_to_string`, but returns an unrendered pretty-printing document. *)
val comp_to_doc : comp -> TacRO Pprint.document

(*| Prints a source range as a string. *)
val range_to_string : range -> TacRO string

(*| Runs a tactic with the compat pre-core setting `n`.

    An escape hatch for backward compatibility, for code that breaks with the core typechecker. *)
val with_compat_pre_core : #a:Type -> n:int -> f:(unit -> Tac a) -> Tac a

(*| Returns the verification configuration of the current goal, including fuel, ifuel and rlimit.

    See `FStar.Stubs.Tactics.V2.Builtins.set_vconfig`. *)
val get_vconfig : unit -> TacRO vconfig

(*| Sets the verification configuration (fuel, ifuel, rlimit and so on) of the current goal.

    It is used if the goal is sent to SMT at the end of the tactic run. *)
val set_vconfig : vconfig -> Tac unit

(*| Tries to solve the current goal with SMT immediately, using the given verification configuration, and fails if it cannot.

    The current goal's own configuration is ignored. `FStar.Tactics.V2.Derived.smt_sync` uses the goal's configuration, and `FStar.Tactics.V2.Derived.smt_sync'` sets fuel and ifuel. *)
val t_smt_sync : vconfig -> Tac unit

(*| Returns the identifiers of the unification variables that occur free in a term.

    This is not a reflection primitive, since the result depends on the current state of the unifier. *)
val free_uvars : term -> TacRO (list int)

(*| Returns all key/value pairs set with the `--ext` option.

    The order is unspecified. *)
val all_ext_options : unit -> TacRO (list (string & string))

(*| Returns the value of a key set with the `--ext` option, or the empty string if the key is unset. *)
val ext_getv (k:string) : TacRO string

(*| Returns true if the `--ext` flag of the given key is enabled, that is, set to a non-empty value other than `0`, `off` or `false`. *)
val ext_enabled (k:string) : TacRO bool

(*| Returns all key/value pairs set with the `--ext` option whose keys are in the given namespace. *)
val ext_getns (ns:string) : TacRO (list (string & string))

(*| Allocates a reference in the tactic's local state, holding the given initial value.

    This local state is monotonic: it is not reverted when the tactic backtracks, for instance with `FStar.Stubs.Tactics.V2.Builtins.catch`. Use `FStar.Stubs.Tactics.V2.Builtins.read` and `FStar.Stubs.Tactics.V2.Builtins.write` to access it. *)
val alloc (#a:Type) (x:a) : Tac (tref a)
(*| Reads the current value of a reference allocated with `FStar.Stubs.Tactics.V2.Builtins.alloc`. *)
val read (#a:Type) (r:tref a) : TacRO a
(*| Updates a reference allocated with `FStar.Stubs.Tactics.V2.Builtins.alloc`.

    The write is not reverted on backtracking. *)
val write (#a:Type) (r:tref a) (x:a) : Tac unit

(*| During a `%splice`, returns the qualifiers attached to the splice declaration.

    Returns the empty list when the tactic was not started by a splice. *)
val splice_quals () : TacRO (list qualifier)

(*| During a `%splice`, returns the attributes attached to the splice declaration.

    Returns the empty list when the tactic was not started by a splice. *)
val splice_attrs () : TacRO (list term)

(***** APIs used in the meta DSL framework *****)

(** Meta DSL framework is an experimental feature
    See examples/dsls/ for more details
    Following APIs are part of the framework *)

(** TODO: maybe the equiv APIs should require typing of the arguments? *)

(*| The result of the typing primitives of the meta DSL framework: an optional result together with the issues (errors and warnings) that were raised.

    These primitives return `Some` result (usually carrying a typing, subtyping or equivalence token) on success and `None` with the issues on failure, instead of failing the tactic. Most of them use the compiler's core typechecker, reject environments and terms that contain unification variables (returning `None` with an issue), and do not change the unifier state. Proof obligations they produce are handled according to the current guard policy (see `FStar.Stubs.Tactics.V2.Builtins.get_guard_policy`). The meta DSL framework is experimental; see `examples/dsls/`. *)
unfold
let ret_t (a:Type) = option a & issues

(*| Checks, with the core typechecker, that a type is non-informative (its values carry no computational content), returning a token on success.

    Part of the experimental meta DSL support; see `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val is_non_informative (g:env) (t:typ)
  : Tac (ret_t (non_informative_token g (denote_term t)))

(*| Checks, with the core typechecker, that `t0` is a subtype of `t1` in `g`, returning a subtyping token on success.

    See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention, and `FStar.Stubs.Tactics.V2.Builtins.t_check_equiv` for equivalence. *)
val check_subtyping (g:env) (t0 t1:typ)
  : Tac (ret_t (subtyping_token g (denote_term t0) (denote_term t1)))

(*| Checks, with the core typechecker, that `t0` and `t1` are equivalent types in `g`, returning an equivalence token on success.

    `smt_ok` allows the check to produce proof obligations, which are handled per the current guard policy, and `unfolding_ok` allows unfolding definitions. See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val t_check_equiv (smt_ok:bool) (unfolding_ok:bool) (g:env) (t0 t1:typ)
  : Tac (ret_t (equiv_token g (denote_term t0) (denote_term t1)))

(*| Computes the type of a term with the core typechecker, returning the effect (total or ghost) and the type, with a typing token.

    See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention, and `FStar.Stubs.Tactics.V2.Builtins.tc_term` for a variant that also instantiates implicits. *)
val core_compute_term_type (g:env) (e:term)
  : Tac (ret_t (r:(tot_or_ghost & typ){typing_token g (denote_term e) (fst r, denote_term (snd r))}))

(*| Checks with the core typechecker that a term has the given type with the given effect (total or ghost), returning a typing token.

    See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val core_check_term (g:env) (e:term) (t:typ) (eff:tot_or_ghost)
  : Tac (ret_t (typing_token g (denote_term e) (eff, denote_term t)))

(*| Checks with the core typechecker that a term has the given type, returning the effect (total or ghost) at which it does, with a typing token.

    See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val core_check_term_at_type (g:env) (e:term) (t:typ)
  : Tac (ret_t (eff:tot_or_ghost{typing_token g (denote_term e) (eff, denote_term t)}))

(*| Instantiates the implicits of a term and computes its type, returning the elaborated term, its effect and its type, with a typing token.

    See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention, and `FStar.Stubs.Tactics.V2.Builtins.core_compute_term_type` for terms that need no elaboration. *)
val tc_term (g:env) (e:term)
  : Tac (ret_t (r:(term & (tot_or_ghost & typ)){typing_token g (denote_term (fst r)) (fst (snd r), denote_term (snd (snd r)))}))

(*| Computes the universe of a type, with a token that the type has type `Type u` for the returned universe `u`.

    Fails (returns `None`) if the universe remains an unresolved variable. See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val universe_of (g:env) (e:term)
  : Tac (ret_t (u:universe{typing_token g (denote_term e) (E_Total, Ts_Type (denote_universe u))}))

(*| A token that `t` is a valid proposition in `g`: an erased proof term `e` together with typings that `t` has type `prop` and `e` has type `t`.

    Returned by `FStar.Stubs.Tactics.V2.Builtins.check_prop_validity`. *)
type prop_validity_token (g:env) (t:term) =
  Ghost.erased (
    e:term{typing_token g (denote_term t) (E_Total, denote_term (pack_ln (Tv_FVar (pack_fv prop_qn)))) /\
           typing_token g (denote_term e) (E_Total, denote_term t)}
  )

(*| Proves that a proposition (of type `prop` in `g`) is valid, returning a `FStar.Stubs.Tactics.V2.Builtins.prop_validity_token`.

    The proposition becomes a proof obligation handled per the current guard policy (for instance sent to SMT). See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val check_prop_validity (g:env) (t:term { typing_token g (denote_term t) (E_Total, denote_term (`prop)) })
  : Tac (ret_t (prop_validity_token g t))

// Can't immediately move to FStar.Tactics.Types since pattern is not in scope there
(*| An abstract proposition stating that the given patterns, with the given bindings for each, exhaustively match a scrutinee `sc` of type `t` in `g`.

    Produced by `FStar.Stubs.Tactics.V2.Builtins.check_match_complete`. Implemented by the compiler. *)
val match_complete_token (g:env) (sc:term_spec) (t:term_spec) (pats:list pattern_spec) (bnds:list (list binding))
  : prop

(*| Checks that a list of patterns is exhaustive for a scrutinee of the given type, returning the elaborated patterns, the bindings of each pattern and a `FStar.Stubs.Tactics.V2.Builtins.match_complete_token`.

    There is one list of bindings per pattern, and the bindings are open. See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val check_match_complete (g:env) (sc:term) (t:typ) (pats:list pattern)
  : Tac (ret_t (pats_bnds:(list pattern & list (list binding))
                           {match_complete_token g (denote_term sc) (denote_term t) (List.Tot.map denote_pattern (fst pats_bnds)) (snd pats_bnds)
                            /\ List.Tot.length (fst pats_bnds) == List.Tot.length (snd pats_bnds)
                            /\ List.Tot.length (fst pats_bnds) == List.Tot.length pats}))

(*| Instantiates the implicit arguments of a term, optionally against an expected type, returning the elaborated term and its type.

    The returned list contains fresh names (fresh with respect to `g`), with their types, for the implicits that could not be solved. When `inst_extra` is true, implicits at the end of the type of the term may also be instantiated, as in turning `None` into `None #int`. See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val instantiate_implicits (g:env) (t:term) (expected_typ : option term)
  (inst_extra : bool)
  : Tac (ret_t (list (namedv & typ) & term & typ))

(*| Tries to find substitutions for the names `uvs` by unifying `t0` and `t1`, returning the names it could solve with their solutions.

    Internally the names are replaced by fresh unification variables in both terms before unifying. The names are listed oldest first, and `t0` and `t1` should be well-typed in `g` extended with them. There are no guarantees on the solutions: the caller should check that they are well-typed. See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val try_unify (g:env) (uvs:list (namedv & typ)) (t0 t1:term)
  : Tac (ret_t (list (namedv & term)))

(*| Suggests which of two terms to unfold before relating them, by comparing the delta depths of their heads.

    The result is a `FStar.Stubs.TypeChecker.Core.unfold_side`: `Both` when the depths are equal, otherwise `Left` or `Right` for the side with the greater depth. See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val maybe_relate_after_unfolding (g:env) (t1 t2:term)
  : Tac (ret_t unfold_side)

(*| Unfolds the head symbol of a term once, returning the result with an equivalence token.

    Fails (returns `None`) if the head cannot be unfolded. See `FStar.Stubs.Tactics.V2.Builtins.ret_t` for the result convention. *)
val maybe_unfold_head (g:env) (t0:term)
  : Tac (ret_t (t1:term{equiv_token g (denote_term t0) (denote_term t1)}))

(*| Normalizes a term in the given environment with the given steps, returning the result with an equivalence token for the original and the normalized term.

    Unlike `FStar.Stubs.Tactics.V2.Builtins.norm_term_env` it does not typecheck the term, so the term should be well-typed; this precondition is not yet enforced by the type. *)
val norm_well_typed_term
  (g:env) (steps : list norm_step) (t:term)
  : Tac (t':term{equiv_token g (denote_term t) (denote_term t')})

(*| Returns the environment extended so that names of the given namespace can be used unqualified, as with `open`.

    Only affects name resolution, for example by `FStar.Stubs.Tactics.V2.Builtins.string_to_term` and `FStar.Stubs.Tactics.V2.Builtins.resolve_name`. *)
val push_open_namespace (g:env) (ns:name)
  : Tac env

(*| Returns the environment extended with the module abbreviation `n` for module `m`, as with `module n = m`.

    Only affects name resolution. *)
val push_module_abbrev (g:env) (n:string) (m:name)
  : Tac env

(*| Resolves a (possibly partially qualified) name in the given environment to a local variable or a top-level name, as the desugarer would.

    Returns `None` if the name does not resolve. *)
val resolve_name (g:env) (n:name)
  : Tac (option (either bv fv))

(*| Reports the given issues (errors, warnings, information) as if raised by the compiler, without failing the tactic.

    When the engine dumps on failure (see `FStar.Stubs.Tactics.V2.Builtins.set_dump_on_failure`), each message is prefixed by "Tactic logged issue:". *)
val log_issues (issues:list FStar.Issue.issue)
  : Tac unit

(*| Runs a tactic on a fresh proof state whose single goal is `goal_ty`, and returns the witness it builds, with a typing token.

    This lets a metaprogram spawn a sub-metaprogram from a clean state. Returns `None` with the issues if the subtactic fails or leaves a goal it cannot discharge; the proof state is not dumped on failure. `u` is the universe of `goal_ty`. See `FStar.Stubs.Tactics.V2.Builtins.call_subtac_tm` for a quoted tactic. *)
val call_subtac (g:env) (t : unit -> Tac unit) (u:universe)
                (goal_ty : term{typing_token g (denote_term goal_ty) (E_Total, Ts_Type (denote_universe u))})
  : Tac (ret_t (w:term{typing_token g (denote_term w) (E_Total, denote_term goal_ty)}))

(*| Like `FStar.Stubs.Tactics.V2.Builtins.call_subtac`, but the subtactic is given as a quoted term. *)
val call_subtac_tm
    (g:env) (t : term) (u:universe)
    (goal_ty : term{typing_token g (denote_term goal_ty) (E_Total, Ts_Type (denote_universe u))})
  : Tac (ret_t (w:term{typing_token g (denote_term w) (E_Total, denote_term goal_ty)}))

(*| Runs a tactic and records the time it takes under the given statistics key, otherwise behaving exactly like the tactic.

    The statistics are printed when F\* runs with `--stats true`. *)
val stats_record #a #wp (s : string) ($f : unit -> TAC a wp) : TAC a wp

(*| Runs a tactic with the given string added to the error context, so that errors raised inside it mention that context.

    Otherwise behaves exactly like the tactic. *)
val with_error_context #a #wp (s : string) ($f : unit -> TAC a wp) : TAC a wp
