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
module FStar.Tactics.V2.Derived

open FStar.Reflection.V2
open FStar.Reflection.V2.Formula
open FStar.Tactics.Effect
open FStar.Stubs.Tactics.Types
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Tactics.Util
open FStar.Tactics.V2.SyntaxHelpers
open FStar.VConfig
open FStar.Tactics.NamedView
open FStar.Tactics.V2.SyntaxCoercions
include FStar.Tactics.Names

module L = FStar.List.Tot.Base
private let (@) = L.op_At

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(*| Returns the user-facing (pretty-printing) name of a bound variable.

    The name is only for display; it does not identify the variable. See
    also `FStar.Tactics.V2.Derived.name_of_binder`. *)
let name_of_bv (bv : bv) : Tac string =
    unseal ((inspect_bv bv).ppname)

(*| Renders a bound variable as a string for messages; currently just its
    name, as given by `FStar.Tactics.V2.Derived.name_of_bv`. *)
let bv_to_string (bv : bv) : Tac string =
    (* Could also print type...? *)
    name_of_bv bv

(*| Returns the user-facing (pretty-printing) name of a binder.

    See `FStar.Tactics.V2.Derived.binder_to_string` for a rendering that
    also shows the unique index and the sort. *)
let name_of_binder (b : binder) : Tac string =
  unseal b.ppname

(*| Renders a binder as `name@@uniq::(sort)`, showing its name, unique
    index and printed sort, for debugging output.

    Qualifiers and attributes are not printed. *)
let binder_to_string (b : binder) : Tac string =
  // TODO: print aqual, attributes..? or no?
  name_of_binder b ^ "@@" ^ string_of_int b.uniq ^ "::(" ^ term_to_string b.sort ^ ")"

(*| Renders a binding (a variable of the goal's context) as a string for
    messages; currently just its name. *)
let binding_to_string (b : binding) : Tac string =
  unseal b.ppname

(*| Returns the sort recorded in a named variable (unsealing it).

    The sort may be `Tv_Unknown`, for instance for variables made by
    `FStar.Tactics.V2.Derived.fresh_namedv`. *)
let type_of_var (x : namedv) : Tac typ =
  unseal ((inspect_namedv x).sort)

(*| Returns the type of a binding of the goal's context (its `sort` field). *)
let type_of_binding (x : binding) : Tot typ =
  x.sort

exception Goal_not_trivial

(*| Returns the list of active goals of the current proof state, the first
    one being the goal most tactics act on.

    SMT goals are not included; see `FStar.Tactics.V2.Derived.smt_goals`. *)
let goals () : Tac (list goal) = goals_of (get ())
(*| Returns the list of goals that have been set aside for the SMT solver
    (for example by `FStar.Tactics.V2.Derived.smt`), which are sent to SMT
    when the tactic finishes. *)
let smt_goals () : Tac (list goal) = smt_goals_of (get ())

private
let map_optRO (f:'a -> TacRO 'b) (x:option 'a) : TacRO (option 'b) =
  match x with
  | None -> None
  | Some x -> Some (f x)

(*| Aborts the tactic with a `TacticFailure` carrying a structured error
    message and, optionally, the source range to report it at.

    Like every `fail` variant it never returns and can be caught by
    `FStar.Tactics.V2.Derived.try_with`, `FStar.Tactics.V2.Derived.trytac`
    or `FStar.Tactics.V2.Derived.or_else`. *)
let fail_doc_at (#a:Type) (m:error_message) (r:option range)
  : TacH a (requires True) (ensures fun _ -> False)
  = let r = map_optRO fixup_range r in
    raise #a (TacticFailure (m, r))

(*| Aborts the tactic with a `TacticFailure` carrying a structured error
    message, without a source range.

    See `FStar.Tactics.V2.Derived.fail` for the plain string version. *)
let fail_doc (#a:Type) (m:error_message)
  : TacH a (requires True) (ensures fun _ -> False)
  = raise #a (TacticFailure (m, None))

(*| Aborts the tactic with a `TacticFailure` whose message is the given
    string, reported at the given source range if one is provided. *)
let fail_at (#a:Type) (m:string) (r:option range)
  : TacH a (requires True) (ensures fun _ -> False)
  = fail_doc_at (mkmsg m) r

(*| Aborts the tactic with a `TacticFailure` whose message is the given
    string; the standard way for a tactic to signal that it does not apply.

    It never returns, and its result type is arbitrary. The failure can be
    caught by `FStar.Tactics.V2.Derived.try_with`,
    `FStar.Tactics.V2.Derived.trytac` or `FStar.Tactics.V2.Derived.or_else`;
    otherwise it is reported as an error. See also
    `FStar.Tactics.V2.Derived.fail_at` and
    `FStar.Tactics.V2.Derived.fail_silently`. *)
let fail (#a:Type) (m:string)
  : TacH a (requires True) (ensures fun _ -> False)
  = fail_at m None

(*| Aborts the tactic with a `TacticFailure` carrying a structured message,
    after setting the error urgency to 0 (with
    `FStar.Stubs.Tactics.V2.Builtins.set_urgency`).

    Meant for failures that are expected to be caught. See
    `FStar.Tactics.V2.Derived.fail_silently` for the string version. *)
let fail_silently_doc (#a:Type) (m:error_message)
  : TacH a (requires True) (ensures fun _ -> False)
  = set_urgency 0;
    raise #a (TacticFailure (m, None))

(*| Aborts the tactic with a `TacticFailure` whose message is the given
    string, after setting the error urgency to 0.

    Meant for failures that are expected to be caught; otherwise behaves like
    `FStar.Tactics.V2.Derived.fail`. *)
let fail_silently (#a:Type) (m:string)
  : TacH a (requires True) (ensures fun _ -> False)
  = fail_silently_doc (mkmsg m)

(*| Returns the first active goal itself (not its type); fails with "no
    more goals" when there are no active goals.

    SMT goals are ignored. Use `FStar.Tactics.V2.Derived.cur_goal` for the
    goal's type. *)
let _cur_goal () : Tac goal =
    match goals () with
    | []   -> fail "no more goals"
    | g::_ -> g

(*| Returns the typing environment of the first active goal; fails when
    there are no goals. *)
let cur_env () : Tac env = goal_env (_cur_goal ())

(*| Returns the type (the statement to prove) of the first active goal;
    fails with "no more goals" when there are none.

    For a proposition the goal usually has the form `squash p`; use
    `FStar.Tactics.V2.Logic.cur_formula` to view it as a formula. *)
let cur_goal () : Tac typ = goal_type (_cur_goal ())

(*| Returns the witness of the first active goal, the (usually still
    unresolved) term that solving the goal will define. *)
let cur_witness () : Tac term = goal_witness (_cur_goal ())

(*| Returns the bindings of the first active goal's context (its local
    variables and hypotheses).

    See `FStar.Tactics.V2.Derived.nth_var` to pick one by position. *)
let cur_vars () : Tac (list binding) =
    vars_of_env (cur_env ())

(*| Runs a tactic under the given guard policy (what to do with guards
    raised by the engine: SMT, Goal, Force, ...) and then restores the
    previous policy when it returns. *)
let with_policy pol (f : unit -> Tac 'a) : Tac 'a =
    let old_pol = get_guard_policy () in
    set_guard_policy pol;
    let r = f () in
    set_guard_policy old_pol;
    r

(*| Solves the first goal with the given term, which must typecheck at the
    goal's type.

    Typing guards that arise are sent to SMT (the `SMT` guard policy). If the goal type is a refinement,
    its formula may become a separate obligation.
    Fails if the term does not have the goal's type. See also
    `FStar.Tactics.V2.Derived.exact_guard` (guards become goals) and
    `FStar.Tactics.V2.Derived.exact_with_ref`. *)
let exact (t : term) : Tac unit =
    with_policy SMT (fun () -> t_exact true false t)

(*| Solves the first goal with the given term, typechecking it with the
    goal's type as the expected type, which allows a term whose type is a
    subtype of the goal's type.

    A more flexible variant of `FStar.Tactics.V2.Derived.exact`; guards
    are sent to SMT. *)
let exact_with_ref (t : term) : Tac unit =
    with_policy SMT (fun () -> t_exact true true t)

(*| Solves the first goal if it normalizes to `True`, and fails otherwise
    by raising `Goal_not_trivial`.

    The goal is first normalized with `iota`, `zeta`, `reify_`, `delta`,
    `primops`, `simplify` and `unmeta`, so closed arithmetic facts such as
    `1 + 1 == 2` and syntactic equalities `x == x` are trivial.

    ```fstar
    let _ = assert (True /\ 1 + 1 == 2) by (split (); trivial (); trivial ())
    ``` *)
let trivial () : Tac unit =
  norm [iota; zeta; reify_; delta; primops; simplify; unmeta];
  let g = cur_goal () in
  match term_as_formula g with
  | True_ -> exact (`())
  | _ -> raise Goal_not_trivial

(*| Runs a tactic once, at typechecking time, in a proof state without
    goals: `run_tactic t` typechecks as a `unit` value and has the effect of
    executing `t`.

    Useful to run a tactic for its side effects, such as printing. *)
let run_tactic (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic (fun () -> trivial (); t ()) True) (range_of t)))
         (ensures (fun _ -> True))
  = ()

(*| Removes the first goal from the list of active goals without solving it;
    fails if there are no goals.

    The goal's obligation is not discharged: if it is never solved,
    checking fails after the tactic finishes. *)
let dismiss () : Tac unit =
    match goals () with
    | [] -> fail "dismiss: no more goals"
    | _::gs -> set_goals gs

(*| Swaps the first two active goals; fails if there are fewer than two. *)
let flip () : Tac unit =
    let gs = goals () in
    match goals () with
    | [] | [_]   -> fail "flip: less than two goals"
    | g1::g2::gs -> set_goals (g2::g1::gs)

(*| Succeeds if there are no active goals left, and fails with "qed: not
    done!" otherwise.

    SMT goals are not considered. See also
    `FStar.Tactics.V2.Derived.finish_by`. *)
let qed () : Tac unit =
    match goals () with
    | [] -> ()
    | _ -> fail "qed: not done!"

(*| Prints a message, like `FStar.Stubs.Tactics.V2.Builtins.print`, but
    only when tactic debugging is enabled (`--debug Tac`). *)
let debug (m:string) : Tac unit =
    if debugging () then print m

(*| Moves the first active goal to the front of the SMT goals, to be
    discharged by the SMT solver when the tactic finishes; fails if there
    are no active goals.

    The solver is not called immediately. Only proof-irrelevant goals
    (propositions) should be sent; otherwise the engine raises an error
    later. *)
let smt () : Tac unit =
    match goals (), smt_goals () with
    | [], _ -> fail "smt: no active goals"
    | g::gs, gs' ->
        begin
        set_goals gs;
        set_smt_goals (g :: gs')
        end

(*| The tactic that does nothing and always succeeds; useful as a
    placeholder, for instance in `FStar.Tactics.V2.Derived.iseq`. *)
let idtac () : Tac unit = ()

(*| Moves the first active goal to the end of the goal list; fails if there
    are no goals. *)
let later () : Tac unit =
    match goals () with
    | g::gs -> set_goals (gs @ [g])
    | _ -> fail "later: no goals"

(*| Solves the first goal by applying the given term to as many arguments as
    needed for its result type to unify with the goal, turning the
    arguments into new goals.

    The fewest arguments that make the result unify are used. Arguments
    that appear free in later goals (and so will be determined by solving
    them) are not asked for as separate goals. Fails if no number of
    arguments makes the types unify. For lemmas use
    `FStar.Tactics.V2.Derived.apply_lemma`; see also
    `FStar.Tactics.V2.Derived.apply_noinst` and
    `FStar.Tactics.V2.Derived.apply_raw`. *)
let apply (t : term) : Tac unit =
    t_apply true false false t

(*| Like `FStar.Tactics.V2.Derived.apply`, but fails rather than
    instantiate unification variables that occur in the goal. *)
let apply_noinst (t : term) : Tac unit =
    t_apply true true false t

(*| Solves a goal `squash phi` with a lemma `l` whose postcondition is
    `phi`, turning the lemma's arguments and its precondition into new
    goals.

    Arguments of type `unit` are discharged by the engine. This is the
    backwards-reasoning step for lemmas; see also
    `FStar.Tactics.V2.Derived.apply_lemma_noinst` and
    `FStar.Tactics.V2.Derived.apply_lemma_rw`. *)
let apply_lemma (t : term) : Tac unit =
    t_apply_lemma false false t

(*| Solves a goal `squash (l == r)` by unifying `l` with `r`, failing if
    they do not unify.

    Unification may instantiate unification variables, which is how the
    rewriting tactics such as `FStar.Tactics.V2.Derived.pointwise` leave a
    subterm unchanged. See `FStar.Tactics.V2.Derived.trefl_guard` for a
    variant that allows guards. *)
let trefl () : Tac unit =
  t_trefl false

(*| Like `FStar.Tactics.V2.Derived.trefl`, but allows unification to raise
    some guards (currently those equating refinement types), which are
    added as a new goal. *)
let trefl_guard () : Tac unit =
  t_trefl true

(*| Solves a goal stating that an applied `match` equals the `match` whose
    branches are applied:
    `(match e with | pi -> ei) a1 .. an == (match e with | pi -> ei a1 .. an)`.

    Mostly useful in rewriting, when the right-hand side is a unification
    variable. A wrapper around
    `FStar.Stubs.Tactics.V2.Builtins.t_commute_applied_match`. *)
let commute_applied_match () : Tac unit =
  t_commute_applied_match ()

(*| Like `FStar.Tactics.V2.Derived.apply_lemma`, but fails rather than
    instantiate unification variables that occur in the goal. *)
let apply_lemma_noinst (t : term) : Tac unit =
    t_apply_lemma true false t

(*| Like `FStar.Tactics.V2.Derived.apply_lemma`, for rewriting goals of the
    form `t == ?u`: unification variables on the left-hand side of the
    goal's equality are not instantiated, while the right-hand side may be.

    Used by `FStar.Tactics.V2.Derived.l_to_r`. *)
let apply_lemma_rw (t : term) : Tac unit =
    t_apply_lemma false true t

(*| Like `FStar.Tactics.V2.Derived.apply`, but every argument of the
    applied term becomes a goal, even those that appear free in later goals.

    See `FStar.Stubs.Tactics.V2.Builtins.t_apply` for details. *)
let apply_raw (t : term) : Tac unit =
    t_apply false false false t

(*| Like `FStar.Tactics.V2.Derived.exact`, but typing guards needed for the
    term to have the goal's type are added as new goals instead of being
    sent to SMT. *)
let exact_guard (t : term) : Tac unit =
    with_policy Goal (fun () -> t_exact true false t)

(*| Rewrites the first goal by visiting every subterm `t` of its type, in
    the given direction (`TopDown` or `BottomUp`), and running the tactic on
    a goal `t == ?u`.

    When the tactic solves that goal, `t` is replaced by the solution of
    `?u`; to leave a subterm unchanged, solve the goal with
    `FStar.Tactics.V2.Derived.trefl`. The tactic can inspect the goal to
    decide what to do. See `FStar.Tactics.V2.Derived.pointwise` and
    `FStar.Tactics.V2.Derived.topdown_rewrite`. *)
let t_pointwise (d:direction) (tau : unit -> Tac unit) : Tac unit =
  let ctrl (t:term) : Tac (bool & ctrl_flag) =
    true, Continue
  in
  let rw () : Tac unit =
    tau ()
  in
  ctrl_rewrite d ctrl rw

(*| Rewrites the subterms `t` of the first goal for which `fst (ctrl t)` is
    true, traversing top-down, by running `rw` on a goal `t == ?u` and
    replacing `t` with the solution of `?u`.

    The second component of `ctrl t` controls the traversal: `0` continues
    into the subterms of `t`, `1` skips them and continues with the next
    subtree, and `2` stops all further rewriting. Any other value makes the
    tactic fail. Built on `FStar.Stubs.Tactics.V2.Builtins.ctrl_rewrite`. *)
let topdown_rewrite (ctrl : term -> Tac (bool & int))
                    (rw:unit -> Tac unit) : Tac unit
  = let ctrl' (t:term) : Tac (bool & ctrl_flag) =
      let b, i = ctrl t in
      let f =
        match i with
        | 0 -> Continue
        | 1 -> Skip
        | 2 -> Abort
        | _ -> fail "topdown_rewrite: bad value from ctrl"
      in
      b, f
    in
    ctrl_rewrite TopDown ctrl' rw

(*| Rewrites the first goal bottom-up by running the tactic on a goal
    `t == ?u` for every subterm `t` and replacing `t` with the solution of
    `?u`.

    The tactic must solve every such goal; use
    `FStar.Tactics.V2.Derived.trefl` to keep a subterm unchanged. See
    `FStar.Tactics.V2.Derived.pointwise'` for the top-down order and
    `FStar.Tactics.V2.Derived.l_to_r` for rewriting with lemmas. *)
let pointwise  (tau : unit -> Tac unit) : Tac unit = t_pointwise BottomUp tau
(*| Like `FStar.Tactics.V2.Derived.pointwise`, but visits the subterms of
    the goal top-down. *)
let pointwise' (tau : unit -> Tac unit) : Tac unit = t_pointwise TopDown  tau

(*| Returns the fully qualified name of the module being checked, as a list
    of name components. *)
let cur_module () : Tac name =
    moduleof (top_env ())

(*| Returns the names of the modules opened in the top-level environment. *)
let open_modules () : Tac (list name) =
    env_open_modules (top_env ())

(*| Creates a fresh unification variable in the environment of the first
    goal, optionally with a given type.

    When no type is given, a second unification variable is created for
    its type. See `FStar.Stubs.Tactics.V2.Builtins.uvar_env`. *)
let fresh_uvar (o : option typ) : Tac term =
    let e = cur_env () in
    uvar_env e o

(*| Tries to unify two terms in the environment of the first goal and
    returns whether it succeeded, instantiating unification variables on
    success.

    Nothing is changed when it returns `false`. See also
    `FStar.Tactics.V2.Derived.unify_guard` and
    `FStar.Tactics.V2.Derived.tmatch`. *)
let unify (t1 t2 : term) : Tac bool =
    let e = cur_env () in
    unify_env e t1 t2

(*| Like `FStar.Tactics.V2.Derived.unify`, but allows unification to raise
    some guards, which are added as a new goal. *)
let unify_guard (t1 t2 : term) : Tac bool =
    let e = cur_env () in
    unify_guard_env e t1 t2

(*| Checks whether the first term matches the second in the environment of
    the first goal, that is whether the second can have its unification
    variables instantiated to make them equal; returns the result.

    On success the variables are instantiated; on failure nothing changes.
    See `FStar.Stubs.Tactics.V2.Builtins.match_env`. *)
let tmatch (t1 t2 : term) : Tac bool =
    let e = cur_env () in
    match_env e t1 t2

(*| Splits the active goals into the first `n` and the rest, runs the first
    tactic on the first group and the second on the rest, and returns both
    results.

    The goals left by both tactics are concatenated (left ones first), and
    the SMT goals produced by both are added after the existing ones. Fails
    if `n` is negative. See also `FStar.Tactics.V2.Derived.focus` and
    `FStar.Tactics.V2.Derived.iseq`. *)
let divide (n:int) (l : unit -> Tac 'a) (r : unit -> Tac 'b) : Tac ('a & 'b) =
    if n < 0 then
      fail "divide: negative n";
    let gs, sgs = goals (), smt_goals () in
    let gs1, gs2 = List.Tot.Base.splitAt n gs in

    set_goals gs1; set_smt_goals [];
    let x = l () in
    let gsl, sgsl = goals (), smt_goals () in

    set_goals gs2; set_smt_goals [];
    let y = r () in
    let gsr, sgsr = goals (), smt_goals () in

    set_goals (gsl @ gsr); set_smt_goals (sgs @ sgsl @ sgsr);
    (x, y)

(*| Runs the tactics of the list on successive goals: the first tactic on
    the first goal, the second on the second goal, and so on, each one
    focused on its goal.

    Goals beyond the length of the list are left untouched. *)
let rec iseq (ts : list (unit -> Tac unit)) : Tac unit =
    match ts with
    | t::ts -> let _ = divide 1 t (fun () -> iseq ts) in ()
    | []    -> ()

(*| Runs a tactic on the first goal alone, hiding the other goals, and then
    restores them.

    The goals left by the tactic come before the previously hidden goals.
    Fails if there are no goals. Use it to make sure a tactic only affects
    the current goal. *)
let focus (t : unit -> Tac 'a) : Tac 'a =
    match goals () with
    | [] -> fail "focus: no goals"
    | g::gs ->
        let sgs = smt_goals () in
        set_goals [g]; set_smt_goals [];
        let x = t () in
        set_goals (goals () @ gs); set_smt_goals (smt_goals () @ sgs);
        x

(*| Prints the proof state restricted to the first goal, with a message,
    like `FStar.Stubs.Tactics.V2.Builtins.dump`. *)
let dump1 (m : string) = focus (fun () -> dump m)

(*| Runs a tactic on each active goal separately (focused) and returns the
    list of results.

    The goals left by each run replace the goal it ran on. *)
let rec mapAll (t : unit -> Tac 'a) : Tac (list 'a) =
    match goals () with
    | [] -> []
    | _::_ -> let (h, t) = divide 1 t (fun () -> mapAll t) in h::t

(*| Runs a tactic on each active goal separately (focused), discarding the
    results.

    The goals left by each run replace the goal it ran on. Fails if the
    tactic fails on any goal.

    ```fstar
    let _ = assert (1 + 1 == 2 /\ 2 + 2 == 4)
              by (split (); iterAll (fun () -> trivial ()))
    ``` *)
let rec iterAll (t : unit -> Tac unit) : Tac unit =
    (* Could use mapAll, but why even build that list *)
    match goals () with
    | [] -> ()
    | _::_ -> let _ = divide 1 t (fun () -> iterAll t) in ()

(*| Runs a tactic on each SMT goal separately; the goals it leaves are put
    back as SMT goals, and the active goals are kept unchanged. *)
let iterAllSMT (t : unit -> Tac unit) : Tac unit =
    let gs, sgs = goals (), smt_goals () in
    set_goals sgs;
    set_smt_goals [];
    iterAll t;
    let gs', sgs' = goals (), smt_goals () in
    set_goals gs;
    set_smt_goals (gs'@sgs')

(*| Runs the first tactic on the first goal and then the second tactic on
    each of the goals it produced, each run focused on one goal.

    ```fstar
    let _ = assert (True /\ True) by (seq split trivial)
    ``` *)
let seq (f : unit -> Tac unit) (g : unit -> Tac unit) : Tac unit =
    focus (fun () -> f (); iterAll g)

(*| Solves the first goal with the term applied to fresh unification
    variables, one per qualifier in the list (with that qualifier), and
    turns those not solved by typechecking into new goals.

    See `FStar.Tactics.V2.Derived.exact_n` for explicit arguments. *)
let exact_args (qs : list aqualv) (t : term) : Tac unit =
    focus (fun () ->
        let n = List.Tot.Base.length qs in
        let uvs = repeatn n (fun () -> fresh_uvar None) in
        let t' = mk_app t (zip uvs qs) in
        exact t';
        iter (fun uv -> if is_uvar uv
                        then unshelve uv
                        else ()) (L.rev uvs)
    )

(*| Solves the first goal with the term applied to `n` explicit arguments,
    which become new goals unless they are solved by typechecking.

    A shorthand for `FStar.Tactics.V2.Derived.exact_args`. *)
let exact_n (n : int) (t : term) : Tac unit =
    exact_args (repeatn n (fun () -> Q_Explicit)) t

(*| Returns the number of active goals (not counting SMT goals). *)
let ngoals () : Tac int = List.Tot.Base.length (goals ())

(*| Returns the number of goals set aside for SMT. *)
let ngoals_smt () : Tac int = List.Tot.Base.length (smt_goals ())

(* sigh GGG fix names!! *)
(*| Creates a named variable with the given display name, a fresh unique
    index and an unknown sort.

    See `FStar.Tactics.V2.Derived.fresh_namedv` for a generic name. *)
let fresh_namedv_named (s:string) : Tac namedv =
  let n = fresh () in
  pack_namedv ({
    ppname = seal s;
    sort   = seal (pack Tv_Unknown);
    uniq   = n;
  })

(*| Creates a named variable with a fresh unique index, a generic name of
    the form `x<n>` and an unknown sort.

    See also `FStar.Tactics.V2.Derived.fresh_namedv_named`. *)
let fresh_namedv () : Tac namedv =
  let n = fresh () in
  pack_namedv ({
    ppname = seal ("x" ^ string_of_int n);
    sort   = seal (pack Tv_Unknown);
    uniq   = n;
  })

(*| Creates an explicit binder with the given name and sort and a fresh
    unique index, for building abstractions and arrows.

    See also `FStar.Tactics.V2.Derived.fresh_binder` and
    `FStar.Tactics.V2.Derived.mk_abs`. *)
let fresh_binder_named (s : string) (t : typ) : Tac simple_binder =
  let n = fresh () in
  {
    ppname = seal s;
    sort   = t;
    uniq   = n;
    qual   = Q_Explicit;
    attrs  = [] ;
  }

(*| Creates an explicit binder of the given sort, with a fresh unique index
    and a generic name of the form `x<n>`. *)
let fresh_binder (t : typ) : Tac simple_binder =
  let n = fresh () in
  {
    ppname = seal ("x" ^ string_of_int n);
    sort   = t;
    uniq   = n;
    qual   = Q_Explicit;
    attrs  = [] ;
  }

(*| Creates an implicit binder of the given sort, with a fresh unique index
    and a generic name of the form `x<n>`. *)
let fresh_implicit_binder (t : typ) : Tac binder =
  let n = fresh () in
  {
    ppname = seal ("x" ^ string_of_int n);
    sort   = t;
    uniq   = n;
    qual   = Q_Implicit;
    attrs  = [] ;
  }

(*| Fails with "guard failed" unless the boolean is `true`; after it
    returns, the boolean is known to be `true`. *)
let guard (b : bool) : TacH unit (requires True)
                                 (ensures fun _ -> b)
        (* ^ the proofstate on failure is not exactly equal (has the psc set) *)
    =
    if not b then
        fail "guard failed"
    else ()

(*| Runs the first tactic and, if it raises an exception, runs the handler
    on that exception instead.

    The effects of the failed run on unification variables are reverted
    (see `FStar.Stubs.Tactics.V2.Builtins.catch`). *)
let try_with (f : unit -> Tac 'a) (h : exn -> Tac 'a) : Tac 'a =
    match catch f with
    | Inl e -> h e
    | Inr x -> x

(*| Runs a tactic and returns `Some` of its result, or `None` if it fails;
    never fails itself. *)
let trytac (t : unit -> Tac 'a) : Tac (option 'a) =
    try Some (t ())
    with
    | _ -> None

(*| Runs the first tactic and, if it fails, runs the second one instead.

    See also the infix `FStar.Tactics.V2.Derived.op_Less_Bar_Greater` and
    `FStar.Tactics.V2.Derived.first`. *)
let or_else (#a:Type) (t1 : unit -> Tac a) (t2 : unit -> Tac a) : Tac a =
    try t1 ()
    with | _ -> t2 ()

(*| Combines two tactics into one that runs the first and, if it fails, the
    second: an infix, unapplied form of `FStar.Tactics.V2.Derived.or_else`. *)
val (<|>) : (unit -> Tac 'a) ->
            (unit -> Tac 'a) ->
            (unit -> Tac 'a)
let (<|>) t1 t2 = fun () -> or_else t1 t2

(*| Runs the tactics of the list in order and returns the result of the
    first one that succeeds; fails with "no tactics to try" if all fail or
    the list is empty. *)
let first (ts : list (unit -> Tac 'a)) : Tac 'a =
    L.fold_right (<|>) ts (fun () -> fail "no tactics to try") ()

(*| Runs a tactic repeatedly until it fails and returns the list of its
    results; never fails itself.

    The run that fails is discarded. See also
    `FStar.Tactics.V2.Derived.repeat1` and
    `FStar.Tactics.V2.Derived.repeatseq`. *)
let rec repeat (#a:Type) (t : unit -> Tac a) : Tac (list a) =
    match catch t with
    | Inl _ -> []
    | Inr x -> x :: repeat t

(*| Like `FStar.Tactics.V2.Derived.repeat`, but the tactic must succeed at
    least once: a failure of the first run is propagated. *)
let repeat1 (#a:Type) (t : unit -> Tac a) : Tac (list a) =
    t () :: repeat t

(*| Runs a tactic repeatedly until it fails, discarding the results; never
    fails itself. *)
let repeat' (f : unit -> Tac 'a) : Tac unit =
    let _ = repeat f in ()

(*| Normalizes a term with the given steps, in the environment of the first
    goal, or in the top-level environment when there are no goals.

    The goals are unchanged. See `FStar.Stubs.Tactics.V2.Builtins.norm`
    to normalize the goal itself. *)
let norm_term (s : list norm_step) (t : term) : Tac term =
    let e =
        try cur_env ()
        with | _ -> top_env ()
    in
    norm_term_env e s t

(* TODO: would be nice to try to join them in a more meaningful
   way, as the order can matter. *)
(*| Joins all SMT goals into a single one, which can help when they are
    similar and easier for the solver to prove at once.

    Goals are joined with `FStar.Stubs.Tactics.V2.Builtins.join`; the order
    in which they are combined is not chosen in any meaningful way. The
    active goals are unchanged. *)
let join_all_smt_goals () =
  let gs, sgs = goals (), smt_goals () in
  set_smt_goals [];
  set_goals sgs;
  repeat' join;
  let sgs' = goals () in // should be a single one
  set_goals gs;
  set_smt_goals sgs'

(*| Turns a tactic into one that returns `unit`, ignoring its result. *)
let discard (tau : unit -> Tac 'a) : unit -> Tac unit =
    fun () -> let _ = tau () in ()

// TODO: do we want some value out of this?
(*| Runs a tactic on the first goal and, recursively, on every goal it
    produces, until it fails; never fails itself. *)
let rec repeatseq (#a:Type) (t : unit -> Tac a) : Tac unit =
    let _ = trytac (fun () -> (discard t) `seq` (discard (fun () -> repeatseq t))) in ()

(*| Admits the first goal, solving it without proof; unsafe, and reported
    with a warning.

    The goal's witness is set to `()`. See also
    `FStar.Tactics.V2.Derived.admit_all`. *)
let tadmit () = tadmit_t (`())

(*| Admits the first goal; the same as `FStar.Tactics.V2.Derived.tadmit`. *)
let admit1 () : Tac unit =
    tadmit ()

(*| Admits all active goals; unsafe, and reported with warnings. *)
let admit_all () : Tac unit =
    let _ = repeat tadmit in
    ()

(*| Returns whether the first goal arose from a typechecking guard
    (verification condition) rather than from a tactic step; fails when
    there are no goals. *)
let is_guard () : Tac bool =
    Stubs.Tactics.Types.is_guard (_cur_goal ())

(*| Sends the first goal to SMT if it arose from a typechecking guard, and
    fails otherwise. *)
let skip_guard () : Tac unit =
    if is_guard ()
    then smt ()
    else fail ""

(*| Sends goals that arose from typechecking guards to SMT, from the front
    of the goal list, stopping at the first goal that is not a guard; never
    fails. *)
let guards_to_smt () : Tac unit =
    let _ = repeat skip_guard in
    ()

(*| Normalizes the first goal with logical simplification and primitive
    operations only (`simplify` and `primops`). *)
let simpl   () : Tac unit = norm [simplify; primops]
(*| Reduces the first goal to weak head normal form, unfolding definitions
    as needed (`weak`, `hnf`, `primops` and `delta`). *)
let whnf    () : Tac unit = norm [weak; hnf; primops; delta]
(*| Normalizes the first goal with `primops`, `iota`, `delta` and `zeta`:
    unfolds definitions, reduces matches and recursive functions, and
    computes primitive operations. *)
let compute () : Tac unit = norm [primops; iota; delta; zeta]

(*| Introduces all the binders of a goal that is a literal arrow, moving
    them into the context, and returns them.

    The goal is not normalized or unfolded first. For logical `forall` and
    `==>` goals use `FStar.Tactics.V2.Logic.l_intros`. This shadows
    `FStar.Stubs.Tactics.V2.Builtins.intros`, which takes a bound. *)
let intros () : Tac (list binding) = intros (-1)

(*| Like `FStar.Tactics.V2.Derived.intros`, but discards the introduced
    bindings. *)
let intros' () : Tac unit = let _ = intros () in ()
(*| Does case analysis on a term of an inductive type, replacing the first
    goal by one goal per constructor.

    The constructor's arguments and an equation for the term are left as
    binders to introduce in each new goal; see
    `FStar.Tactics.V2.Derived.destruct_intros`. *)
let destruct tm : Tac unit = let _ = t_destruct tm in ()
(*| Does case analysis on a term of an inductive type, as
    `FStar.Tactics.V2.Derived.destruct`, and introduces the binders of each
    resulting goal. *)
let destruct_intros tm : Tac unit = seq (fun () -> let _ = t_destruct tm in ()) intros'

private val __cut : (a:Type) -> (b:Type) -> (a -> b) -> a -> b
private let __cut a b f x = f x

(*| Cuts on a statement: given a type `t`, the first goal is replaced by the
    same goal with a new hypothesis of type `t`, followed by a goal to prove
    `t`; returns the hypothesis. *)
let tcut (t:term) : Tac binding =
    let g = cur_goal () in
    let tt = mk_e_app (`__cut) [t; g] in
    apply tt;
    intro ()

(*| Adds a term to the context of the first goal as a new hypothesis of the
    term's type and returns the new binding.

    The binding does not remember that it equals the term. For lemma
    applications see `FStar.Tactics.V2.Derived.pose_apply` and
    `FStar.Tactics.V2.Logic.pose_lemma`. *)
let pose (t:term) : Tac binding =
    apply (`__cut);
    flip ();
    exact t;
    intro ()

(* [apply] is run under [focus] so that the goals it introduces are collected in
front of the ones that were already there, whether it prepends them (its own
implicit arguments) or appends them (a proof obligation coming out of its
guard).  Counting alone cannot tell the two apart. *)
(*| Like `FStar.Tactics.V2.Derived.pose`, but the term is applied (as with
    `FStar.Tactics.V2.Derived.apply`) rather than used exactly, so leftover
    implicit arguments become new goals instead of unsolved unification
    variables.

    This matters for a lemma application, whose precondition is a trailing
    implicit argument. Goals introduced this way are moved behind the
    existing goals, so the main goal (with the new hypothesis) stays first. *)
let pose_apply (t:term) : Tac binding =
    apply (`__cut);
    flip ();
    let n_rest = ngoals () - 1 in
    focus (fun () -> apply t);
    let gs = goals () in
    let n_introduced = ngoals () - n_rest in
    let n_introduced = if n_introduced < 0 then 0 else n_introduced in
    let introduced, rest = List.Tot.Base.splitAt n_introduced gs in
    set_goals (rest @ introduced);
    intro ()

(*| Introduces the first binder of an arrow goal, like
    `FStar.Stubs.Tactics.V2.Builtins.intro`, and gives it the given name. *)
let intro_as (s:string) : Tac binding =
    let b = intro () in
    rename_to b s

(*| Like `FStar.Tactics.V2.Derived.pose`, but gives the new hypothesis the
    given name. *)
let pose_as (s:string) (t:term) : Tac binding =
    let b = pose t in
    rename_to b s

(*| Runs a tactic on each binding of the first goal's context and returns
    the results. *)
let for_each_binding (f : binding -> Tac 'a) : Tac (list 'a) =
    map f (cur_vars ())

(*| Reverts as many binders of the first goal's context as there are
    elements in the list, moving them back into the goal.

    Only the length of the list is used: it calls
    `FStar.Stubs.Tactics.V2.Builtins.revert` once per element, which reverts
    the most recent binder each time, regardless of which bindings the list
    contains. *)
let rec revert_all (bs:list binding) : Tac unit =
    match bs with
    | [] -> ()
    | _::tl -> revert ();
             revert_all tl

(*| Returns the sort (type) of a binder. *)
let binder_sort (b : binder) : Tot typ = b.sort

// Cannot define this inside `assumption` due to #1091
private
let rec __assumption_aux (xs : list binding) : Tac unit =
    match xs with
    | [] ->
        fail "no assumption matches goal"
    | b::bs ->
        try exact b with | _ ->
        __assumption_aux bs

(*| Solves the first goal with a hypothesis from its context, trying each
    binding in turn with `FStar.Tactics.V2.Derived.exact`; fails with "no
    assumption matches goal" if none works.

    ```fstar
    let _ = assert (forall (p q : prop). p ==> q ==> p)
              by (let _ = l_intros () in
                  assumption ())
    ``` *)
let assumption () : Tac unit =
    __assumption_aux (cur_vars ())

(*| Recognizes a formula of the form `lhs ==> rhs` where `lhs` is an
    equality, returning the equality as a formula together with `rhs`, or
    `None` otherwise. *)
let destruct_equality_implication (t:term) : Tac (option (formula & term)) =
    match term_as_formula t with
    | Implies lhs rhs ->
        let lhs = term_as_formula' lhs in
        begin match lhs with
        | Comp (Eq _) _ _ -> Some (lhs, rhs)
        | _ -> None
        end
    | _ -> None

private
let __eq_sym #t (a b : t) : Lemma ((a == b) == (b == a)) =
  FStar.PropositionalExtensionality.apply (a==b) (b==a)

(*| Rewrites the first goal with a hypothesis that is an equality between a
    variable and a term, in either orientation (`v == e` or `e == v`),
    replacing the variable by the term; fails with "rewrite' failed"
    otherwise.

    See `FStar.Stubs.Tactics.V2.Builtins.rewrite`, which only handles
    `v == e`. *)
let rewrite' (x:binding) : Tac unit =
    ((fun () -> rewrite x)
     <|> (fun () -> var_retype x;
                    apply_lemma (`__eq_sym);
                    rewrite x)
     <|> (fun () -> fail "rewrite' failed"))
    ()

(*| Rewrites the first goal with the first binding of the list whose type is
    an equality `x == e` with left-hand side syntactically equal to the
    given term `x`; does nothing if there is none. *)
let rec try_rewrite_equality (x:term) (bs:list binding) : Tac unit =
    match bs with
    | [] -> ()
    | x_t::bs ->
        begin match term_as_formula (type_of_binding x_t) with
        | Comp (Eq _) y _ ->
            if term_eq x y
            then rewrite x_t
            else try_rewrite_equality x bs
        | _ ->
            try_rewrite_equality x bs
        end

(*| Tries to rewrite the first goal with each binding of the list in turn,
    ignoring those for which `FStar.Stubs.Tactics.V2.Builtins.rewrite`
    fails. *)
let rec rewrite_all_context_equalities (bs:list binding) : Tac unit =
    match bs with
    | [] -> ()
    | x_t::bs -> begin
        (try rewrite x_t with | _ -> ());
        rewrite_all_context_equalities bs
    end

(*| Tries to rewrite the first goal with every hypothesis of its context,
    ignoring those that are not usable equalities. *)
let rewrite_eqs_from_context () : Tac unit =
    rewrite_all_context_equalities (cur_vars ())

(*| Rewrites the first goal with the first hypothesis of its context that is
    an equality `t == e` for the given term `t`, replacing `t` by `e`; does
    nothing if there is none. *)
let rewrite_equality (t:term) : Tac unit =
    try_rewrite_equality t (cur_vars ())

(*| Unfolds a top-level definition everywhere in the first goal, given the
    definition's name as a term; fails if the term is not a top-level name.

    Uses `delta_fully` for that name only. *)
let unfold_def (t:term) : Tac unit =
    match inspect t with
    | Tv_FVar fv ->
        let n = implode_qn (inspect_fv fv) in
        norm [delta_fully [n]]
    | _ -> fail "unfold_def: term is not a fv"

(*| Rewrites the first goal left to right, bottom-up, with a list of lemmas
    stating equalities; each subterm is rewritten with the first lemma that
    applies, if any.

    The lemmas must prove propositional equalities, with `==`. The goal is
    traversed only once, so the result may still contain instances of the
    left-hand sides. Built on `FStar.Tactics.V2.Derived.pointwise` and
    `FStar.Tactics.V2.Derived.apply_lemma_rw`.

    ```fstar
    let double (x:int) : int = x + x
    let double_eq (x:int) : Lemma (double x == x + x) = ()

    let _ = assert (double 3 == 6) by (l_to_r [`double_eq]; trivial ())
    ``` *)
let l_to_r (lems:list term) : Tac unit =
    let first_or_trefl () : Tac unit =
        fold_left (fun k l () ->
                    (fun () -> apply_lemma_rw l)
                    `or_else` k)
                  trefl lems () in
    pointwise first_or_trefl

(*| Builds the term `squash t` from a term `t`. *)
let mk_squash (t : term) : Tot term =
    let sq : term = pack (Tv_FVar (pack_fv squash_qn)) in
    mk_e_app sq [t]

(*| Builds the term `squash (t1 == t2)` from two terms. *)
let mk_sq_eq (t1 t2 : term) : Tot term =
    let eq : term = pack (Tv_FVar (pack_fv eq2_qn)) in
    mk_squash (mk_e_app eq [t1; t2])

(*| Rewrites every occurrence of `t1` in the first goal into `t2`, adding a
    goal `t1 == t2`.

    An implementation of `FStar.Stubs.Tactics.V2.Builtins.grewrite` in terms
    of `FStar.Tactics.V2.Derived.pointwise`, kept for backwards
    compatibility; the primitive is likely a better choice. *)
let __grewrite_derived (t1 t2 : term) : Tac unit =
    let e = tcut (mk_sq_eq t1 t2) in
    let e = pack (Tv_Var e) in
    pointwise (fun () ->
      let (lhs, rhs) : term & term =
        match term_as_formula (cur_goal()) with
        | Comp (Eq _) lhs rhs ->
          lhs, rhs
        | _ ->
          raise SKIP
      in
      if Tv_Uvar? lhs then
        trefl () (* If the LHS is a uvar, do nothing, so we do not instantiate it. *)
      else if not (term_eq lhs t1) then
        raise SKIP
      else
        try exact e with | _ -> trefl ()
    )

private
let __un_sq_eq (#a:Type) (x y : a) (_ : squash (x == y)) : Lemma (x == y) = ()

(*| Rewrites every occurrence of `l` in the first goal into `r`, given a
    hypothesis of type `l == r` (possibly squashed) that discharges the
    equality; fails if the binding's type is not an equality.

    See `FStar.Stubs.Tactics.V2.Builtins.grewrite`. *)
let grewrite_eq (b:binding) : Tac unit =
  match term_as_formula (type_of_binding b) with
  | Comp (Eq _) l r ->
    grewrite l r;
    iseq [idtac; (fun () -> exact b)]
  | _ ->
    begin match term_as_formula' (type_of_binding b) with
    | Comp (Eq _) l r ->
      grewrite l r;
      iseq [idtac; (fun () -> apply_lemma (`__un_sq_eq);
                              exact b)]
    | _ ->
      fail "grewrite_eq: binder type is not an equality"
    end

private
let admit_dump_t () : Tac unit =
  dump "Admitting";
  apply (`admit)

(*| Like `admit ()`, but also dumps the proof state with its expected type
    (message "Admitting") when typechecking; use `admit_dump ()` to see what
    remains to be proved at that point.

    Unsafe: the expected type is admitted. See also
    `FStar.Tactics.V2.Derived.magic_dump`. *)
val admit_dump : #a:Type -> (#[admit_dump_t ()] x : (unit -> Tot (_:a{False}))) -> unit -> Tot (_:a{False})
let admit_dump #a #x () = x ()

private
let magic_dump_t () : Tac unit =
  dump "Admitting";
  (* [apply] fills in [magic]'s anonymous [unit] argument itself *)
  apply (`magic)

(*| Like `magic ()`, but also dumps the proof state with its expected type
    (message "Admitting") when typechecking; `magic_dump ()` produces a
    value of any type without proof.

    Unsafe. See also `FStar.Tactics.V2.Derived.admit_dump`. *)
val magic_dump : #a:Type -> (#[magic_dump_t ()] x : a) -> unit -> Tot a
let magic_dump #a #x () = x

(*| Replaces `t1` by `t2` in the first goal, provided `t1 == t2` holds by
    `FStar.Tactics.V2.Derived.trivial` (that is, by normalization); fails
    otherwise. *)
let change_with t1 t2 : Tac unit =
    focus (fun () ->
        grewrite t1 t2;
        iseq [idtac; trivial]
    )

(*| Changes the first goal to `squash t`, which must be convertible with the
    current goal.

    See `FStar.Stubs.Tactics.V2.Builtins.change`. *)
let change_sq (t1 : term) : Tac unit =
    change (mk_e_app (`squash) [t1])

(*| Runs a tactic and then fails with `finish_by: not finished` if any
    active goal remains; otherwise returns the tactic's result. *)
let finish_by (t : unit -> Tac 'a) : Tac 'a =
    let x = t () in
    or_else qed (fun () -> fail "finish_by: not finished");
    x

(*| Solves the first goal with `t1` (which must solve it completely), then
    runs `t2` on an equation between that solution and the goal's
    witness, closing it by `FStar.Tactics.V2.Derived.trefl`.

    This lets `t2` transform the term built by `t1`, for instance by
    normalizing it; see `FStar.Tactics.V2.Derived.specialize`. Built on
    `FStar.Stubs.Tactics.V2.Builtins.dup`. *)
let solve_then #a #b (t1 : unit -> Tac a) (t2 : a -> Tac b) : Tac b =
    dup ();
    let x = focus (fun () -> finish_by t1) in
    let y = t2 x in
    trefl ();
    y

(*| For a goal that is a list to build, applies `Cons`, solves the head
    completely with the given tactic, and leaves the tail as the next goal.

    Fails if the tactic does not solve the head. *)
let add_elem (t : unit -> Tac 'a) : Tac 'a = focus (fun () ->
    apply (`Cons);
    focus (fun () ->
      let x = t () in
      qed ();
      x
    )
  )

(*| Builds a tactic that synthesizes the term `f`, partially evaluated by
    unfolding the names in `l` (and reducing matches and recursion).

    Typically used with `synth_by_tactic`: specializing a recursive function
    `foo` applied to a known list, with `l` containing the fully qualified
    name of `foo`, defines a function in which the recursion on that list is
    unfolded. *)
let specialize (#a:Type) (f:a) (l:list string) :unit -> Tac unit
  = fun () -> solve_then (fun () -> exact (quote f)) (fun () -> norm [delta_only l; iota; zeta])

(* The [Tac unit] annotations here are not redundant: [fail] returns a refined
   [unit] now, so without them the inferred result type carries the [goals ()]
   match's postcondition as a refinement. *)
(*| Sets the label of the first goal, which is shown when the goal is
    displayed or reported; fails if there are no goals.

    See also `FStar.Tactics.V2.Derived.tlabel'`. *)
let tlabel (l:string) : Tac unit =
    match goals () with
    | [] -> fail "tlabel: no goals"
    | h::t ->
        set_goals (set_label l h :: t)

(*| Prefixes the label of the first goal with the given string; fails if
    there are no goals. *)
let tlabel' (l:string) : Tac unit =
    match goals () with
    | [] -> fail "tlabel': no goals"
    | h::t ->
        let h = set_label (l ^ get_label h) h in
        set_goals (h :: t)

(*| Moves all SMT goals to the end of the active goals, so that further
    tactics act on them. *)
let focus_all () : Tac unit =
    set_goals (goals () @ smt_goals ());
    set_smt_goals []

private
let rec extract_nth (n:nat) (l : list 'a) : option ('a & list 'a) =
  match n, l with
  | _, [] -> None
  | 0, hd::tl -> Some (hd, tl)
  | _, hd::tl -> begin
    match extract_nth (n-1) tl with
    | Some (hd', tl') -> Some (hd', hd::tl')
    | None -> None
  end

(*| Moves the `n`-th active goal (counting from 1) to the front; fails if
    there are fewer than `n` goals. *)
let bump_nth (n:pos) : Tac unit =
  // n-1 since goal numbering begins at 1
  match extract_nth (n - 1) (goals ()) with
  | None -> fail "bump_nth: not that many goals"
  | Some (h, t) -> set_goals (h :: t)

(*| Converts a term that is a list literal, built from `Cons` and `Nil`,
    into the list of its element terms; raises `NotAListLiteral` otherwise. *)
let rec destruct_list (t : term) : Tac (list term) =
    let head, args = collect_app t in
    match inspect head, args with
    | Tv_FVar fv, [(a1, Q_Explicit); (a2, Q_Explicit)]
    | Tv_FVar fv, [(_, Q_Implicit); (a1, Q_Explicit); (a2, Q_Explicit)] ->
      if inspect_fv fv = cons_qn
      then a1 :: destruct_list a2
      else raise NotAListLiteral
    | Tv_FVar fv, _ ->
      if inspect_fv fv = nil_qn
      then []
      else raise NotAListLiteral
    | _ ->
      raise NotAListLiteral

private let get_match_body () : Tac term =
  match unsquash_term (cur_goal ()) with
  | None -> fail ""
  | Some t -> match inspect_unascribe t with
             | Tv_Match sc _ _ -> sc
             | _ -> fail "Goal is not a match"

private let rec last (x : list 'a) : Tac 'a =
    match x with
    | [] -> fail "last: empty list"
    | [x] -> x
    | _::xs -> last xs

(*| For a goal that is a `match` (`match e with | p1 -> e1 ... | pn -> en`),
    does case analysis on `e`, producing one goal per constructor with an
    equation for `e` rewritten into the goal and the match reduced.

    Fails if the goal is not a squashed `match`. *)
let branch_on_match () : Tac unit =
    focus (fun () ->
      let x = get_match_body () in
      let _ = t_destruct x in
      iterAll (fun () ->
        let bs = repeat intro in
        let b = last bs in (* this one is the equality *)
        grewrite_eq b;
        norm [iota])
    )

(*| Returns a binding of the first goal's context by position: for
    `i >= 0` the `i`-th binding of `FStar.Tactics.V2.Derived.cur_vars`
    (counting from 0), for negative `i` counting from the end (`-1` is the
    last one).

    Fails with "not enough binders" if there is no such binding. *)
let nth_var (i:int) : Tac binding =
  let bs = cur_vars () in
  let k : int = if i >= 0 then i else List.Tot.Base.length bs + i in
  let k : nat = if k < 0 then fail "not enough binders" else k in
  match List.Tot.Base.nth bs k with
  | None -> fail "not enough binders"
  | Some b -> b

(*| Builds the abstraction `fun x1 ... xn -> t` from a list of binders and
    a body; returns the body unchanged when the list is empty. *)
let rec mk_abs (args : list binder) (t : term) : Tac term (decreases args) =
  match args with
  | [] -> t
  | a :: args' ->
    let t' = mk_abs args' t in
    pack (Tv_Abs a t')

// GGG Needed? delete if not
(*| Turns a named variable into an explicit binder with the same name,
    unique index and sort, and no attributes. *)
let namedv_to_simple_binder (n : namedv) : Tac simple_binder =
  let nv = inspect_namedv n in
  {
    ppname = nv.ppname;
    uniq   = nv.uniq;
    sort   = unseal nv.sort; (* GGG USINGSORT *)
    qual   = Q_Explicit;
    attrs  = [];
  }

(*| Turns a binding of the context into an explicit binder with the same
    name, unique index and sort; also available as a coercion. *)
[@@coercion]
let binding_to_simple_binder (b : binding) : Tot simple_binder =
  {
    ppname = b.ppname;
    uniq   = b.uniq;
    sort   = b.sort;
    qual   = Q_Explicit;
    attrs  = [];
  }

(*| Parses a string as a term in an environment extended with the given
    names, and wraps the result in `let` bindings defining each name as its
    given term.

    For `[(id1, t1); ...; (idn, tn)]` the string may refer to `id1` to
    `idn`. See `FStar.Stubs.Tactics.V2.Builtins.string_to_term`. *)
let string_to_term_with_lb
  (letbindings: list (string & term))
  (e: env) (t: string): Tac term
  = let e, lb_bindings : env & list (term & binding) =
      fold_left (fun (e, lb_bvs) (i, v) ->
        let e, b = push_bv_dsenv e i in
        e, (v, b)::lb_bvs
      ) (e, []) letbindings in
    let t = string_to_term e t in
    fold_left (fun t (i, b) ->
          pack (Tv_Let false [] (binding_to_simple_binder b) i t))
        t lb_bindings

private
val lem_trans : (#a:Type) -> (#x:a) -> (#z:a) -> (#y:a) ->
                    squash (x == y) -> squash (y == z) -> Lemma (x == z)
private
let lem_trans #a #x #z #y e1 e2 = ()

(*| Reduces a goal `x == z` to two goals `x == ?u` and `?u == z`, by
    transitivity of equality. *)
let trans () : Tac unit = apply_lemma (`lem_trans)

(*| Calls the SMT solver on the first goal right away, with the goal's
    current settings (fuel, rlimit, ...), and fails if it cannot be proved.

    See also `FStar.Tactics.V2.Derived.smt` (deferred) and
    `FStar.Tactics.V2.Derived.smt_sync'`. *)
let smt_sync () : Tac unit = t_smt_sync (get_vconfig ())

(*| Like `FStar.Tactics.V2.Derived.smt_sync`, but with the given fuel and
    ifuel, used as both the initial and maximum values. *)
let smt_sync' (fuel ifuel : nat) : Tac unit =
    let vcfg = get_vconfig () in
    let vcfg' = { vcfg with initial_fuel = fuel; max_fuel = fuel
                          ; initial_ifuel = ifuel; max_ifuel = ifuel }
    in
    t_smt_sync vcfg'

(* t_check_equiv wrappers. *)
(*| Checks whether two types are equivalent in an environment, allowing
    unfolding and SMT; returns an equivalence token if so, together with any
    issues raised.

    See `FStar.Tactics.V2.Derived.check_equiv_nosmt` and
    `FStar.Stubs.Tactics.V2.Builtins.t_check_equiv`. *)
let check_equiv       g t0 t1 = t_check_equiv true true g t0 t1
(*| Like `FStar.Tactics.V2.Derived.check_equiv`, but without SMT and
    without unfolding definitions. *)
let check_equiv_nosmt g t0 t1 = t_check_equiv false false g t0 t1
