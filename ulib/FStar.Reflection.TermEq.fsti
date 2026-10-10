module FStar.Reflection.TermEq

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Reflection.TermSpec

(* Auxiliary... would be good to move. *)
(*| Holds when a predicate holds of every element of a list.

    An auxiliary for `FStar.Reflection.TermEq`; `FStar.Reflection.TermEq.allP`
    is the variant usable in recursive definitions over a structure containing
    the list. *)
let rec allP0 #a (pred : a -> prop) (l : list a) : prop =
  match l with
  | [] -> True
  | x::xs -> pred x /\ allP0 pred xs

(*| Holds when a predicate holds of every element of a list contained in a structure `top`.

    The predicate need only be defined on values that precede `top`, which
    lets `allP` be used inside a structurally recursive definition over `top`,
    as in `FStar.Reflection.TermEq.faithful_univ`. Otherwise like
    `FStar.Reflection.TermEq.allP0`. *)
let rec allP #a #b (top:b) (pred : (x:a{x << top}) -> prop) (l : list a{l << top \/ l === top}) : prop =
  match l with
  | [] -> True
  | x::xs -> pred x /\ allP top pred xs

(*| Holds when an optional value is `None` or satisfies the predicate.

    `FStar.Reflection.TermEq.optP` is the variant usable in recursive
    definitions over a structure containing the option. *)
let optP0 #a (pred : a -> prop) (o : option a) : prop =
  match o with
  | None -> True
  | Some x -> pred x

(*| Holds when an optional value contained in a structure `top` is `None` or satisfies the predicate.

    The predicate need only be defined on values that precede `top`. Otherwise
    like `FStar.Reflection.TermEq.optP0`. *)
let optP #a #b (top:b) (pred : (x:a{x << top}) -> prop) (o : option a{o << top}) : prop =
  match o with
  | None -> True
  | Some x -> pred x
(* /Aux *)

(*| Holds of universes that contain no universe unification variable.

    For such universes, `FStar.Reflection.TermEq.univ_eq_dec` decides equality. *)
let rec faithful_univ (u : universe) : prop =
  match inspect_universe u with
  | Uv_Unif _ -> False (* We just forbid this *)

  | Uv_Unk
  | Uv_Zero
  | Uv_BVar _
  | Uv_Name _ -> True

  | Uv_Succ u -> faithful_univ u
  | Uv_Max us -> allP u faithful_univ us

(* Just a placeholder for now *)
(*| Holds of every constant; a placeholder for a future restriction on constants in faithful terms. *)
let faithful_const (c:vconst) : prop = True

let rec faithful (t:term) : prop =
  match inspect_ln t with
  | Tv_Var _
  | Tv_BVar _
  | Tv_FVar _
  | Tv_Unknown ->
    True

  | Tv_Const c ->
    faithful_const c

  | Tv_UInst f us ->
    allP t faithful_univ us

  | Tv_Unsupp -> False
  | Tv_App h a ->
    faithful h /\ faithful_arg a
  | Tv_Abs b t  ->
    faithful_binder b /\ faithful t
  | Tv_Arrow b c ->
    faithful_binder b /\ faithful_comp c
  | Tv_Type u ->
    faithful_univ u
  | Tv_Refine b phi ->
    faithful_binder b
     /\ faithful phi

  | Tv_Uvar n u -> False
  | Tv_Let r ats x e b ->
    faithful_attrs ats
     /\ faithful_binder x
     /\ faithful e
     /\ faithful b

  | Tv_Match sc o brs ->
    faithful sc
     /\ None? o // stopgap
     /\ allP t faithful_branch brs

  | Tv_AscribedT e ta tacopt eq ->
    faithful e
     /\ faithful ta
     /\ optP t faithful tacopt

  | Tv_AscribedC e c tacopt eq ->
    faithful e
     /\ faithful_comp c
     /\ optP t faithful tacopt

and faithful_arg (a : argv) : prop =
  faithful (fst a) /\ faithful_qual (snd a)

and faithful_qual (q:aqualv) : prop =
  match q with
  | Q_Implicit -> True
  | Q_Explicit -> True
  | Q_Equality -> True
  | Q_Meta m -> faithful m

and faithful_binder (b:binder) : prop =
  match inspect_binder b with
  | {sort=sort; qual=q; attrs=attrs} ->
    faithful sort /\ faithful_qual q /\ faithful_attrs attrs

and faithful_branch (b : branch) : prop =
  let (p, t) = b in
  faithful_pattern p /\ faithful t

and faithful_pattern (p : pattern) : prop =
  match p with
  | Pat_Constant c -> faithful_const c
  | Pat_Cons head univs subpats ->
    optP p (allP p faithful_univ) univs
     /\ allP p faithful_pattern_arg subpats

  (* non-binding bvs are always OK *)
  | Pat_Var _ _ -> True
  | Pat_Dot_Term None -> True
  | Pat_Dot_Term (Some t) -> faithful t

and faithful_pattern_arg (pb : pattern & bool) : prop =
  faithful_pattern (fst pb)

and faithful_attrs ats : prop =
  allP ats faithful ats

and faithful_comp c =
  let cv = inspect_comp c in
  faithful cv.result_typ /\ allP c faithful_flag cv.flags

and faithful_flag (f:cflag) : prop =
  match f with
  | SMTPAT t -> faithful t
  | DECREASES (Decreases_lex ts) -> allP f faithful ts
  | DECREASES (Decreases_wf rel e) -> faithful rel /\ faithful e

(*| Terms whose syntax can be compared exactly: no unification variables, no unsupported syntax, no `match` return annotations, and only faithful universes.

    `FStar.Reflection.TermEq.term_eq_dec` decides equality of denotations on
    such terms. *)
let faithful_term     = t:term{faithful t}
(*| Universes that contain no unification variable; see `FStar.Reflection.TermEq.faithful_univ`. *)
let faithful_universe = u:universe{faithful_univ u}

(*| Conservatively compares two terms: returns `true` only if they have the same denotation.

    The denotation (`FStar.Reflection.TermSpec.denote_term`) ignores data that
    does not matter to the type theory, such as ranges, pretty-printing names
    and sealed sorts. The comparison works on all terms, but may return `false`
    for terms with equal denotations, for instance when they contain
    unification variables or unsupported syntax. Runs natively as a plugin.
    `FStar.Reflection.TermEq.term_eq_dec` is exact on faithful terms, and
    `FStar.Reflection.TermEq.Simple.term_eq` is a lighter interface returning a
    plain boolean. *)
[@@plugin]
val term_eq (t1 t2 : term) : (b:bool{b ==> denote_term t1 == denote_term t2})

(*| Decides whether two faithful terms have the same denotation.

    On terms satisfying `FStar.Reflection.TermEq.faithful_term`, the result is
    `true` exactly when their `FStar.Reflection.TermSpec.denote_term` are
    equal. Runs natively as a plugin. See `FStar.Reflection.TermEq.term_eq`
    for arbitrary terms. *)
[@@plugin]
val term_eq_dec (t1 t2 : faithful_term) : (b:bool{b <==> denote_term t1 == denote_term t2})

(*| Conservatively compares two universes: returns `true` only if they are equal.

    Works on all universes, but may return `false` for equal ones, for instance
    when they contain unification variables. Runs natively as a plugin. See
    `FStar.Reflection.TermEq.univ_eq_dec`. *)
[@@plugin]
val univ_eq (u1 u2 : universe) : (b:bool{b ==> u1 == u2})

(*| Decides equality of two faithful universes.

    On universes satisfying `FStar.Reflection.TermEq.faithful_universe`, the
    result is `true` exactly when they are equal. Runs natively as a plugin. *)
[@@plugin]
val univ_eq_dec (u1 u2 : faithful_universe) : (b:bool{b <==> u1 == u2})
