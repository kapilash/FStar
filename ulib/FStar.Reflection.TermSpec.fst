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
module FStar.Reflection.TermSpec

(* Erasable "spec" model of reflection terms. These types mirror the
   reflected AST but drop all data that is irrelevant to F*'s type theory
   (ranges, pretty-print names, sealed sorts, unification metadata). The
   functions [denote_term] and friends map a concrete (abstract) term to
   its spec model, ignoring that irrelevant data.

   The point is that a [term_spec] is a plain, recursive, erasable
   inductive that can be matched on structurally, without going through
   [inspect_ln]. This is intended to be the vocabulary in which
   Reflection.Typing states its rules, so that type-correctness proofs
   never need to reason about ranges, names, etc. *)

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins
module L = FStar.List.Tot

(* Universes are independent of terms, so their spec type is standalone. *)
(*| Erasable spec model of reflected universes, with no range or name data
    beyond what the type theory needs.

    It mirrors `FStar.Stubs.Reflection.V2.Data.universe_view`, but recursively,
    so it can be matched structurally without calling
    `FStar.Stubs.Reflection.V2.Builtins.inspect_universe`. The constructors are:

    - `Us_Zero`, the universe zero
    - `Us_Succ u`, the successor of `u`
    - `Us_Max us`, the maximum of the list `us`
    - `Us_BVar n`, a bound universe variable with de Bruijn index `n`
    - `Us_Name n`, a named universe variable
    - `Us_Unif uv`, a universe unification variable
    - `Us_Unk`, an unknown universe

    The type is `erasable` and `noeq`. `FStar.Reflection.TermSpec.denote_universe`
    computes the spec of a concrete universe. *)
[@@erasable]
noeq
type universe_spec =
  | Us_Zero : universe_spec
  | Us_Succ : universe_spec -> universe_spec
  | Us_Max  : list universe_spec -> universe_spec
  | Us_BVar : nat -> universe_spec
  | Us_Name : univ_name -> universe_spec
  | Us_Unif : universe_uvar -> universe_spec
  | Us_Unk  : universe_spec

(* The mutually-recursive spec model of terms, comps, binders,
   qualifiers and patterns. *)
(*| Erasable spec model of reflected terms, the vocabulary in which typing
    rules can be stated without reasoning about ranges or names.

    `term_spec` and its companion types mirror the reflected syntax of
    `FStar.Stubs.Reflection.V2.Data` but drop data irrelevant to the type
    theory: ranges, pretty-printing names, sealed sorts, binder attributes and
    unification metadata. Unlike `FStar.Stubs.Reflection.Types.term`, they are
    plain inductives that can be matched on and recursed over structurally,
    without going through `FStar.Stubs.Reflection.V2.Builtins.inspect_ln`. All
    are `erasable` and `noeq`. The concrete-to-spec map is the mutually
    recursive `denote_term` family of this module (`denote_term`,
    `denote_binder`, `denote_comp`, `denote_pattern` and friends).

    The constructors of `term_spec` follow `FStar.Stubs.Reflection.V2.Data.term_view`:

    - `Ts_Var uniq`, a free (named) variable, kept only by its unique number
    - `Ts_BVar index`, a bound variable by de Bruijn index
    - `Ts_FVar nm` and `Ts_UInst nm us`, top-level names, without and with universes
    - `Ts_App hd arg q`, an application to one argument with qualifier `q`
    - `Ts_Abs b body` and `Ts_Arrow b c`, abstractions and arrows
    - `Ts_Type u`, a universe of types
    - `Ts_Refine sort ref`, a refinement keeping only the binder sort
    - `Ts_Const c`, a constant
    - `Ts_Uvar n`, a unification variable, kept only by its number
    - `Ts_Let recf attrs sort def body`, a let binding keeping only the binder sort
    - `Ts_Match scrutinee ret brs`, a match with optional return annotation
    - `Ts_AscribedT` and `Ts_AscribedC`, type and computation-type ascriptions
    - `Ts_Unknown` and `Ts_Unsupp`, the unknown term and unsupported syntax

    The companion types defined together with it are:

    - `aqualv_spec`, argument qualifiers: `Qs_Implicit`, `Qs_Explicit`, `Qs_Equality` and `Qs_Meta t`
    - `binder_spec`, a binder `Bs sort qual`, without name or attributes
    - `decreases_order_spec`, `Ds_lex ts` or `Ds_wf rel e`
    - `cflag_spec`, computation flags `Fs_SMTPAT t` and `Fs_DECREASES d`
    - `comp_spec`, a computation type `Cs eff_name result flags`
    - `pattern_spec`, patterns `Ps_Constant`, `Ps_Cons`, `Ps_Var` and `Ps_Dot_Term`

    A `comp_spec` does not record the source effect name, which is presentation
    only. `Ps_Var` carries nothing, since all pattern variables are provably
    equal in the spec. *)
[@@erasable]
noeq
type term_spec =
  | Ts_Var    : uniq:nat -> term_spec
  | Ts_BVar   : index:nat -> term_spec
  | Ts_FVar   : nm:name -> term_spec
  | Ts_UInst  : nm:name -> us:list universe_spec -> term_spec
  | Ts_App    : hd:term_spec -> arg:term_spec -> q:aqualv_spec -> term_spec
  | Ts_Abs    : b:binder_spec -> body:term_spec -> term_spec
  | Ts_Arrow  : b:binder_spec -> c:comp_spec -> term_spec
  | Ts_Type   : u:universe_spec -> term_spec
  | Ts_Refine : sort:term_spec -> ref:term_spec -> term_spec
  | Ts_Const  : c:vconst -> term_spec
  | Ts_Uvar   : n:nat -> term_spec
  | Ts_Let    : recf:bool ->
                attrs:list term_spec ->
                sort:term_spec ->
                def:term_spec ->
                body:term_spec ->
                term_spec
  | Ts_Match  : scrutinee:term_spec ->
                ret:option (binder_spec & (either term_spec comp_spec & option term_spec & bool)) ->
                brs:list (pattern_spec & term_spec) ->
                term_spec
  | Ts_AscribedT : e:term_spec -> t:term_spec -> tac:option term_spec -> use_eq:bool -> term_spec
  | Ts_AscribedC : e:term_spec -> c:comp_spec -> tac:option term_spec -> use_eq:bool -> term_spec
  | Ts_Unknown : term_spec
  | Ts_Unsupp  : term_spec

and aqualv_spec =
  | Qs_Implicit : aqualv_spec
  | Qs_Explicit : aqualv_spec
  | Qs_Equality : aqualv_spec
  | Qs_Meta     : term_spec -> aqualv_spec

(* A binder in the spec model keeps only its sort and qualifier; the
   pretty-print name and attributes are irrelevant to the type theory. *)
and binder_spec =
  | Bs : sort:term_spec -> qual:aqualv_spec -> binder_spec

and decreases_order_spec =
  | Ds_lex : list term_spec -> decreases_order_spec
  | Ds_wf  : term_spec -> term_spec -> decreases_order_spec

and cflag_spec =
  | Fs_SMTPAT    : term_spec -> cflag_spec
  | Fs_DECREASES : decreases_order_spec -> cflag_spec

(* Mirrors [comp_view].  [source_effect_name] is presentation only and has no
bearing on the type theory, so it is not recorded here. *)
and comp_spec =
  | Cs : eff_name : name ->
         result   : term_spec ->
         flags    : list cflag_spec ->
         comp_spec

(* All [Pat_Var]s are provably equal, so [Ps_Var] carries nothing. *)
and pattern_spec =
  | Ps_Constant : vconst -> pattern_spec
  | Ps_Cons     : head:name ->
                  univs:option (list universe_spec) ->
                  subpats:list (pattern_spec & bool) ->
                  pattern_spec
  | Ps_Var      : pattern_spec
  | Ps_Dot_Term : option term_spec -> pattern_spec

(* -------------------------------------------------------------------- *)
(* Termination helpers: decreasing map/option over a bounded structure.
   These mirror [list_dec_cmp]/[opt_dec_cmp] in FStar.Reflection.TermEq. *)

(*| Maps a ghost function over a list whose elements precede a bound `top`.

    The refinement `x << top` passed to `f` lets recursive denotations (such as
    `FStar.Reflection.TermSpec.denote_universe`) recurse through a list of
    subterms while proving termination on `top`. It mirrors the decreasing list
    helpers of `FStar.Reflection.TermEq`. *)
let rec map_dec (#a:Type u#aa) (#b:Type u#bb) (#tb:Type u#tt)
                (top:tb) (f : (x:a{x << top} -> b)) (l:list a{l << top})
  : GTot (list b) (decreases l)
  = match l with
    | [] -> []
    | x::xs -> f x :: map_dec top f xs

(*| Maps a ghost function over an option whose content precedes a bound `top`.

    The option counterpart of `FStar.Reflection.TermSpec.map_dec`, for
    recursion through an optional subterm. *)
let opt_dec (#a:Type u#aa) (#b:Type u#bb) (#tb:Type u#tt)
            (top:tb) (f : (x:a{x << top} -> b)) (o:option a{o << top})
  : GTot (option b)
  = match o with
    | None -> None
    | Some x -> Some (f x)

(* -------------------------------------------------------------------- *)
(* Universes: standalone recursion via inspect_universe. *)

(*| Computes the spec model of a reflected universe.

    It recurses structurally through
    `FStar.Stubs.Reflection.V2.Builtins.inspect_universe`, mapping each
    constructor of `FStar.Stubs.Reflection.V2.Data.universe_view` to the
    corresponding constructor of `FStar.Reflection.TermSpec.universe_spec`. *)
let rec denote_universe (u:universe) : Tot universe_spec (decreases u) =
  match inspect_universe u with
  | Uv_Zero    -> Us_Zero
  | Uv_Succ u' -> Us_Succ (denote_universe u')
  | Uv_Max  us -> Us_Max (map_dec u denote_universe us)
  | Uv_BVar n  -> Us_BVar n
  | Uv_Name n  -> Us_Name n
  | Uv_Unif uv -> Us_Unif uv
  | Uv_Unk     -> Us_Unk

(*| Computes the spec models of a list of universes, with
    `FStar.Reflection.TermSpec.denote_universe` on each element. *)
let denote_universes (us:list universe) : GTot (list universe_spec) =
  L.map denote_universe us

(* -------------------------------------------------------------------- *)
(* The main denotation: a total, structural map from terms to specs. *)

let rec denote_term (t:term) : Tot term_spec (decreases t) =
  match inspect_ln t with
  | Tv_Var v      -> Ts_Var (inspect_namedv v).uniq
  | Tv_BVar v     -> Ts_BVar (inspect_bv v).index
  | Tv_FVar f     -> Ts_FVar (inspect_fv f)
  | Tv_UInst f us -> Ts_UInst (inspect_fv f) (denote_universes us)
  | Tv_App hd a   -> Ts_App (denote_term hd) (denote_term (fst a)) (denote_aqualv (snd a))
  | Tv_Abs b body -> Ts_Abs (denote_binder b) (denote_term body)
  | Tv_Arrow b c  -> Ts_Arrow (denote_binder b) (denote_comp c)
  | Tv_Type u     -> Ts_Type (denote_universe u)
  | Tv_Refine sb r -> Ts_Refine (denote_term (inspect_binder sb).sort) (denote_term r)
  | Tv_Const c    -> Ts_Const c
  | Tv_Uvar n _   -> Ts_Uvar n
  | Tv_Let recf attrs sb def body ->
    Ts_Let recf (denote_terms attrs)
                (denote_term (inspect_binder sb).sort)
                (denote_term def)
                (denote_term body)
  | Tv_Match sc ret brs ->
    Ts_Match (denote_term sc) (denote_ret ret) (denote_branches brs)
  | Tv_AscribedT e ta tac eq ->
    Ts_AscribedT (denote_term e) (denote_term ta) (denote_opt_term tac) eq
  | Tv_AscribedC e c tac eq ->
    Ts_AscribedC (denote_term e) (denote_comp c) (denote_opt_term tac) eq
  | Tv_Unknown -> Ts_Unknown
  | Tv_Unsupp  -> Ts_Unsupp

and denote_terms (ts:list term) : GTot (list term_spec) (decreases ts) =
  match ts with
  | [] -> []
  | t::ts -> denote_term t :: denote_terms ts

and denote_aqualv (q:aqualv) : Tot aqualv_spec (decreases q) =
  match q with
  | Q_Implicit -> Qs_Implicit
  | Q_Explicit -> Qs_Explicit
  | Q_Equality -> Qs_Equality
  | Q_Meta m   -> Qs_Meta (denote_term m)

and denote_binder (b:binder) : Tot binder_spec (decreases b) =
  let bv = inspect_binder b in
  Bs (denote_term bv.sort) (denote_aqualv bv.qual)

and denote_comp (c:comp) : Tot comp_spec (decreases c) =
  let cv = inspect_comp c in
  Cs cv.effect_name (denote_term cv.result_typ) (denote_flags cv.flags)

and denote_flags (fs:list cflag) : Tot (list cflag_spec) (decreases fs) =
  match fs with
  | [] -> []
  | f::fs -> denote_flag f :: denote_flags fs

and denote_flag (f:cflag) : Tot cflag_spec (decreases f) =
  match f with
  | SMTPAT t -> Fs_SMTPAT (denote_term t)
  | DECREASES d -> Fs_DECREASES (denote_decreases_order d)

and denote_decreases_order (d:decreases_order) : Tot decreases_order_spec (decreases d) =
  match d with
  | Decreases_lex ts -> Ds_lex (denote_terms ts)
  | Decreases_wf rel e -> Ds_wf (denote_term rel) (denote_term e)

and denote_args (a:list argv) : GTot (list (term_spec & aqualv_spec)) (decreases a) =
  match a with
  | [] -> []
  | (t,q)::a -> (denote_term t, denote_aqualv q) :: denote_args a

and denote_opt_term (o:option term) : GTot (option term_spec) (decreases o) =
  match o with
  | None -> None
  | Some t -> Some (denote_term t)

and denote_ret (o:option match_returns_ascription)
  : GTot (option (binder_spec & (either term_spec comp_spec & option term_spec & bool)))
        (decreases o) =
  match o with
  | None -> None
  | Some (b, (Inl t, tacopt, eq)) ->
    Some (denote_binder b, (Inl (denote_term t), denote_opt_term tacopt, eq))
  | Some (b, (Inr c, tacopt, eq)) ->
    Some (denote_binder b, (Inr (denote_comp c), denote_opt_term tacopt, eq))

and denote_branches (brs:list branch) : GTot (list (pattern_spec & term_spec)) (decreases brs) =
  match brs with
  | [] -> []
  | (p,t)::brs -> (denote_pattern p, denote_term t) :: denote_branches brs

and denote_pattern (p:pattern) : Tot pattern_spec (decreases p) =
  match p with
  | Pat_Constant c -> Ps_Constant c
  | Pat_Cons head univs subpats ->
    Ps_Cons (inspect_fv head)
            (match univs with None -> None | Some us -> Some (denote_universes us))
            (denote_subpats subpats)
  | Pat_Var _ _ -> Ps_Var
  | Pat_Dot_Term o -> Ps_Dot_Term (denote_opt_term o)

and denote_subpats (ps:list (pattern & bool)) : GTot (list (pattern_spec & bool)) (decreases ps) =
  match ps with
  | [] -> []
  | (p,b)::ps -> (denote_pattern p, b) :: denote_subpats ps

(* -------------------------------------------------------------------- *)
(* Computation lemmas: the denotation of a packed view. These are the
   rewrites that let Reflection.Typing reason about the spec of a term it
   builds with [pack_ln]. They rely only on [inspect_pack_inv], which
   remains valid. *)

(*| The spec denotation of a term built with `Tv_Var v`: `Ts_Var` of the unique number of `v`.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_var (v:namedv)
  : Lemma (denote_term (pack_ln (Tv_Var v)) == Ts_Var (inspect_namedv v).uniq)
  = inspect_pack_inv (Tv_Var v)

(*| The spec denotation of a term built with `Tv_BVar v`: `Ts_BVar` of the de Bruijn index of `v`.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_bvar (v:bv)
  : Lemma (denote_term (pack_ln (Tv_BVar v)) == Ts_BVar (inspect_bv v).index)
  = inspect_pack_inv (Tv_BVar v)

(*| The spec denotation of a term built with `Tv_FVar f`: `Ts_FVar` of the name of `f`.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_fvar (f:fv)
  : Lemma (denote_term (pack_ln (Tv_FVar f)) == Ts_FVar (inspect_fv f))
  = inspect_pack_inv (Tv_FVar f)

(*| The spec denotation of a term built with `Tv_UInst f us`: `Ts_UInst` of the name of `f` and the denoted universes.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_uinst (f:fv) (us:universes)
  : Lemma (denote_term (pack_ln (Tv_UInst f us)) == Ts_UInst (inspect_fv f) (denote_universes us))
  = inspect_pack_inv (Tv_UInst f us)

(*| The spec denotation of a term built with `Tv_App hd a`: `Ts_App` of the denoted head, argument and qualifier.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_app (hd:term) (a:argv)
  : Lemma (denote_term (pack_ln (Tv_App hd a)) ==
           Ts_App (denote_term hd) (denote_term (fst a)) (denote_aqualv (snd a)))
  = inspect_pack_inv (Tv_App hd a)

(*| The spec denotation of a term built with `Tv_Abs b body`: `Ts_Abs` of the denoted binder and body.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_abs (b:binder) (body:term)
  : Lemma (denote_term (pack_ln (Tv_Abs b body)) == Ts_Abs (denote_binder b) (denote_term body))
  = inspect_pack_inv (Tv_Abs b body)

(*| The spec denotation of a term built with `Tv_Arrow b c`: `Ts_Arrow` of the denoted binder and computation type.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_arrow (b:binder) (c:comp)
  : Lemma (denote_term (pack_ln (Tv_Arrow b c)) == Ts_Arrow (denote_binder b) (denote_comp c))
  = inspect_pack_inv (Tv_Arrow b c)

(*| The spec denotation of a term built with `Tv_Type u`: `Ts_Type` of the denoted universe.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_type (u:universe)
  : Lemma (denote_term (pack_ln (Tv_Type u)) == Ts_Type (denote_universe u))
  = inspect_pack_inv (Tv_Type u)

(*| The spec denotation of a term built with `Tv_Refine sb r`: `Ts_Refine` of the denoted binder sort and refinement.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_refine (sb:simple_binder) (r:term)
  : Lemma (denote_term (pack_ln (Tv_Refine sb r)) ==
           Ts_Refine (denote_term (inspect_binder sb).sort) (denote_term r))
  = inspect_pack_inv (Tv_Refine sb r)

(*| The spec denotation of a term built with `Tv_Const c`: `Ts_Const c`.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_const (c:vconst)
  : Lemma (denote_term (pack_ln (Tv_Const c)) == Ts_Const c)
  = inspect_pack_inv (Tv_Const c)

(*| The spec denotation of a term built with `Tv_Uvar n ctx`: `Ts_Uvar n`, forgetting the context and substitution.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_uvar (n:nat) (ctx:ctx_uvar_and_subst)
  : Lemma (denote_term (pack_ln (Tv_Uvar n ctx)) == Ts_Uvar n)
  = inspect_pack_inv (Tv_Uvar n ctx)

(*| The spec denotation of a term built with `Tv_Match sc ret brs`: `Ts_Match` of the denoted scrutinee, return annotation and branches.

    A rewrite for reasoning about the spec of a term built with
    `FStar.Stubs.Reflection.V2.Builtins.pack_ln`, proved from
    `FStar.Stubs.Reflection.V2.Builtins.inspect_pack_inv`. It has no SMT
    pattern, so call it explicitly. *)
let denote_pack_match (sc:term) (ret:option match_returns_ascription) (brs:list branch)
  : Lemma (denote_term (pack_ln (Tv_Match sc ret brs)) ==
           Ts_Match (denote_term sc) (denote_ret ret) (denote_branches brs))
  = inspect_pack_inv (Tv_Match sc ret brs)

(* -------------------------------------------------------------------- *)
(* Spec-level (ghost) substitution on [term_spec]. This mirrors
   [FStar.Reflection.Typing.subst_term] exactly, but operates structurally
   on the [term_spec] inductive with no [inspect_ln]/[pack_ln]. The
   connecting lemma [denote_subst_term] (below) relates the two.

   Fidelity note: the concrete [subst_term] never descends into an
   [aqualv] (it keeps [snd argv]) nor into a binder's qualifier, so the
   spec mirror leaves [aqualv_spec] and the [qual] field untouched. *)

(*| One element of a spec-level substitution on
    `FStar.Reflection.TermSpec.term_spec`.

    The constructors mirror `DT`, `NT` and `ND` of `FStar.Reflection.Typing.subst_elt`:

    - `DTs i t` replaces the bound variable with de Bruijn index `i` by `t`
    - `NTs x t` replaces the free variable with unique number `x` by `t`
    - `NDs x i` replaces the free variable `x` by the bound index `i`, closing over it *)
[@@erasable]
noeq
type subst_spec_elt =
  | DTs : nat -> term_spec -> subst_spec_elt
  | NTs : nat -> term_spec -> subst_spec_elt
  | NDs : nat -> nat -> subst_spec_elt

(*| Shifts the de Bruijn indices in a substitution element by `n`, for use
    under `n` additional binders.

    `DTs` and `NDs` have their index increased; `NTs` is unchanged. Mirrors
    `FStar.Reflection.Typing.shift_subst_elt`. *)
let shift_subst_spec_elt (n:nat) = function
  | DTs i t -> DTs (i + n) t
  | NTs x t -> NTs x t
  | NDs x i -> NDs x (i + n)

(*| A spec-level substitution: an erased list of
    `FStar.Reflection.TermSpec.subst_spec_elt`, applied by `subst_term_spec`.

    Mirrors `FStar.Reflection.Typing.subst`. *)
let subst_spec = Ghost.erased (list subst_spec_elt)

(*| Shifts every element of a substitution by `n`, for use under `n` additional
    binders.

    Mirrors `FStar.Reflection.Typing.shift_subst_n`. *)
let shift_subst_spec_n (n:nat) (s:subst_spec) : subst_spec = L.map (shift_subst_spec_elt n) s

(*| Shifts a substitution by one, for use under one additional binder.

    The same as `FStar.Reflection.TermSpec.shift_subst_spec_n 1`. *)
let shift_subst_spec = shift_subst_spec_n 1

(*| Returns `Some k` when the term is the free variable `Ts_Var k`, and `None`
    otherwise. *)
let maybe_uniq_of_spec (ts:term_spec) : GTot (option nat) =
  match ts with
  | Ts_Var k -> Some k
  | _ -> None

(*| Finds the first `DTs i t` element of a substitution for the de Bruijn
    index `i`, or `None` if there is none. *)
let rec find_matching_subst_spec_elt_bv (s:subst_spec) (i:nat) : GTot (option subst_spec_elt) =
  match s with
  | [] -> None
  | (DTs j t)::ss ->
    if j = i then Some (DTs j t) else find_matching_subst_spec_elt_bv ss i
  | _::ss -> find_matching_subst_spec_elt_bv ss i

(*| Applies a substitution to the bound variable with de Bruijn index `i`.

    If the substitution has a `DTs i t` element (the first one is used), the
    result is `t`; otherwise the variable `Ts_BVar i` is left unchanged.
    Mirrors `FStar.Reflection.Typing.subst_db`. *)
let subst_db_spec (i:nat) (s:subst_spec) : GTot term_spec =
  match find_matching_subst_spec_elt_bv s i with
  | Some (DTs _ t) ->
    (match maybe_uniq_of_spec t with
     | None -> t
     | Some k -> Ts_Var k)
  | _ -> Ts_BVar i

(*| Finds the first `NTs` or `NDs` element of a substitution for the free
    variable with unique number `uniq`, or `None` if there is none. *)
let rec find_matching_subst_spec_elt_var (s:subst_spec) (uniq:nat) : GTot (option subst_spec_elt) =
  match s with
  | [] -> None
  | (NTs y _)::rest
  | (NDs y _)::rest ->
    if y = uniq then Some (L.hd s) else find_matching_subst_spec_elt_var rest uniq
  | _::rest -> find_matching_subst_spec_elt_var rest uniq

(*| Applies a substitution to the free variable with unique number `uniq`.

    The first `NTs` or `NDs` element for `uniq` decides: `NTs uniq t` gives
    `t`, and `NDs uniq i` gives the bound variable `Ts_BVar i`. Otherwise the
    variable `Ts_Var uniq` is left unchanged. Mirrors
    `FStar.Reflection.Typing.subst_var`. *)
let subst_var_spec (uniq:nat) (s:subst_spec) : GTot term_spec =
  match find_matching_subst_spec_elt_var s uniq with
  | Some (NTs _ t) ->
    (match maybe_uniq_of_spec t with
     | None -> t
     | Some k -> Ts_Var k)
  | Some (NDs _ i) -> Ts_BVar i
  | _ -> Ts_Var uniq

let rec binder_offset_patterns_spec (ps:list (pattern_spec & bool))
  : GTot nat
  = match ps with
    | [] -> 0
    | (p, _)::ps ->
      binder_offset_pattern_spec p + binder_offset_patterns_spec ps

and binder_offset_pattern_spec (p:pattern_spec)
  : GTot nat
  = match p with
    | Ps_Constant _
    | Ps_Dot_Term _ -> 0
    | Ps_Var -> 1
    | Ps_Cons _ _ subpats -> binder_offset_patterns_spec subpats

let rec subst_term_spec (t:term_spec) (ss:subst_spec)
  : GTot term_spec (decreases t)
  = match t with
    | Ts_FVar _
    | Ts_UInst _ _
    | Ts_Type _
    | Ts_Const _
    | Ts_Uvar _
    | Ts_Unknown
    | Ts_Unsupp -> t

    | Ts_Var uniq -> subst_var_spec uniq ss
    | Ts_BVar j   -> subst_db_spec j ss

    | Ts_App hd arg q ->
      Ts_App (subst_term_spec hd ss) (subst_term_spec arg ss) q

    | Ts_Abs b body ->
      Ts_Abs (subst_binder_spec b ss) (subst_term_spec body (shift_subst_spec ss))

    | Ts_Arrow b c ->
      Ts_Arrow (subst_binder_spec b ss) (subst_comp_spec c (shift_subst_spec ss))

    | Ts_Refine sort ref ->
      Ts_Refine (subst_term_spec sort ss) (subst_term_spec ref (shift_subst_spec ss))

    | Ts_Let recf attrs sort def body ->
      Ts_Let recf
             (subst_terms_spec attrs ss)
             (subst_term_spec sort ss)
             (if recf then subst_term_spec def (shift_subst_spec ss)
              else subst_term_spec def ss)
             (subst_term_spec body (shift_subst_spec ss))

    | Ts_Match scr ret brs ->
      Ts_Match (subst_term_spec scr ss)
               (subst_ret_spec ret ss)
               (subst_branches_spec brs ss)

    | Ts_AscribedT e ta tac eq ->
      Ts_AscribedT (subst_term_spec e ss)
                   (subst_term_spec ta ss)
                   (subst_opt_term_spec tac ss)
                   eq

    | Ts_AscribedC e c tac eq ->
      Ts_AscribedC (subst_term_spec e ss)
                   (subst_comp_spec c ss)
                   (subst_opt_term_spec tac ss)
                   eq

and subst_binder_spec (b:binder_spec) (ss:subst_spec)
  : GTot binder_spec (decreases b)
  = let Bs sort qual = b in
    Bs (subst_term_spec sort ss) qual

and subst_comp_spec (c:comp_spec) (ss:subst_spec)
  : GTot comp_spec (decreases c)
  = let Cs eff res flags = c in
    Cs eff (subst_term_spec res ss) (subst_flags_spec flags ss)

and subst_flags_spec (fs:list cflag_spec) (ss:subst_spec)
  : GTot (list cflag_spec) (decreases fs)
  = match fs with
    | [] -> []
    | f::fs -> subst_flag_spec f ss :: subst_flags_spec fs ss

and subst_flag_spec (f:cflag_spec) (ss:subst_spec)
  : GTot cflag_spec (decreases f)
  = match f with
    | Fs_SMTPAT t -> Fs_SMTPAT (subst_term_spec t ss)
    | Fs_DECREASES (Ds_lex ts) -> Fs_DECREASES (Ds_lex (subst_terms_spec ts ss))
    | Fs_DECREASES (Ds_wf rel e) ->
      Fs_DECREASES (Ds_wf (subst_term_spec rel ss) (subst_term_spec e ss))

and subst_terms_spec (ts:list term_spec) (ss:subst_spec)
  : GTot (list term_spec) (decreases ts)
  = match ts with
    | [] -> []
    | t::ts -> subst_term_spec t ss :: subst_terms_spec ts ss

and subst_args_spec (ts:list (term_spec & aqualv_spec)) (ss:subst_spec)
  : GTot (list (term_spec & aqualv_spec)) (decreases ts)
  = match ts with
    | [] -> []
    | (t,q)::ts -> (subst_term_spec t ss, q) :: subst_args_spec ts ss

and subst_opt_term_spec (o:option term_spec) (ss:subst_spec)
  : GTot (option term_spec) (decreases o)
  = match o with
    | None -> None
    | Some t -> Some (subst_term_spec t ss)

and subst_ret_spec (o:option (binder_spec & (either term_spec comp_spec & option term_spec & bool)))
                   (ss:subst_spec)
  : GTot (option (binder_spec & (either term_spec comp_spec & option term_spec & bool)))
        (decreases o)
  = match o with
    | None -> None
    | Some (b, (Inl t, as_, eq)) ->
      Some (subst_binder_spec b ss,
            (Inl (subst_term_spec t (shift_subst_spec ss)),
             subst_opt_term_spec_shift as_ ss,
             eq))
    | Some (b, (Inr c, as_, eq)) ->
      Some (subst_binder_spec b ss,
            (Inr (subst_comp_spec c (shift_subst_spec ss)),
             subst_opt_term_spec_shift as_ ss,
             eq))

and subst_opt_term_spec_shift (o:option term_spec) (ss:subst_spec)
  : GTot (option term_spec) (decreases o)
  = match o with
    | None -> None
    | Some t -> Some (subst_term_spec t (shift_subst_spec ss))

and subst_branches_spec (brs:list (pattern_spec & term_spec)) (ss:subst_spec)
  : GTot (list (pattern_spec & term_spec)) (decreases brs)
  = match brs with
    | [] -> []
    | br::brs -> subst_branch_spec br ss :: subst_branches_spec brs ss

and subst_branch_spec (br:(pattern_spec & term_spec)) (ss:subst_spec)
  : GTot (pattern_spec & term_spec) (decreases br)
  = let p, t = br in
    let p = subst_pattern_spec p ss in
    let j = binder_offset_pattern_spec p in
    p, subst_term_spec t (shift_subst_spec_n j ss)

and subst_pattern_spec (p:pattern_spec) (ss:subst_spec)
  : GTot pattern_spec (decreases p)
  = match p with
    | Ps_Constant _ -> p
    | Ps_Var -> p
    | Ps_Cons head us pats -> Ps_Cons head us (subst_patterns_spec pats ss)
    | Ps_Dot_Term o -> Ps_Dot_Term (subst_opt_term_spec o ss)

and subst_patterns_spec (ps:list (pattern_spec & bool)) (ss:subst_spec)
  : GTot (list (pattern_spec & bool)) (decreases ps)
  = match ps with
    | [] -> ps
    | (p, b)::ps ->
      let n = binder_offset_pattern_spec p in
      let p = subst_pattern_spec p ss in
      let ps = subst_patterns_spec ps (shift_subst_spec_n n ss) in
      (p,b)::ps
