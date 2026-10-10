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
module FStar.Reflection.V2.Derived.Lemmas

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Builtins
open FStar.Stubs.Reflection.V2.Data
open FStar.Reflection.V2.Collect
open FStar.List.Tot

(*| Holds when `p` holds of every element of a list, defined by recursion on
    the list as an iterated conjunction.

    See `FStar.Reflection.V2.Derived.Lemmas.forallP` for the version stated
    with membership. *)
let rec forall_list (p:'a -> prop) (l:list 'a) : prop =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

(*| Holds when `p` holds of every member of a list, stated as
    `forall x. memP x l ==> p x`. *)
let forallP (p: 'a -> prop) (l: list 'a): prop
  = forall (x: 'a). memP x l ==> p x
(*| Holds when every element of the list `l` precedes `r` in the well-founded
    order `<<`, as in `l <<: r`.

    Used to state that the pieces returned by the collection functions of
    `FStar.Reflection.V2.Collect` are smaller than the term they came from. *)
unfold let (<<:) (l: list 'a) (r: 'r)
  = forallP (fun x -> x << r) l

(*| Refines each element of a list with a predicate that holds of all members.

    Returns the same list, with elements of type `x:a{p x}`, given
    `FStar.Reflection.V2.Derived.Lemmas.forallP p l`. *)
val list_ref : (#a:Type) -> (#p:(a -> prop)) -> (l:list a) ->
                    Pure (list (x:a{p x}))
                         (requires (forallP p l))
                         (ensures (fun _ -> True))
let rec list_ref #a #p l =
    match l with
    | [] -> []
    | x::xs -> x :: list_ref #a #p xs

(*| The head and arguments returned by
    `FStar.Reflection.V2.Collect.collect_app_ln'` precede `tt` when the term and
    the accumulated arguments do.

    The inductive step for `FStar.Reflection.V2.Derived.Lemmas.collect_app_order`. *)
val collect_app_order' : (args:list argv) -> (tt:term) -> (t:term) ->
             Lemma (requires args <<: tt /\ t << tt)
                   (ensures (let fn, args' = collect_app_ln' args t in
                             args' <<: tt /\ fn << tt))
                   (decreases t)
let rec collect_app_order' args tt t =
    match inspect_ln_unascribe t with
    | Tv_App l r -> collect_app_order' (r::args) tt l
    | _ -> ()

(*| The head and arguments of `FStar.Reflection.V2.Collect.collect_app_ln t`
    precede `t`, unless `t` is not an application, in which case the head is
    `t` and there are no arguments.

    Call it to justify recursion on the head and arguments of an application;
    `FStar.Reflection.V2.Derived.Lemmas.collect_app_ref` packages the result in
    the types. *)
val collect_app_order : (t:term) ->
            Lemma (ensures (forall (f:term). forall (s:list argv). (f,s) == collect_app_ln t ==>
                              (f << t /\ s <<: t)
                            \/ (f == t /\ s == [] /\ ~(Tv_App? (inspect_ln t)))))
let collect_app_order t =
    match inspect_ln_unascribe t with
    | Tv_App l r -> collect_app_order' [r] t l
    | _ -> ()

(*| Splits an application into its head and arguments, like
    `FStar.Reflection.V2.Collect.collect_app_ln`, with refinements that support
    recursion.

    The head is `t` or precedes `t`, and the term of each argument precedes
    `t`, so a recursive function on terms can call itself on them. *)
val collect_app_ref : (t:term) -> (h:term{h == t \/ h << t}) & list (a:argv{fst a << t})
let collect_app_ref t =
    let h, a = collect_app_ln t in
    collect_app_order t;
    h, list_ref a

(**** [collect_abs_ln t] is smaller than [t] *)
(*| The binders and body returned by `FStar.Reflection.V2.Collect.collect_abs'`
    precede `tt` when the term and the accumulated binders do.

    The inductive step for
    `FStar.Reflection.V2.Derived.Lemmas.collect_abs_ln_order`. *)
let rec collect_abs_order' (bds: binders) (tt t: term)
  : Lemma (requires t << tt /\ bds <<: tt)
          (ensures (let bds', body = collect_abs' bds t in
                    (bds' <<: tt /\ body << tt)))
          (decreases t)
  = match inspect_ln_unascribe t with
    | Tv_Abs b body -> collect_abs_order' (b::bds) tt body
    | _ -> ()

(*| The binders and body of `FStar.Reflection.V2.Collect.collect_abs_ln t`
    precede `t`, unless `t` is not an abstraction, in which case there are no
    binders and the body is `t`. *)
val collect_abs_ln_order : (t:term) ->
            Lemma (ensures forall bds body.
                           (bds, body) == collect_abs_ln t ==>
                                (body << t /\ bds <<: t)
                              \/ (body == t /\ bds == [])
                  )
let collect_abs_ln_order t =
    match inspect_ln_unascribe t with
    | Tv_Abs b body -> collect_abs_order' [b] t body;
                      let bds, body = collect_abs' [] t in
                      Classical.forall_intro (rev_memP bds)
    | _ -> ()

(*| Splits nested abstractions into binders and body, like
    `FStar.Reflection.V2.Collect.collect_abs_ln`, with refinements that support
    recursion.

    Each binder precedes `t`, and the body is `t` or precedes `t`. *)
val collect_abs_ln_ref : (t:term) -> list (bd:binder{bd << t}) & (body:term{body == t \/ body << t})
let collect_abs_ln_ref t =
    let bds, body = collect_abs_ln t in
    collect_abs_ln_order t;
    list_ref bds, body



(**** [collect_arr_ln_bs t] is smaller than [t] *)
(*| The binders and computation type returned by
    `FStar.Reflection.V2.Collect.collect_arr'` precede `tt` when the input
    computation type and the accumulated binders do.

    The inductive step for
    `FStar.Reflection.V2.Derived.Lemmas.collect_arr_ln_bs_order`. *)
let rec collect_arr_order' (bds: binders) (tt: term) (c: comp)
  : Lemma (requires c << tt /\ bds <<: tt)
          (ensures (let bds', c' = collect_arr' bds c in
                    bds' <<: tt /\ c' << tt))
          (decreases c)
  = let cv = inspect_comp c in
    if is_tot_comp cv then
      ( match inspect_ln_unascribe cv.result_typ with
        | Tv_Arrow b c -> collect_arr_order' (b::bds) tt c
        | _ -> ())
    else ()

(*| The binders and computation type of
    `FStar.Reflection.V2.Collect.collect_arr_ln_bs t` precede `t`, unless there
    are no binders and the computation type is `Tot t`. *)
val collect_arr_ln_bs_order : (t:term) ->
            Lemma (ensures forall bds c.
                           (bds, c) == collect_arr_ln_bs t ==>
                                (c << t /\ bds <<: t)
                              \/ (c == pack_comp (mk_tot_comp t) /\ bds == [])
                  )
let collect_arr_ln_bs_order t =
  match inspect_ln_unascribe t with
  | Tv_Arrow b c -> collect_arr_order' [b] t c;
                   Classical.forall_intro_2 (rev_memP #binder);
                   inspect_pack_comp_inv (mk_tot_comp t)
  | _ -> inspect_pack_comp_inv (mk_tot_comp t)

(*| Splits an arrow type into binders and final computation type, like
    `FStar.Reflection.V2.Collect.collect_arr_ln_bs`, with refinements that
    support recursion.

    Each binder precedes `t`, and the computation type precedes `t` or is
    `Tot t` (built with `FStar.Stubs.Reflection.V2.Data.mk_tot_comp`). *)
val collect_arr_ln_bs_ref : (t:term) -> list (bd:binder{bd << t})
                                     & (c:comp{ c == pack_comp (mk_tot_comp t) \/ c << t})
let collect_arr_ln_bs_ref t =
    let bds, c = collect_arr_ln_bs t in
    collect_arr_ln_bs_order t;
    list_ref bds, c
