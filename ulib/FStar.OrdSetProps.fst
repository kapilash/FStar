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
module FStar.OrdSetProps
 
open FStar.OrdSet
 
(*| Folds `g` over the elements of `s`, starting from `x`: for a non-empty set
    the result is `g e (fold g (remove e s) x)` where `e` is the element picked
    by `FStar.OrdSet.choose s`.

    The order in which elements are visited follows `FStar.OrdSet.choose`,
    which the interface does not specify. Compare `FStar.OrdSet.fold`. *)
val fold: #a:eqtype -> #b:Type -> #f:cmp a -> (a -> b -> Tot b) -> s:ordset a f -> b
          -> Tot b (decreases (size s))
let rec fold (#a:eqtype) (#b:Type) #f g s x =
  if s = empty then x
  else
    let Some e = choose s in
    let a_rest = fold g (remove e s) x in
    g e a_rest

(**********)

(*| Returns `s` with `x` added: the union of `singleton x` and `s`. *)
let insert (#a:eqtype) (#f:cmp a) (x:a) (s:ordset a f) = union #a #f (singleton #a #f x) s

(*| Union defined by folding `FStar.OrdSetProps.insert` over the first set.

    `FStar.OrdSetProps.union_lemma'` shows that it equals `FStar.OrdSet.union`. *)
val union':#a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
let union' (#a:eqtype) #f s1 s2 = fold (fun e (s:ordset a f) -> insert e s) s1 s2

(*| `FStar.OrdSetProps.union'` and `FStar.OrdSet.union` have the same members. *)
val union_lemma: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                 -> Lemma (requires (True))
                    (ensures (forall x. mem x (union s1 s2) = mem x (union' s1 s2)))
                    (decreases (size s1))
let rec union_lemma (#a:eqtype) #f s1 s2 =
  if s1 = empty then ()
  else
    union_lemma (remove (Some?.v (choose s1)) s1) s2

(*| `FStar.OrdSetProps.union'` and `FStar.OrdSet.union` are equal. *)
val union_lemma': #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                  -> Lemma (requires (True))
                     (ensures (union s1 s2 = union' s1 s2))
let union_lemma' (#a:eqtype) #f s1 s2 =
  union_lemma s1 s2;
  eq_lemma (union s1 s2) (union' s1 s2)

