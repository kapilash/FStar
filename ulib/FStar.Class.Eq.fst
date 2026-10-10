(*
   Copyright 2008-2023 Microsoft Research

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
module FStar.Class.Eq

open FStar.Tactics.Typeclasses
module Raw = FStar.Class.Eq.Raw

(*| Holds when the boolean test `f` decides propositional equality: `f x y` is true exactly when `x == y`. *)
let decides_eq (#a:Type) (f : a -> a -> bool) : prop =
  forall x y. f x y <==> x == y

(*| Typeclass of decidable equality on `a`: a raw equality test together with a proof that it is correct.

    Fields:

    - `raw`: a `FStar.Class.Eq.Raw.deq` instance providing the test `raw.eq`.
    - `eq_dec`: the law `decides_eq raw.eq`, as a `squash`.

    Unlike `eqtype`, this also applies to types whose equality is not built in, as long as an instance is provided. Use `FStar.Class.Eq.eq` or `=` to compare. *)
class deq a = {
  raw : Raw.deq a;
  eq_dec : squash (decides_eq raw.eq);
}

(*| Superclass projection: every lawful `deq` instance yields the corresponding `FStar.Class.Eq.Raw.deq` instance. *)
instance deq_raw_deq (a:Type) (d:deq a) : Raw.deq a = d.raw

(*| Tests equality with the `deq` instance in scope; the result is true exactly when the arguments are equal, by the `eq_dec` law.

    The law is not attached to the result type, so to use it in proofs, unfold `decides_eq` from the instance's `eq_dec` field, or normalize on concrete values. *)
let eq (#a:Type) {| d : deq a |} (x y : a) : bool =
  d.raw.eq x y

(*| Builds a lawful `deq` instance for any `eqtype`, using the built-in decidable equality `=`.

    The raw test is always `FStar.Class.Eq.Raw.eq_instance_of_eqtype`; the `FStar.Class.Eq.Raw.deq` instance argument is not used.

    Used to define the instances for `int`, `unit`, `bool` and `string`. *)
let eq_instance_of_eqtype (#a:eqtype) {| Raw.deq a |} : deq a = {
  raw = Raw.eq_instance_of_eqtype #a;
  eq_dec = ();
}

(*| Decidable equality on `int`. *)
instance int_has_eq : deq int = eq_instance_of_eqtype
(*| Decidable equality on `unit`. *)
instance unit_has_eq : deq unit = eq_instance_of_eqtype
(*| Decidable equality on `bool`. *)
instance bool_has_eq : deq bool = eq_instance_of_eqtype
(*| Decidable equality on `string`. *)
instance string_has_eq : deq string = eq_instance_of_eqtype

(*| `FStar.Class.Eq.Raw.eqList` decides equality on lists, given a lawful `deq` instance for the elements.

    Provides the `eq_dec` law of `FStar.Class.Eq.eq_list`. *)
let eqList_ok (#a:Type) (d : deq a) : Lemma (decides_eq #(list a) (Raw.eqList d.raw.eq)) =
  let rec aux (xs ys : list a) : Lemma (Raw.eqList d.raw.eq xs ys <==> xs == ys) =
    match xs, ys with
    | x::xs, y::ys ->
      aux xs ys
    | [], [] -> ()
    | _ -> ()
  in
  Classical.forall_intro_2 aux;
  ()

(*| Decidable equality on lists, elementwise. *)
instance eq_list (d : deq 'a) : deq (list 'a) = {
  raw = Raw.eq_list d.raw;
  eq_dec = eqList_ok d;
}

(*| Decidable equality on pairs, componentwise. *)
instance eq_pair (_ : deq 'a) (_ : deq 'b) : deq ('a & 'b) = {
  raw = solve;
  eq_dec = ();
}

(*| Decidable equality on options. *)
instance eq_option (_ : deq 'a) : deq (option 'a) = {
  raw = solve;
  eq_dec = ();
}

(*| Tests equality with the `deq` instance in scope; the same as `FStar.Class.Eq.eq`.

    Shadows the built-in `=` when this module is opened. *)
val (=) : #a:Type -> {| deq a |} -> a -> a -> bool
let (=) = eq
