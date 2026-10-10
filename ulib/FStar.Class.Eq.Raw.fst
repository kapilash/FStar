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
module FStar.Class.Eq.Raw

(*| Typeclass of boolean equality tests on `a`, with no correctness law ("raw").

    Field:

    - `eq`: the equality test.

    Nothing requires `eq` to agree with `==`; for a lawful version see `FStar.Class.Eq.deq`. The operator `FStar.Class.Eq.Raw.op_Equals` (`=`) calls `eq`. *)
class deq a = {
  eq : a -> a -> bool;
}

(*| Builds a `deq` instance for any `eqtype` from the built-in decidable equality `=`.

    Not an instance itself, because typeclass resolution does not look at refinements; the instances for `int`, `unit`, `bool` and `string` are defined with it. *)
let eq_instance_of_eqtype (#a:eqtype) : deq a = {
  eq = (fun x y -> x = y)
}

// It would be nice to declare a single instance for every eqtype,
// but typeclass resolution does not look at refinements to decide
// what to apply.
(*| Equality on `int`, using the built-in decidable equality. *)
instance int_has_eq    : deq int    = eq_instance_of_eqtype
(*| Equality on `unit`, using the built-in decidable equality. *)
instance unit_has_eq   : deq unit   = eq_instance_of_eqtype
(*| Equality on `bool`, using the built-in decidable equality. *)
instance bool_has_eq   : deq bool   = eq_instance_of_eqtype
(*| Equality on `string`, using the built-in decidable equality. *)
instance string_has_eq : deq string = eq_instance_of_eqtype

(*| Compares two lists elementwise with `eq`; true when they have the same length and all corresponding elements are related. *)
let rec eqList #a (eq : a -> a -> bool) (xs ys : list a) : Tot bool =
  match xs, ys with
  | [], [] -> true
  | x::xs, y::ys -> eq x y && eqList eq xs ys
  | _, _ -> false

(*| Equality on lists, comparing elementwise with `FStar.Class.Eq.Raw.eqList`. *)
instance eq_list (_ : deq 'a) : deq (list 'a) = {
  eq = eqList eq;
}

(*| Equality on pairs, componentwise. *)
instance eq_pair (_ : deq 'a) (_ : deq 'b) : deq ('a & 'b) = {
  eq = (fun (a,b) (c,d) -> eq a c && eq b d)
}

(*| Equality on options: `None` equals `None`, and `Some x` equals `Some y` when `x` and `y` are equal. *)
instance eq_option (_ : deq 'a) : deq (option 'a) = {
  eq = (fun o1 o2 ->
    match o1, o2 with
    | None, None -> true
    | Some x, Some y -> eq x y
    | _, _ -> false);
}

(*| Equality on `either`: values are equal when they use the same constructor and their payloads are equal. *)
instance eq_either (_ : deq 'a) (_ : deq 'b) : deq (either 'a 'b) = {
  eq = (fun x y -> 
    match x, y with
    | Inl a1, Inl a2 -> eq a1 a2
    | Inr b1, Inr b2 -> eq b1 b2
    | _, _ -> false);
}

(*| Tests equality with the `eq` method of the `FStar.Class.Eq.Raw.deq` instance in scope.

    Shadows the built-in `=` when this module is opened. *)
val (=) : #a:Type -> {| deq a |} -> a -> a -> bool
let (=) = eq
