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
module FStar.Class.TotalOrder.Raw

open FStar.Order

(*| Reverses a `FStar.Order.order`: swaps `Lt` and `Gt` and keeps `Eq`. *)
let flip = function
  | Lt -> Gt
  | Eq -> Eq
  | Gt -> Lt

(*| The type of three-way comparison functions on `a`, returning a `FStar.Order.order`. *)
let raw_comparator (a:Type) = a -> a -> order

(*| Typeclass of three-way comparisons on `a`, intended to be total orders, with no laws recorded ("raw").

    Field:

    - `compare`: the comparison, a `FStar.Class.TotalOrder.Raw.raw_comparator`.

    The operators `<`, `>`, `=`, `<=`, `>=` and `<>` of this module are derived from `compare` and shadow the built-in ones when the module is opened. Instances exist for `int`, `bool` (with `false` below `true`), pairs, options and lists. For example, lists compare lexicographically:

    ```fstar
    let _ = assert_norm (compare [1; 2] [1; 3] == FStar.Order.Lt)
    ``` *)
class totalorder (a:Type) = {
  compare : raw_comparator a;
}

(*| True when `compare x y` is `Lt`. *)
val (<) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (<) x y = compare x y = Lt

(*| True when `compare x y` is `Gt`. *)
val (>) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (>) x y = compare x y = Gt

(*| True when `compare x y` is `Eq`.

    This is equality as decided by the instance, not necessarily `==`. *)
val (=) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (=) x y = compare x y = Eq

(*| True when `compare x y` is not `Gt`. *)
val (<=) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (<=) x y = compare x y <> Gt

(*| True when `compare x y` is not `Lt`. *)
val (>=) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (>=) x y = compare x y <> Lt

(*| True when `compare x y` is not `Eq`. *)
val (<>) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (<>) x y = compare x y <> Eq

instance _ : totalorder int = {
  compare = Order.compare_int;
}

instance _ : totalorder bool = {
  compare = (fun b1 b2 -> match b1, b2 with | false, false | true, true -> Eq | false, _ -> Lt | _ -> Gt);
}

(*| Lexicographic order on pairs: by first component, then by second. *)
instance totalorder_pair #a #b (d1 : totalorder a) (d2 : totalorder b) : totalorder (a & b) = {
  compare = (fun (xa,xb) (ya, yb) ->
    match compare xa ya with
    | Lt -> Lt
    | Gt -> Gt
    | Eq -> compare xb yb);
}

(*| Order on options: `None` is below every `Some x`, and `Some` values compare by their contents.

    ```fstar
    let _ = assert_norm (Some 1 < Some 2)
    ``` *)
instance totalorder_option #a (d : totalorder a) : totalorder (option a) = {
  compare = (fun o1 o2 -> match o1, o2 with
    | None, None -> Eq
    | None, Some _ -> Lt
    | Some _, None -> Gt
    | Some a1, Some a2 -> compare a1 a2);
}

(*| Lexicographic comparison of lists using the element order `d`; a proper prefix is below the longer list. *)
let rec raw_compare_lists #a (d : totalorder a) : raw_comparator (list a) =
  fun l1 l2 ->
    match l1, l2 with
    | [], [] -> Eq
    | [], _::_ -> Lt
    | _::_, [] -> Gt
    | x::xs, y::ys ->
        match compare x y with
        | Lt -> Lt
        | Gt -> Gt
        | Eq -> raw_compare_lists d xs ys

(*| Lexicographic order on lists, by `FStar.Class.TotalOrder.Raw.raw_compare_lists`. *)
instance totalorder_list #a (d : totalorder a) : totalorder (list a) = {
  compare = raw_compare_lists d;
}
