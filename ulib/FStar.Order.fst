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
module FStar.Order

(*| The result of a three-way comparison.

    Constructors: `Lt` (less than), `Eq` (equal) and `Gt` (greater than).
    Equality on `order` is decidable. Comparison functions such as
    `FStar.Order.compare_int` return an `order`; `FStar.Order.lex` combines them. *)
[@@plugin]
type order = | Lt | Eq | Gt

// Some derived checks
(*| Holds when the comparison result is not `Lt`, i.e. greater than or equal. *)
val ge : order -> bool
let ge o = o <> Lt

(*| Holds when the comparison result is not `Gt`, i.e. less than or equal. *)
val le : order -> bool
let le o = o <> Gt

(*| Holds when the comparison result is not `Eq`. *)
val ne : order -> bool
let ne o = o <> Eq

// Just for completeness and consistency...
(*| Holds when the comparison result is `Gt`. *)
val gt : order -> bool
let gt o = o = Gt

(*| Holds when the comparison result is `Lt`. *)
val lt : order -> bool
let lt o = o = Lt

(*| Holds when the comparison result is `Eq`. *)
val eq : order -> bool
let eq o = o = Eq

// Lexicographical combination, thunked to be lazy
(*| Lexicographic combination of two comparisons: returns `o1` unless it is
    `Eq`, in which case it returns `o2 ()`.

    The second comparison is thunked, so it is only computed when the first
    one is `Eq`.

    ```fstar
    let compare_pair (p q: int & int) : FStar.Order.order =
      let open FStar.Order in
      lex (compare_int (fst p) (fst q)) (fun _ -> compare_int (snd p) (snd q))

    let _ = assert_norm (compare_pair (1, 5) (1, 3) == FStar.Order.Gt)
    ``` *)
val lex : order -> (unit -> order) -> order
let lex o1 o2 =
    match o1 with
    | Lt -> Lt
    | Eq -> o2 ()
    | Gt -> Gt

(*| Converts the sign of an integer to an `order`: negative gives `Lt`, zero
    gives `Eq` and positive gives `Gt`.

    The inverse direction is `FStar.Order.int_of_order`. *)
val order_from_int : int -> order
let order_from_int i =
    if i < 0 then Lt
    else if i = 0 then Eq
    else Gt

(*| Converts an `order` to `-1`, `0` or `1` for `Lt`, `Eq` and `Gt`.

    The inverse of `FStar.Order.order_from_int` on these three values. *)
val int_of_order : order -> int
let int_of_order = function
    | Lt -> (-1)
    | Eq -> 0
    | Gt -> 1

(*| Compares two integers: `Lt` when `i < j`, `Eq` when `i = j` and `Gt`
    when `i > j`. *)
val compare_int : int -> int -> order
let compare_int i j = order_from_int (i - j)

(*
 * It promises to call the comparator in strictly smaller elements
 * Useful when writing a comparator for an inductive type,
 *   that contains the list of itself as an argument to one of its
 *   data constructors
 *)
(*| Lexicographic comparison of two lists using an element comparator `f`.

    Elements are compared pairwise from the head; if one list runs out first
    while all compared elements are `Eq`, the shorter list is `Lt`. The
    comparator is only called on elements of `l1` and `l2`, which is reflected
    in its refined argument types (`x << l1`, `y << l2`): this lets `f` call
    back into a comparator for an inductive type that contains a list of
    itself, with termination checked by the typechecker. *)
let rec compare_list (#a:Type)
  (l1 l2:list a)
  (f:(x:a{x << l1} -> y:a{y << l2} -> order))
  : order
  = match l1, l2 with
    | [], [] -> Eq
    | [], _ -> Lt
    | _, [] -> Gt
    | x::xs, y::ys -> lex (f x y) (fun _ -> compare_list xs ys f)

(*| Compares two options using `f` on the contents; `None` is smaller than any
    `Some`. *)
val compare_option : ('a -> 'a -> order) -> option 'a -> option 'a -> order
let compare_option f x y =
    match x, y with
    | None   , None   -> Eq
    | None   , Some _ -> Lt
    | Some _ , None   -> Gt
    | Some x , Some y -> f x y
