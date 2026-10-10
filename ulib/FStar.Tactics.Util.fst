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
module FStar.Tactics.Util

open FStar.Tactics.Effect
open FStar.List.Tot.Base

(* Tac list functions, since there's no effect polymorphism *)

(*| Applies a tactic to each element of a list, from left to right, and
    returns the list of results; the `Tac` version of
    `FStar.List.Tot.Base.map`.

    ```fstar
    let _ = assert True by (let l = FStar.Tactics.Util.map (fun x -> x + 1) [1; 2] in
                            guard (l = [2; 3]))
    ``` *)
val map: ('a -> Tac 'b) -> list 'a -> Tac (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

(*| Applies a tactic returning a list to each element of a list, from left
    to right, and concatenates the results. *)
let rec concatMap (f : 'a -> Tac (list 'b)) (l : list 'a) : Tac (list 'b) =
  match l with
  | [] -> []
  | x::xs -> f x @ concatMap f xs

(*| Helper for `FStar.Tactics.Util.mapi`: maps a tactic over a list,
    passing it each element's index, counting from the given start index. *)
val __mapi: nat -> (nat -> 'a -> Tac 'b) -> list 'a -> Tac (list 'b)
let rec __mapi i f x = match x with
  | [] -> []
  | a::tl -> f i a::__mapi (i+1) f tl

(*| Applies a tactic to each element of a list together with its index
    (counting from 0), from left to right, and returns the results. *)
val mapi: (nat -> 'a -> Tac 'b) -> list 'a -> Tac (list 'b)
let mapi f l = __mapi 0 f l

(*| Runs a tactic on each element of a list, from left to right. *)
val iter : ('a -> Tac unit) -> list 'a -> Tac unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> f a; iter f tl

(*| Helper for `FStar.Tactics.Util.iteri`: runs a tactic on each element of
    a list with its index, counting from the given start index. *)
val iteri_aux: int -> (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl

(*| Runs a tactic on each element of a list together with its index
    (counting from 0), from left to right. *)
val iteri: (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let iteri f x = iteri_aux 0 f x

(*| Folds a tactic over a list from the left, starting from the given
    accumulator; the `Tac` version of `FStar.List.Tot.Base.fold_left`. *)
val fold_left: ('a -> 'b -> Tac 'a) -> 'a -> l:list 'b -> Tac 'a
let rec fold_left f x l = match l with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

(*| Folds a tactic over a list from the right, ending with the given
    value; the `Tac` version of `FStar.List.Tot.Base.fold_right`. *)
val fold_right: ('a -> 'b -> Tac 'b) -> list 'a -> 'b -> Tac 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(* There's no unconditionally total zip like this in Tot.Base, why? Anyway use this *)
(*| Pairs up the elements of two lists; the result is as long as the
    shorter list, the extra elements of the longer one are dropped. *)
val zip : (#a:Type) -> (#b:Type) -> list a -> list b -> Tac (list (a & b))
let rec zip #a #b l1 l2 = match l1, l2 with
    | x::xs, y::ys -> (x,y) :: (zip xs ys)
    | _ -> []

(*| Keeps the elements of a list for which a tactic returns `true`, in
    order. *)
val filter: ('a -> Tac bool) -> list 'a -> Tac (list 'a)
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl

private let rec filter_map_acc (f:'a -> Tac (option 'b)) (acc:list 'b) (l:list 'a)
    : Tac (list 'b) =
  match l with
  | [] ->
      rev acc
  | hd :: tl ->
      match f hd with
      | Some hd ->
          filter_map_acc f (hd :: acc) tl
      | None ->
          filter_map_acc f acc tl

(*| Applies a tactic returning an option to each element of a list and keeps
    the `Some` results, in order. *)
let filter_map (f:'a -> Tac (option 'b)) (l:list 'a) : Tac (list 'b) =
  filter_map_acc f [] l

(*| Returns the first `Some` result of a tactic applied to the elements of a
    list in order, or `None` if there is none; stops at the first `Some`. *)
val tryPick: ('a -> Tac (option 'b)) -> list 'a -> Tac (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

(*| Applies a tactic to the content of an option, if any. *)
let map_opt (f:'a -> Tac 'b) (x:option 'a) : Tac (option 'b) =
  match x with
  | None -> None
  | Some x -> Some (f x)

(*| Runs a tactic `n` times and returns the list of results, which has
    length `n` (empty if `n` is not positive). *)
let rec repeatn (#a:Type) (n : int) (t : unit -> Tac a) : Tac (l:list a{n < 0 \/ length l == n}) =
    if n <= 0
    then []
    else t () :: repeatn (n - 1) t

(*| Returns whether a tactic returns `true` on some element of a list,
    trying them in order and stopping at the first success.

    The same as `FStar.Tactics.Util.existsb`. *)
let rec tryFind (#a:Type) (f:a -> Tac bool) (l:list a) : Tac bool =
  match l with
  | [] -> false
  | hd::tl ->
    if f hd then true
    else tryFind f tl

(*| Folds a tactic over two lists of equal length from the left, starting
    from the given accumulator; the lists must have the same length. *)
let rec fold_left2 (#a #b #c:Type) (f:a -> b -> c -> Tac a) (x:a) (l1:list b) (l2:list c)
  : TacH a
      (requires length l1 == length l2)
      (ensures fun _ -> True) =
  match l1, l2 with
  | [], [] -> x
  | hd1::tl1, hd2::tl2 ->
    fold_left2 f (f x hd1 hd2) tl1 tl2

(*| Renders a list as the concatenation of its elements printed by the given
    tactic, each followed by `;`. *)
let rec string_of_list #a (f : a -> Tac string) (l : list a) : Tac string =
  match l with
  | [] -> ""
  | x::xs -> f x ^ ";" ^ string_of_list f xs

(*| Renders an option as `None`, or as `Some` and a space followed by its
    content printed by the given tactic. *)
let string_of_option #a (f : a -> Tac string) (o : option a) : Tac string =
  match o with
  | Some x -> "Some " ^ f x
  | None -> "None"

(*| Returns whether a tactic returns `true` on some element of a list,
    trying them in order and stopping at the first success.

    The same as `FStar.Tactics.Util.tryFind`. *)
val existsb : ('a -> Tac bool) -> list 'a -> Tac bool
let rec existsb f l = match l with
  | [] -> false
  | hd::tl ->
    if f hd then true
    else existsb f tl
