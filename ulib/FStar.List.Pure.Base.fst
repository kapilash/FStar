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
module FStar.List.Pure.Base

open FStar.List.Tot.Base

(** Functions on list with a pure specification *)

(*| Applies `f` pointwise to two lists of the same length and returns the list
    of results.

    `map2 f [x1; x2] [y1; y2]` is `[f x1 y1; f x2 y2]`. The caller must prove
    that the lengths are equal; `FStar.List.map2` is the `ML` variant that
    fails at run time instead. *)
val map2 (#a1 #a2 #b: Type)
  (f: a1 -> a2 -> b)
  (l1:list a1)
  (l2:list a2)
  : Pure (list b)
    (requires (length l1 == length l2))
    (ensures (fun _ -> True))
    (decreases l1)
let rec map2 #a1 #a2 #b f l1 l2 =
  match l1, l2 with
  | [], [] -> []
  | x1::xs1, x2::xs2 -> f x1 x2 :: map2 f xs1 xs2

(*| Applies `f` pointwise to three lists of the same length and returns the
    list of results.

    `map3 f [x1; x2] [y1; y2] [z1; z2]` is `[f x1 y1 z1; f x2 y2 z2]`. The
    caller must prove that the three lengths are equal; `FStar.List.map3` is the
    `ML` variant that fails at run time instead. *)
val map3 (#a1 #a2 #a3 #b: Type)
  (f: a1 -> a2 -> a3 -> b)
  (l1:list a1)
  (l2:list a2)
  (l3:list a3)
  : Pure (list b)
    (requires (let n = length l1 in
      (n == length l2 /\
        n == length l3)))
    (ensures (fun _ -> True))
    (decreases l1)
let rec map3 #a1 #a2 #a3 #b f l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x1::xs1, x2::xs2, x3::xs3 -> f x1 x2 x3 :: map3 f xs1 xs2 xs3

(*| Pairs up the elements at the same positions of two lists of the same
    length.

    The caller must prove that the lengths are equal. Defined with
    `FStar.List.Pure.Base.map2`; `FStar.List.zip` is the `ML` variant that fails
    at run time instead.

    ```fstar
    let pairs : list (int & bool) = FStar.List.Pure.Base.zip [1; 2] [true; false]
    ``` *)
val zip (#a1 #a2:Type) (l1:list a1) (l2:list a2)
  : Pure (list (a1 & a2))
    (requires (let n = length l1 in n == length l2))
    (ensures (fun _ -> True))
let zip #a1 #a2 l1 l2 = map2 (fun x y -> x, y) l1 l2

(*| Groups the elements at the same positions of three lists of the same
    length into triples.

    The caller must prove that the three lengths are equal. Defined with
    `FStar.List.Pure.Base.map3`. *)
val zip3 (#a1 #a2 #a3:Type) (l1:list a1) (l2:list a2) (l3:list a3)
  : Pure (list (a1 & a2 & a3))
    (requires (let n = length l1 in n == length l2 /\ n == length l3))
    (ensures (fun _ -> True))
let zip3 #a1 #a2 #a3 l1 l2 l3 = map3 (fun x y z -> x,y,z) l1 l2 l3
