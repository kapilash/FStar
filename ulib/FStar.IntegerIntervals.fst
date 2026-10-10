(*
   Copyright 2008-2022 Microsoft Research
   
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
   
       http://www.apache.org/licenses/LICENSE-2.0
       
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: A. Rozanov
*)
module FStar.IntegerIntervals
 
(* Aliases to all kinds of integer intervals *)

(* general infinite integer intervals *)
(*| The integers strictly below `k`. *)
type less_than (k: int) = x:int{x<k}
(*| The integers strictly above `k`. *)
type greater_than (k: int) = x:int{x>k}
(*| The integers greater than or equal to `x`, defined as `greater_than (x - 1)`. *)
type not_less_than (x: int) = greater_than (x-1)
(*| The integers less than or equal to `x`, defined as `less_than (x + 1)`. *)
type not_greater_than (x: int) = less_than (x+1)

(* Type coercion. While supposed to be absolutely trivial, 
   might still be invoked directly under extremely low rlimits *)
(*| Views a value of `not_greater_than n` as a value of `less_than (n + 1)`; the identity on the integer.

    The two types are equal by definition. The coercion is useful when a proof under a very low rlimit fails to see that. *)
let coerce_to_less_than #n (x: not_greater_than n) : less_than (n+1) = x
(*| Views a value of `greater_than n` as a value of `not_less_than (n + 1)`; the identity on the integer.

    The coercion is useful when a proof under a very low rlimit fails to see that the types coincide. *)
let coerce_to_not_less_than #n (x: greater_than n) : not_less_than (n+1) = x

(*| Boolean test that `t` lies in the half-open interval from `x` (included) to `y` (excluded): `x <= t && t < y`. *)
let interval_condition (x y t: int) = (x <= t) && (t < y)

(*| The type of the interval types with bounds `x` and `y`: a `Type0` provably equal to the refinement of `int` by `interval_condition x y`.

    It lets functions such as `FStar.IntegerIntervals.interval_size` take an interval type as an argument and recover its bounds as implicit arguments. *)
type interval_type (x y:int) = z : Type0{ z == t:int{interval_condition x y t} }

(* Default interval is half-open, which is the most frequently used case *) 
(*| The half-open integer interval of `t` with `x <= t < y`, the default kind of interval.

    It is empty when `y <= x`. For the other combinations of open and closed ends see `FStar.IntegerIntervals.efrom_eto`, `FStar.IntegerIntervals.efrom_ito`, `FStar.IntegerIntervals.ifrom_eto` and `FStar.IntegerIntervals.ifrom_ito`. *)
type interval (x y: int) : interval_type x y = t:int{interval_condition x y t}

(* general finite integer intervals *)
(*| The open integer interval `x < t < y`, excluding both ends. *)
type efrom_eto (x y: int) = interval (x+1) y
(*| The integer interval `x < t <= y`, excluding `x` and including `y`. *)
type efrom_ito (x y: int) = interval (x+1) (y+1)
(*| The integer interval `x <= t < y`, including `x` and excluding `y`; the same as `FStar.IntegerIntervals.interval x y`. *)
type ifrom_eto (x y: int) = interval x y
(*| The closed integer interval `x <= t <= y`, including both ends. *)
type ifrom_ito (x y: int) = interval x (y+1)

(* Special case for naturals under k, to use in sequences, lists, arrays, etc *)
(*| The natural numbers below `k`, the interval from `0` (included) to `k` (excluded).

    Convenient for indices into sequences, lists and arrays of length `k`.

    ```fstar
    let first_ten : under 10 = 9
    ``` *)
type under (k: nat) = interval 0 k

(* If we define our intervals this way, then the following lemma comes for free: *)
private let closed_interval_lemma (x y:int) : Lemma (interval x (y+1) == ifrom_ito x y) = ()


(* how many numbers fall into an interval? *)
(*| The number of integers in an interval type: `y - x` when `y >= x`, else `0`.

    The argument is the interval type itself, for example `interval_size (interval 5 10) = 5`; its bounds are inferred.

    ```fstar
    let sizes () : Lemma (interval_size (interval 5 10) = 5 /\ closed_interval_size 5 10 = 6) = ()
    ``` *)
let interval_size (#x #y: int) (interval: interval_type x y) : nat 
  = if y >= x then y-x else 0

(* when we want a zero-based index that runs over an interval, we use this *)
(*| Zero-based indices running over an interval: the type `under (interval_size interval)`. *)
type counter_for (#x #y:int) (interval: interval_type x y) = under (interval_size interval)

(* special case for closed intervals, used in FStar.Algebra.CommMonoid.Fold *)
(*| The number of integers in the closed interval `ifrom_ito x y`: `y - x + 1` when `x <= y + 1`, else `0`.

    Used by `FStar.Algebra.CommMonoid.Fold`. *)
let closed_interval_size (x y: int) : nat = interval_size (ifrom_ito x y)

(* A usage example and a test at the same time: *)
private let _ = assert (interval_size (interval 5 10) = 5)
private let _ = assert (interval_size (ifrom_ito 5 10) = 6)
private let _ = assert (interval_size (ifrom_ito 15 10) = 0)

(* This lemma, especially when used with forall_intro, helps the 
   prover verify the index ranges of sequences that correspond 
   to arbitrary folds. 

   It is supposed to be invoked to decrease the toll we put on rlimit,
   i.e. will be redundant in most use cases. *)
(*| For a zero-based counter `i` over the closed interval `ifrom_ito x y`, the shifted value `x + i` lies between `x` and `y`.

    Mostly redundant, it can reduce the rlimit needed when proving index ranges of folds, for instance via `FStar.Classical.forall_intro`. *)
let counter_bounds_lemma (x y:int) (i: (counter_for (ifrom_ito x y))) 
  : Lemma (x+i >= x /\ x+i <= y) = ()

(* An integer sequence [0..n), n values in total,
   with index value available to the prover. *)
(*| The sequence `0, 1, ..., n - 1` of the indices below `n`.

    Its type states that it has length `n` and that the element at each index `k` is `k`. *)
let indices_seq (n: nat) 
  : (f:FStar.Seq.Base.seq (under n) {
       FStar.Seq.Base.length f = n /\ 
       (forall (k: under n). FStar.Seq.Base.index f k = k) 
    }) 
  = FStar.Seq.Base.init n (fun (x:under n) -> x)
