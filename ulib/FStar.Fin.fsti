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
*)

module FStar.Fin

/// This module is supposed to contain various lemmas about
/// finiteness. For now, it mainly provides a basic pigeonhole
/// principle
///
/// TODO: We might generalize this to also support general utilities
/// for reasoning about cardinality, relation with injections and
/// surjections, etc.
///
/// UPD. November 8, 2022 -- added support for custom equivalence relation-aware
/// pigeon principle lemma.
/// UPD. November 23, 2022 -- added interface file

module L = FStar.List.Tot
module S = FStar.Seq 

(*| The type of integers `k` with `0 <= k < n`.

    The bound `n` is an `int`, so the type is well formed without proving
    `n >= 0`; it is empty when `n <= 0`. See also `FStar.Fin.under`. *)
inline_for_extraction
let fin (n: int) = k: int {0 <= k /\ k < n}

(*| The type of natural numbers smaller than `p`.

    The same set as `FStar.Fin.fin p`, written as a refinement of `nat`.
    `FStar.IntegerIntervals` defines it too, along with other finite
    intervals. *)
inline_for_extraction
let under (p:int) = x:nat {x<p}

(*| The type of lists of `a` with length `n`. *)
inline_for_extraction
let vect (n: int) (a: Type) = l: list a {L.length l = n}

(*| The type of sequences of `a` with length `n`. *)
inline_for_extraction
let seqn (n: int) (a: Type) = s: S.seq a {S.length s = n}

(*| The type of valid indices of the sequence `s`. *)
inline_for_extraction
let in_ (#a: Type) (s: S.seq a) = n: nat{n < S.length s}

(*| Searches the sequence `s`, from position `i` onwards, for an element that
    satisfies `p`.

    Returns `Some j` with `i <= j` and `p (S.index s j)`, or `None` if no
    element at a position `k >= i` satisfies `p`. The contract does not say
    that `j` is the first such position. *)
val find (#a: Type) (s: S.seq a) (p: (a -> bool)) (i: under (S.length s))
    : Pure (option (in_ s))
      (requires True)
      (ensures (function
                | None -> (forall (k: nat{i <= k /\ k < S.length s}). p (S.index s k) == false)
                | Some j -> i <= j /\ p (S.index s j)))
      (decreases (S.length s - i))  

(*| The pigeonhole principle: a sequence of more than `n` values, each
    smaller than `n`, contains a repeated value.

    Returns positions `(i1, i2)` with `i1 < i2` holding equal elements. It
    is a `Pure` function, so it can be used in proofs to name the witnesses:

    ```fstar
    let collision (s: FStar.Seq.seq (FStar.Fin.under 3){FStar.Seq.length s = 4})
      : GTot (i: nat & j: nat{i < j /\ j < 4})
      = let (i, j) = FStar.Fin.pigeonhole s in
        (| i, j |)
    ```

    For a custom equivalence relation instead of equality, see
    `FStar.Fin.pigeonhole_eq`. *)
val pigeonhole (#n: nat) (s: S.seq (under n))
    : Pure (in_ s & in_ s)
      (requires S.length s > n)
      (ensures (fun (i1, i2) -> i1 < i2 /\ S.index s i1 = S.index s i2))
      (decreases n)  

(* Here we prepare to prove pigeonhole principle for a finite sequence
    with a custom equivalence relation (as opposed to eqtype).
    
    Think setoids. *)

(* Following code is extracted from CuteCAS, which will eventually make 
    its way into F* -- when I wrap things up with most important notions
    of abstract algebra. 
    
    As I port more code from my CAS project to F*, such things will be
    moved to separate modules. -- Alex Rozanov *)
 
(*| The type of boolean binary relations on `a`. *)
inline_for_extraction
type binary_relation (a: Type) = a -> a -> bool
 
(*| States that the relation `r` is reflexive: `r x x` for every `x`.

    Abstract in the interface, which keeps the quantifier out of the SMT
    context. Use `FStar.Fin.is_reflexive_intro` to establish it and
    `FStar.Fin.refl_lemma` to use it. *)
val is_reflexive (#a:Type) (r: binary_relation a) : prop

(*| States that the relation `r` is symmetric: `r x y == r y x` for all `x`
    and `y`.

    Abstract in the interface, which keeps the quantifier out of the SMT
    context. Use `FStar.Fin.symm_lemma` to use it. No lemma of the interface
    establishes it: `FStar.Fin.is_symmetric_intro` proves reflexivity instead. *)
val is_symmetric (#a:Type) (r: binary_relation a) : prop

(*| States that the relation `r` is transitive: `r x y` and `r y z` imply
    `r x z`.

    Abstract in the interface, which keeps the quantifier out of the SMT
    context. Use `FStar.Fin.trans_lemma` to use it. No lemma of the interface
    establishes it: `FStar.Fin.is_transitive_intro` proves reflexivity instead. *)
val is_transitive (#a:Type) (r: binary_relation a) : prop

(*| Proves `FStar.Fin.is_reflexive r` from `r x x` for every `x`.

    ```fstar
    let _ = FStar.Fin.is_reflexive_intro #int (fun x y -> x = y)
    ``` *)
val is_reflexive_intro (#a:Type) (r: binary_relation a)
  : Lemma (requires forall (x:a). r x x) (ensures is_reflexive r)
  
(*| Despite its name, this lemma has the same statement as
    `FStar.Fin.is_reflexive_intro`: it proves `is_reflexive r` from
    `r x x` for every `x`.

    It does not establish `FStar.Fin.is_symmetric`; this is a mistake in
    the interface. *)
val is_symmetric_intro (#a:Type) (r: binary_relation a)
  : Lemma (requires forall (x:a). r x x) (ensures is_reflexive r)
 
(*| Despite its name, this lemma has the same statement as
    `FStar.Fin.is_reflexive_intro`: it proves `is_reflexive r` from
    `r x x` for every `x`.

    It does not establish `FStar.Fin.is_transitive`; this is a mistake in
    the interface. *)
val is_transitive_intro (#a:Type) (r: binary_relation a)
  : Lemma (requires forall (x:a). r x x) (ensures is_reflexive r)
   
(*| The type of boolean relations on `a` that are reflexive, symmetric and
    transitive.

    Use `FStar.Fin.refl_lemma`, `FStar.Fin.symm_lemma` and
    `FStar.Fin.trans_lemma` to apply the three properties. *)
type equivalence_relation (a: Type) 
  = r:binary_relation a { is_reflexive r /\ is_symmetric r /\ is_transitive r }

(*| An equivalence relation relates every element to itself: `eq x x`. *)
val refl_lemma (#a:Type) (eq: equivalence_relation a) (x:a) 
  : Lemma (eq x x)
   
(*| An equivalence relation is symmetric: `eq x y == eq y x`. *)
val symm_lemma (#a:Type) (eq:equivalence_relation a) (x y:a) 
  : Lemma (eq x y == eq y x)  
  
(*| An equivalence relation is transitive, in either direction: if `x` and
    `y` are related and `y` and `z` are related, in either order, then
    `eq x z` and `eq z x` both hold. *)
val trans_lemma (#a:Type) (eq: equivalence_relation a) (x y z:a)
  : Lemma (requires (eq x y \/ eq y x) /\ (eq y z \/ eq z y))  
          (ensures (x `eq` z) && (z `eq` x))    
  

(*| States that `s` contains an element related to `x` by the equivalence
    relation `eq`.

    The counterpart of `FStar.Seq.Properties.mem` for a custom equivalence.
    It is opaque to SMT; `FStar.Fin.find_eq` returns a witness position. *)
[@@"opaque_to_smt"]
let contains_eq #a (eq: equivalence_relation a) (s: S.seq a) (x:a)
  = exists (i:under (S.length s)). eq x (S.index s i)

(*| A sequence that contains an element up to `eq` is nonempty.

    Triggered automatically on `contains_eq eq s x`. *)
val contains_eq_means_nonempty (#a:Type) (eq:equivalence_relation a) (s: S.seq a) (x:a)
  : Lemma (requires contains_eq eq s x) 
          (ensures S.length s > 0) 
          [SMTPat(contains_eq eq s x)]  

(*| The type of the values that occur in `s` up to the equivalence relation
    `eq`, as stated by `FStar.Fin.contains_eq`. *)
let items_of #a (eq: equivalence_relation a) (s: S.seq a) 
  = x:a { contains_eq eq s x } 
   
(*| Returns the first position in `s` of an element related to `x` by `eq`.

    Unlike `FStar.Fin.find`, the precondition `contains_eq eq s x` guarantees
    success, so the result is a bare index. No earlier position holds an
    element related to `x`. *)
val find_eq (#a:Type) (eq:equivalence_relation a) (s: S.seq a) (x:a { contains_eq eq s x })
  : (i: nat { (i < S.length s) 
          /\ (x `eq` S.index s i) 
          /\ (forall (j: under i). not (x `eq` S.index s j)) })  
  
(*| The pigeonhole principle up to an equivalence relation: if every element
    of `pigeons` is related by `eq` to some element of the nonempty sequence
    `holes`, and `pigeons` is longer than `holes`, then two elements of
    `pigeons` are related.

    Returns positions `(i1, i2)` with `i1 < i2` whose elements are related
    by `eq`. See `FStar.Fin.pigeonhole` for the version with equality. *)
val pigeonhole_eq (#a:Type) (eq: equivalence_relation a) 
                            (holes: S.seq a{S.length holes > 0}) 
                            (pigeons: S.seq (items_of eq holes))
  : Pure (under (S.length pigeons) & under (S.length pigeons))
         (requires S.length pigeons > S.length holes)
         (ensures (fun (i1, i2) -> i1 < i2 /\ (S.index pigeons i1 `eq` S.index pigeons i2)))
         (decreases S.length holes)  
