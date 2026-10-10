(*
   Copyright 2022 Microsoft Research

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


(* Sequence equivalence relation (see FStar.Algebra.CommMonoid.Equiv)
*)

module FStar.Seq.Equiv
module CE = FStar.Algebra.CommMonoid.Equiv
open FStar.Seq.Base
open FStar.Seq.Properties
open FStar.IntegerIntervals

(*| Lifts an equivalence relation `eq` on elements to sequences: `s1` and `s2`
    are related when they have the same length and their elements at each index
    are related by `eq`.

    The definition is hidden; `FStar.Seq.Equiv.eq_of_seq_condition` states it.
    `FStar.Seq.Equiv.seq_equiv` packages the relation as an equivalence. *)
val eq_of_seq (#c:_) (eq:CE.equiv c) (s1 s2: seq c) : prop

(*| Related sequences have the same length and elements related by `eq` at every
    index. *)
val eq_of_seq_element_equality (#c:_) (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires eq_of_seq eq s1 s2) 
          (ensures length s1 = length s2 /\ 
                   (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i))) 

(*| Sequences of the same length whose elements are related by `eq` at every
    index are related by `FStar.Seq.Equiv.eq_of_seq`. *)
val eq_of_seq_from_element_equality (#c:_) (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires (length s1 = length s2) /\ 
                    (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i)))
          (ensures eq_of_seq eq s1 s2)
         
(*| Characterizes `FStar.Seq.Equiv.eq_of_seq`: the sequences are related exactly
    when they have the same length and their elements are related by `eq` at
    every index. *)
val eq_of_seq_condition (#c:_) (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma ((length s1 = length s2) /\ 
           (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i)) <==>
            eq_of_seq eq s1 s2)

(*| `FStar.Seq.Equiv.eq_of_seq eq` is reflexive. *)
val eq_of_seq_reflexivity (#c:_) (eq: CE.equiv c) (s: seq c)
  : Lemma (ensures eq_of_seq eq s s)

(*| `FStar.Seq.Equiv.eq_of_seq eq` is symmetric. *)
val eq_of_seq_symmetry (#c:_) (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires eq_of_seq eq s1 s2) 
          (ensures eq_of_seq eq s2 s1)

(*| `FStar.Seq.Equiv.eq_of_seq eq` is transitive. *)
val eq_of_seq_transitivity (#c:_) (eq: CE.equiv c) (s1 s2 s3: seq c)
  : Lemma (requires eq_of_seq eq s1 s2 /\ eq_of_seq eq s2 s3) 
          (ensures eq_of_seq eq s1 s3) 
   
(*| The equivalence relation on sequences induced by an equivalence `eq` on
    elements, as a `FStar.Algebra.CommMonoid.Equiv.equiv` built from
    `FStar.Seq.Equiv.eq_of_seq`. *)
val seq_equiv (#c:_) (eq:CE.equiv c) : (CE.equiv (seq c)) 
 
(*| Related non-empty sequences have related last elements and related prefixes,
    as split by `FStar.Seq.Properties.un_snoc`. *)
val eq_of_seq_unsnoc (#c:_) (eq:CE.equiv c) (m:pos) (s1 s2: (z:seq c{length z==m}))
  : Lemma (requires eq_of_seq eq s1 s2)
          (ensures eq.eq (snd (un_snoc s1)) (snd (un_snoc s2)) /\
                   eq_of_seq eq (fst (un_snoc s1)) (fst (un_snoc s2)))
