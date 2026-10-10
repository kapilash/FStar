(*
   Copyright 2008-2026 Microsoft Research

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
module FStar.Real.Dedekind.Sup

/// Completeness of the Dedekind reals.
///
/// The least upper bound of a nonempty, bounded-above family of cuts is simply
/// its *union*. That this union is again a cut is what makes the construction
/// worth the trouble, and it is the single property that separates the reals
/// from the rationals --- and hence the property that gives us square roots.

module Q = FStar.Rational
module B = FStar.Real.Dedekind.Base

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(*| Sets of cuts, represented as predicates `B.cut -> prop`. *)
let cset = B.cut -> prop

(*| `b` is an upper bound of the set of cuts `s`: every `x` in `s` satisfies `B.cle x b`. *)
let cupper (s:cset) (b:B.cut) : prop = forall (x:B.cut). s x ==> B.cle x b
(*| The set of cuts `s` has some upper bound. *)
let cbounded (s:cset) : prop = exists (b:B.cut). cupper s b
(*| The set of cuts `s` has at least one member. *)
let cnonempty (s:cset) : prop = exists (x:B.cut). s x

(*| Membership in the union of a set of cuts: `q` belongs to some cut in `s`. *)
let unionp (s:cset) (q:Q.rat) : prop = exists (x:B.cut). s x /\ x q

(*| The union of a nonempty set of cuts is nonempty. *)
let union_ne (s:cset)
  : Lemma (requires cnonempty s) (ensures exists (q:Q.rat). unionp s q)
  = eliminate exists (x:B.cut). s x
    with begin
      let a = B.cut_mem x in
      introduce exists (x2:B.cut). s x2 /\ x2 a with x and ();
      introduce exists (q:Q.rat). unionp s q with a and ()
    end

(*| The union of a set of cuts bounded above is not all of the rationals: a rational outside an upper bound is outside the union. *)
let union_nf (s:cset)
  : Lemma (requires cbounded s) (ensures exists (q:Q.rat). ~(unionp s q))
  = eliminate exists (b:B.cut). cupper s b
    with begin
      let t = B.cut_nonmem b in
      introduce unionp s t ==> False
      with eliminate exists (x:B.cut). s x /\ x t with ();
      introduce exists (q:Q.rat). ~(unionp s q) with t and ()
    end

(*| The union of a set of cuts is downward closed. *)
let union_dc (s:cset)
  : Lemma (forall (u v:Q.rat). (unionp s v /\ Q.lt u v) ==> unionp s u)
  = introduce forall (u v:Q.rat). (unionp s v /\ Q.lt u v) ==> unionp s u
    with introduce _ ==> _ with
      eliminate exists (x:B.cut). s x /\ x v
      with begin
        B.cut_down x u v;
        introduce exists (x2:B.cut). s x2 /\ x2 u with x and ()
      end

(*| Every member `u` of the union of a set of cuts has a strictly greater member.

    A helper for `FStar.Real.Dedekind.Sup.union_op`. *)
let union_op_aux (s:cset) (u:Q.rat)
  : Lemma (requires unionp s u)
          (ensures exists (v:Q.rat). unionp s v /\ Q.lt u v)
  = eliminate exists (x:B.cut). s x /\ x u
    with begin
      let v = B.cut_above x u in
      introduce exists (x2:B.cut). s x2 /\ x2 v with x and ();
      introduce exists (v2:Q.rat). unionp s v2 /\ Q.lt u v2 with v and ()
    end

(*| The union of a set of cuts has no greatest element, in the sense of `FStar.Real.Dedekind.Base.no_greatest`. *)
let union_op (s:cset) : Lemma (B.no_greatest (unionp s))
  = B.no_greatest_intro (unionp s) (union_op_aux s)

#push-options "--z3rlimit 50"
(*| The supremum of a nonempty set of cuts that is bounded above: the union of its members, which is again a cut.

    Its members are exactly those of `unionp s`. It is an upper bound (`FStar.Real.Dedekind.Sup.csup_upper`) and the least one (`FStar.Real.Dedekind.Sup.csup_least`). This gives completeness of the reals, `FStar.Real.Dedekind.lub`. *)
let csup (s:cset)
  : Pure B.cut
      (requires cnonempty s /\ cbounded s)
      (ensures fun c -> forall (q:Q.rat). c q <==> unionp s q)
  = union_ne s; union_nf s; union_dc s; union_op s;
    B.mk_cut (unionp s)
#pop-options

(*| `csup s` is an upper bound of `s`: every cut in `s` is included in it. *)
let csup_upper (s:cset)
  : Lemma (requires cnonempty s /\ cbounded s) (ensures cupper s (csup s))
  = introduce forall (x:B.cut). s x ==> B.cle x (csup s)
    with introduce _ ==> _ with
      introduce forall (q:Q.rat). x q ==> csup s q
      with introduce _ ==> _ with
        introduce exists (x2:B.cut). s x2 /\ x2 q with x and ()

(*| `csup s` is the least upper bound of `s`: it is included in every upper bound `c` of `s`. *)
let csup_least (s:cset) (c:B.cut)
  : Lemma (requires cnonempty s /\ cbounded s /\ cupper s c)
          (ensures B.cle (csup s) c)
  = introduce forall (q:Q.rat). csup s q ==> c q
    with introduce _ ==> _ with
      eliminate exists (x:B.cut). s x /\ x q with ()
