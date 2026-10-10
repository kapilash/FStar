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
module FStar.Real.Dedekind.Add

/// The additive group of Dedekind cuts.
///
///   x + y  =  { a + b       | a in x, b in y }
///     - x  =  { q | exists r > 0. -q - r not in x }
///
/// The offset [r] in the definition of negation is what stops [-x] from having
/// a greatest element when [x] is the cut of a rational.
///
/// Nothing is assumed here; see [FStar.Real.Dedekind.Base] for the (purely
/// logical) axioms the development rests on.

module Q = FStar.Rational
module B = FStar.Real.Dedekind.Base
module ID = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** Rational helpers *)

/// Each of these is stated on its own: batching them, or reasoning about them
/// inside a larger proof, is markedly slower.

(*| Strict order is preserved by adding two strict inequalities: if `a < a'` and `b < b'` then `a + b < a' + b'` (rationals, `FStar.Rational.lt` and `FStar.Rational.add`).

    A rational helper for the addition of cuts; call it explicitly. *)
let qlt_add2 (a a' b b':Q.rat)
  : Lemma (requires Q.lt a a' /\ Q.lt b b')
          (ensures Q.lt (Q.add a b) (Q.add a' b'))
  = Q.lt_add_r a a' b;
    Q.lt_add_r b b' a';
    Q.add_comm b a'; Q.add_comm b' a';
    Q.lt_trans (Q.add a b) (Q.add a' b) (Q.add a' b')

(*| Adding the same rational `b` on the left preserves and reflects strict order: `b + a < b + a'` iff `a < a'`.

    Left-hand counterpart of `FStar.Rational.lt_add_r`. *)
let qlt_add_l (a a' b:Q.rat)
  : Lemma (Q.lt (Q.add b a) (Q.add b a') <==> Q.lt a a')
  = Q.lt_add_r a a' b; Q.add_comm b a; Q.add_comm b a'

(*| Zero is a left identity for rational addition: `0 + q == q`. *)
let qadd_zero_l (q:Q.rat) : Lemma (Q.add Q.zero q == q)
  = Q.add_comm Q.zero q; Q.add_zero q

(*| Subtracting then adding `b` is the identity on rationals: `(q - b) + b == q`. *)
let qsub_add (q b:Q.rat) : Lemma (Q.add (Q.sub q b) b == q)
  = Q.add_assoc q (Q.neg b) b;
    Q.add_comm (Q.neg b) b;
    Q.add_neg b;
    Q.add_comm b (Q.neg b);
    Q.add_zero q

(*| Adding `b` on the left to `q - b` gives back `q`: `b + (q - b) == q`. *)
let qadd_sub (b q:Q.rat) : Lemma (Q.add b (Q.sub q b) == q)
  = qsub_add q b; Q.add_comm b (Q.sub q b)

(*| Adding then subtracting `b` is the identity on rationals: `(a + b) - b == a`. *)
let qadd_sub_cancel (a b:Q.rat) : Lemma (Q.sub (Q.add a b) b == a)
  = Q.add_assoc a b (Q.neg b); Q.add_neg b; Q.add_zero a

(*| Subtracting the same rational `b` preserves and reflects strict order: `q' - b < q - b` iff `q' < q`. *)
let qsub_lt (q q' b:Q.rat)
  : Lemma (Q.lt (Q.sub q' b) (Q.sub q b) <==> Q.lt q' q)
  = Q.lt_add_r q' q (Q.neg b)

(*| Rational negation distributes over addition: `-(a + b) == (-a) + (-b)`. *)
let qneg_add (a b:Q.rat) : Lemma (Q.neg (Q.add a b) == Q.add (Q.neg a) (Q.neg b))
  = Q.mul_neg Q.one (Q.add a b);
    Q.mul_comm Q.one (Q.add a b); Q.mul_one (Q.add a b);
    Q.distrib (Q.neg Q.one) a b;
    Q.mul_comm (Q.neg Q.one) a; Q.mul_neg Q.one a;
    Q.mul_comm Q.one a; Q.mul_one a;
    Q.mul_comm (Q.neg Q.one) b; Q.mul_neg Q.one b;
    Q.mul_comm Q.one b; Q.mul_one b

(*| The negation of the rational zero is zero. *)
let qneg_zero () : Lemma (Q.neg Q.zero == Q.zero)
  = Q.add_neg Q.zero; qadd_zero_l (Q.neg Q.zero)

(*| A rational is negative exactly when its negation is positive: `0 < -q` iff `q < 0`.

    See also `FStar.Real.Dedekind.Add.qneg_lt_zero'`. *)
let qneg_lt_zero (q:Q.rat) : Lemma (Q.lt Q.zero (Q.neg q) <==> Q.lt q Q.zero)
  = qneg_zero (); Q.lt_neg q Q.zero

(**** Addition *)

(*| The predicate underlying the sum of two cuts: `q` is a sum `a + b` of a member `a` of `x` and a member `b` of `y`.

    `FStar.Real.Dedekind.Add.cadd` packages it as a cut. *)
let addp (x y:B.cut) (q:Q.rat) : prop =
  exists (a b:Q.rat). x a /\ y b /\ q == Q.add a b

(*| The sum predicate `addp x y` is nonempty: it contains the sum of a member of `x` and a member of `y`.

    First of the four cut conditions for `FStar.Real.Dedekind.Add.cadd`. *)
let add_ne (x y:B.cut) : Lemma (exists (q:Q.rat). addp x y q)
  = let a = B.cut_mem x in
    let b = B.cut_mem y in
    introduce exists (q:Q.rat). addp x y q with (Q.add a b) and ()

(*| The sum predicate `addp x y` is not everything: the sum of a non-member of `x` and a non-member of `y` is not in it.

    Second of the four cut conditions for `FStar.Real.Dedekind.Add.cadd`. *)
let add_nf (x y:B.cut) : Lemma (exists (q:Q.rat). ~(addp x y q))
  = let a' = B.cut_nonmem x in
    let b' = B.cut_nonmem y in
    introduce addp x y (Q.add a' b') ==> False
    with eliminate exists (a b:Q.rat). x a /\ y b /\ Q.add a' b' == Q.add a b
      with begin
        B.mem_lt_nonmem x a a';
        B.mem_lt_nonmem y b b';
        qlt_add2 a a' b b';
        Q.lt_irrefl (Q.add a b)
      end;
    introduce exists (q:Q.rat). ~(addp x y q) with (Q.add a' b') and ()

(*| The sum predicate `addp x y` is downward closed: if `v` is in it and `u < v` then `u` is in it.

    Third of the four cut conditions for `FStar.Real.Dedekind.Add.cadd`. *)
let add_dc (x y:B.cut)
  : Lemma (forall (u v:Q.rat). (addp x y v /\ Q.lt u v) ==> addp x y u)
  = introduce forall (u v:Q.rat). (addp x y v /\ Q.lt u v) ==> addp x y u
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat). x a /\ y b /\ v == Q.add a b
      with begin
        qsub_add u b;
        qadd_sub_cancel a b;
        qsub_lt v u b;
        B.cut_down x (Q.sub u b) a;
        introduce exists (a2 b2:Q.rat). x a2 /\ y b2 /\ u == Q.add a2 b2
        with (Q.sub u b) b and ()
      end

(*| Every member `u` of `addp x y` has a strictly larger member, obtained by enlarging the `x` summand within `x`.

    Pointwise form of the no-greatest-element condition, consumed by `FStar.Real.Dedekind.Add.add_op`. *)
let add_op_aux (x y:B.cut) (u:Q.rat)
  : Lemma (requires addp x y u)
          (ensures exists (v:Q.rat). addp x y v /\ Q.lt u v)
  = eliminate exists (a b:Q.rat). x a /\ y b /\ u == Q.add a b
    with begin
      let a2 = B.cut_above x a in
      Q.lt_add_r a a2 b;
      introduce exists (v:Q.rat). addp x y v /\ Q.lt u v
      with (Q.add a2 b) and ()
    end

(*| The sum predicate `addp x y` has no greatest element (`FStar.Real.Dedekind.Base.no_greatest`).

    Last of the four cut conditions for `FStar.Real.Dedekind.Add.cadd`. *)
let add_op (x y:B.cut) : Lemma (B.no_greatest (addp x y))
  = B.no_greatest_intro (addp x y) (add_op_aux x y)

(*| The sum of two Dedekind cuts: the cut of all rationals `a + b` with `a` in `x` and `b` in `y`.

    Its refinement states membership as `FStar.Real.Dedekind.Add.addp`. It is the addition of the real numbers built in `FStar.Real.Dedekind`; it is commutative (`FStar.Real.Dedekind.Add.cadd_comm`), associative (`FStar.Real.Dedekind.Add.cadd_assoc`), has identity `FStar.Real.Dedekind.Add.czero` and inverses `FStar.Real.Dedekind.Add.copp`. *)
let cadd (x y:B.cut) : c:B.cut{forall (q:Q.rat). c q <==> addp x y q} =
  add_ne x y; add_nf x y; add_dc x y; add_op x y;
  B.mk_cut (addp x y)

(**** Negation *)

(*| The predicate underlying the negation of a cut: `q` is in it when, for some rational `r > 0`, `-(q + r)` is not in `x`.

    The positive offset `r` ensures the result has no greatest element even when `x` is the cut of a rational. `FStar.Real.Dedekind.Add.copp` packages it as a cut. *)
let oppp (x:B.cut) (q:Q.rat) : prop =
  exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add q r)))

(*| The negation predicate `oppp x` is nonempty: if `b` is not in `x` then `-(b + 1)` is in `oppp x`.

    First of the four cut conditions for `FStar.Real.Dedekind.Add.copp`. *)
let opp_ne (x:B.cut) : Lemma (exists (q:Q.rat). oppp x q)
  = let b = B.cut_nonmem x in
    let q = Q.neg (Q.add b Q.one) in
    Q.of_int_lt 0 1;
    qneg_add b Q.one;
    Q.neg_neg b; Q.neg_neg Q.one;
    Q.add_assoc (Q.neg b) (Q.neg Q.one) Q.one;
    Q.add_comm (Q.neg Q.one) Q.one;
    Q.add_neg Q.one;
    Q.add_comm Q.one (Q.neg Q.one);
    Q.add_zero (Q.neg b);
    qneg_add (Q.neg b) (Q.neg Q.one);
    introduce exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add q r)))
    with Q.one and ();
    introduce exists (q:Q.rat). oppp x q with q and ()

(*| The negation predicate `oppp x` is not everything: for a member `a` of `x`, `-a` is not in `oppp x`.

    Second of the four cut conditions for `FStar.Real.Dedekind.Add.copp`. *)
let opp_nf (x:B.cut) : Lemma (exists (q:Q.rat). ~(oppp x q))
  = let a = B.cut_mem x in
    introduce oppp x (Q.neg a) ==> False
    with eliminate exists (r:Q.rat). Q.lt Q.zero r /\
                             ~(x (Q.neg (Q.add (Q.neg a) r)))
      with begin
        qneg_add (Q.neg a) r;
        Q.neg_neg a;
        Q.lt_add_r Q.zero r (Q.neg r);
        Q.add_neg r;
        qadd_zero_l (Q.neg r);
        qlt_add_l (Q.neg r) Q.zero a;
        Q.add_zero a;
        B.cut_down x (Q.add a (Q.neg r)) a
      end;
    introduce exists (q:Q.rat). ~(oppp x q) with (Q.neg a) and ()

(*| The negation predicate `oppp x` is downward closed: if `v` is in it and `u < v` then `u` is in it.

    Third of the four cut conditions for `FStar.Real.Dedekind.Add.copp`. *)
let opp_dc (x:B.cut)
  : Lemma (forall (u v:Q.rat). (oppp x v /\ Q.lt u v) ==> oppp x u)
  = introduce forall (u v:Q.rat). (oppp x v /\ Q.lt u v) ==> oppp x u
    with introduce _ ==> _ with
      eliminate exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add v r)))
      with begin
        let s = Q.add r (Q.sub v u) in
        qsub_lt v u u;
        Q.add_neg u;
        qlt_add_l Q.zero (Q.sub v u) r;
        Q.add_zero r;
        Q.lt_trans Q.zero r s;
        Q.add_assoc u r (Q.sub v u);
        Q.add_comm r (Q.sub v u);
        Q.add_assoc u (Q.sub v u) r;
        qadd_sub u v;
        introduce exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add u r)))
        with s and ()
      end

(*| Every member `u` of `oppp x` has a strictly larger member, obtained by moving half of the offset `r` into the rational.

    Pointwise form of the no-greatest-element condition, consumed by `FStar.Real.Dedekind.Add.opp_op`. *)
let opp_op_aux (x:B.cut) (u:Q.rat)
  : Lemma (requires oppp x u)
          (ensures exists (v:Q.rat). oppp x v /\ Q.lt u v)
  = eliminate exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add u r)))
    with begin
      let s = Q.mid Q.zero r in
      Q.mid_spec Q.zero r;
      let v = Q.add u (Q.sub r s) in
      qsub_lt r s s;
      Q.add_neg s;
      qlt_add_l Q.zero (Q.sub r s) u;
      Q.add_zero u;
      Q.add_assoc u (Q.sub r s) s;
      qsub_add r s;
      introduce exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add v r)))
      with s and ();
      introduce exists (v:Q.rat). oppp x v /\ Q.lt u v with v and ()
    end

(*| The negation predicate `oppp x` has no greatest element (`FStar.Real.Dedekind.Base.no_greatest`).

    Last of the four cut conditions for `FStar.Real.Dedekind.Add.copp`. *)
let opp_op (x:B.cut) : Lemma (B.no_greatest (oppp x))
  = B.no_greatest_intro (oppp x) (opp_op_aux x)

(*| The negation (additive inverse) of a Dedekind cut, with membership given by `FStar.Real.Dedekind.Add.oppp`.

    `cadd x (copp x) == czero` is `FStar.Real.Dedekind.Add.cadd_opp`, and on rationals it agrees with `FStar.Rational.neg` (`FStar.Real.Dedekind.Add.rat_opp`). *)
let copp (x:B.cut) : c:B.cut{forall (q:Q.rat). c q <==> oppp x q} =
  opp_ne x; opp_nf x; opp_dc x; opp_op x;
  B.mk_cut (oppp x)

(**** More rational rearrangements *)

(*| Rational rearrangement swapping the last two summands: `(p + q) + r == (p + r) + q`. *)
let ac_shuffle (p q r:Q.rat)
  : Lemma (Q.add (Q.add p q) r == Q.add (Q.add p r) q)
  = Q.add_assoc p q r; Q.add_comm q r; Q.add_assoc p r q

(*| A rational plus its negation on the left is zero: `(-b) + b == 0`. *)
let qadd_neg_l (b:Q.rat) : Lemma (Q.add (Q.neg b) b == Q.zero)
  = Q.add_neg b; Q.add_comm b (Q.neg b)

(*| Rational rearrangement: `(-(b + r)) + b == -r`.

    Used to show that `cadd x (copp x)` contains only negative rationals (`FStar.Real.Dedekind.Add.cadd_opp_sub`). *)
let qcancel2 (b r:Q.rat)
  : Lemma (Q.add (Q.neg (Q.add b r)) b == Q.neg r)
  = qneg_add b r;
    ac_shuffle (Q.neg b) (Q.neg r) b;
    qadd_neg_l b;
    qadd_zero_l (Q.neg r)

(*| Rational rearrangement: `-((-(a + r)) + r) == a`.

    Used to check that a rational built from an approximation of `x` belongs to `copp x` (`FStar.Real.Dedekind.Add.cadd_opp_sub'`). *)
let qcancel1 (a r:Q.rat)
  : Lemma (Q.neg (Q.add (Q.neg (Q.add a r)) r) == a)
  = qneg_add a r;
    Q.add_assoc (Q.neg a) (Q.neg r) r;
    qadd_neg_l r;
    Q.add_zero (Q.neg a);
    Q.neg_neg a

(*| Rational rearrangement: `a + (-((a + e) + r)) == -(e + r)`.

    Used to decompose a negative rational as a sum of a member of `x` and a member of `copp x` (`FStar.Real.Dedekind.Add.cadd_opp_sub'`). *)
let qcancel3 (a e r:Q.rat)
  : Lemma (Q.add a (Q.neg (Q.add (Q.add a e) r)) == Q.neg (Q.add e r))
  = Q.add_assoc a e r;
    qneg_add a (Q.add e r);
    Q.add_assoc a (Q.neg a) (Q.neg (Q.add e r));
    Q.add_neg a;
    qadd_zero_l (Q.neg (Q.add e r))

(*| A rational is positive exactly when its negation is negative: `-r < 0` iff `0 < r`.

    See also `FStar.Real.Dedekind.Add.qneg_lt_zero`. *)
let qneg_lt_zero' (r:Q.rat) : Lemma (Q.lt (Q.neg r) Q.zero <==> Q.lt Q.zero r)
  = qneg_zero (); Q.lt_neg Q.zero r

(**** Commutativity *)

(*| One inclusion of commutativity of cut addition: `cadd x y` is below `cadd y x` for `FStar.Real.Dedekind.Base.cle`.

    Used twice by `FStar.Real.Dedekind.Add.cadd_comm`. *)
let cadd_comm_sub (x y:B.cut) : Lemma (B.cle (cadd x y) (cadd y x))
  = introduce forall (q:Q.rat). cadd x y q ==> cadd y x q
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat). x a /\ y b /\ q == Q.add a b
      with begin
        Q.add_comm a b;
        introduce exists (a2 b2:Q.rat). y a2 /\ x b2 /\ q == Q.add a2 b2
        with b a and ()
      end

(*| Addition of cuts is commutative: `cadd x y == cadd y x`.

    This is propositional equality of cuts, obtained from antisymmetry of `FStar.Real.Dedekind.Base.cle`. *)
let cadd_comm (x y:B.cut) : Lemma (cadd x y == cadd y x)
  = cadd_comm_sub x y; cadd_comm_sub y x;
    B.cle_antisym (cadd x y) (cadd y x)

(**** Associativity *)

(*| One inclusion of associativity of cut addition: `cadd (cadd x y) z` is below `cadd x (cadd y z)`.

    Used by `FStar.Real.Dedekind.Add.cadd_assoc`. *)
let cadd_assoc_sub (x y z:B.cut)
  : Lemma (B.cle (cadd (cadd x y) z) (cadd x (cadd y z)))
  = introduce forall (q:Q.rat). cadd (cadd x y) z q ==> cadd x (cadd y z) q
    with introduce _ ==> _ with
      eliminate exists (u c:Q.rat). cadd x y u /\ z c /\ q == Q.add u c
      with eliminate exists (a b:Q.rat). x a /\ y b /\ u == Q.add a b
      with begin
        Q.add_assoc a b c;
        introduce exists (b2 c2:Q.rat). y b2 /\ z c2 /\ Q.add b c == Q.add b2 c2
        with b c and ();
        introduce exists (a2 u2:Q.rat). x a2 /\ cadd y z u2 /\ q == Q.add a2 u2
        with a (Q.add b c) and ()
      end

(*| The other inclusion of associativity of cut addition: `cadd x (cadd y z)` is below `cadd (cadd x y) z`.

    Used by `FStar.Real.Dedekind.Add.cadd_assoc`. *)
let cadd_assoc_sub' (x y z:B.cut)
  : Lemma (B.cle (cadd x (cadd y z)) (cadd (cadd x y) z))
  = introduce forall (q:Q.rat). cadd x (cadd y z) q ==> cadd (cadd x y) z q
    with introduce _ ==> _ with
      eliminate exists (a u:Q.rat). x a /\ cadd y z u /\ q == Q.add a u
      with eliminate exists (b c:Q.rat). y b /\ z c /\ u == Q.add b c
      with begin
        Q.add_assoc a b c;
        introduce exists (a2 b2:Q.rat). x a2 /\ y b2 /\ Q.add a b == Q.add a2 b2
        with a b and ();
        introduce exists (u2 c2:Q.rat). cadd x y u2 /\ z c2 /\ q == Q.add u2 c2
        with (Q.add a b) c and ()
      end

(*| Addition of cuts is associative: `cadd (cadd x y) z == cadd x (cadd y z)`. *)
let cadd_assoc (x y z:B.cut)
  : Lemma (cadd (cadd x y) z == cadd x (cadd y z))
  = cadd_assoc_sub x y z; cadd_assoc_sub' x y z;
    B.cle_antisym (cadd (cadd x y) z) (cadd x (cadd y z))

(**** Zero *)

(*| The zero cut: the cut of the rational `0`, that is the negative rationals.

    Identity for `FStar.Real.Dedekind.Add.cadd` (`FStar.Real.Dedekind.Add.cadd_zero`). *)
let czero : B.cut = B.rat_cut Q.zero

(*| One inclusion of the identity law: `cadd x czero` is below `x`, since adding a negative rational to a member of `x` stays in `x`.

    Used by `FStar.Real.Dedekind.Add.cadd_zero`. *)
let cadd_zero_sub (x:B.cut) : Lemma (B.cle (cadd x czero) x)
  = introduce forall (q:Q.rat). cadd x czero q ==> x q
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat). x a /\ czero b /\ q == Q.add a b
      with begin
        B.rat_cut_mem Q.zero b;
        qlt_add_l b Q.zero a;
        Q.add_zero a;
        B.cut_down x q a
      end

(*| The other inclusion of the identity law: `x` is below `cadd x czero`, since every member of `x` is a larger member plus a negative rational.

    Used by `FStar.Real.Dedekind.Add.cadd_zero`. *)
let cadd_zero_sub' (x:B.cut) : Lemma (B.cle x (cadd x czero))
  = introduce forall (q:Q.rat). x q ==> cadd x czero q
    with introduce _ ==> _ with begin
      let a = B.cut_above x q in
      qsub_lt a q a;
      Q.add_neg a;
      B.rat_cut_mem Q.zero (Q.sub q a);
      qadd_sub a q;
      introduce exists (a2 b2:Q.rat). x a2 /\ czero b2 /\ q == Q.add a2 b2
      with a (Q.sub q a) and ()
    end

(*| Zero is a right identity for addition of cuts: `cadd x czero == x`.

    For the left identity see `FStar.Real.Dedekind.Mul.cadd_zero_l`. *)
let cadd_zero (x:B.cut) : Lemma (cadd x czero == x)
  = cadd_zero_sub x; cadd_zero_sub' x;
    B.cle_antisym (cadd x czero) x

(**** Inverses *)

(*| One inclusion of the inverse law: every member of `cadd x (copp x)` is a negative rational, so the sum is below `czero`.

    Used by `FStar.Real.Dedekind.Add.cadd_opp`. *)
let cadd_opp_sub (x:B.cut) : Lemma (B.cle (cadd x (copp x)) czero)
  = introduce forall (q:Q.rat). cadd x (copp x) q ==> czero q
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat). x a /\ copp x b /\ q == Q.add a b
      with eliminate exists (r:Q.rat). Q.lt Q.zero r /\ ~(x (Q.neg (Q.add b r)))
      with begin
        B.mem_lt_nonmem x a (Q.neg (Q.add b r));
        Q.lt_add_r a (Q.neg (Q.add b r)) b;
        qcancel2 b r;
        qneg_lt_zero' r;
        Q.lt_trans q (Q.neg r) Q.zero;
        B.rat_cut_mem Q.zero q
      end

(*| The other inclusion of the inverse law: every negative rational is in `cadd x (copp x)`.

    The proof uses the approximation lemma `FStar.Real.Dedekind.Base.approx` to find a member and a non-member of `x` that are close together. Used by `FStar.Real.Dedekind.Add.cadd_opp`. *)
let cadd_opp_sub' (x:B.cut) : Lemma (B.cle czero (cadd x (copp x)))
  = introduce forall (q:Q.rat). czero q ==> cadd x (copp x) q
    with introduce _ ==> _ with begin
      B.rat_cut_mem Q.zero q;
      qneg_lt_zero q;
      let e = Q.mid Q.zero (Q.neg q) in
      Q.mid_spec Q.zero (Q.neg q);
      let r = Q.sub (Q.neg q) e in
      qsub_lt (Q.neg q) e e;
      Q.add_neg e;
      let ab = B.approx x e in
      let a = fst ab in
      let a' = snd ab in
      let b = Q.neg (Q.add a' r) in
      qcancel1 a' r;
      introduce exists (r2:Q.rat). Q.lt Q.zero r2 /\ ~(x (Q.neg (Q.add b r2)))
      with r and ();
      qcancel3 a e r;
      qadd_sub e (Q.neg q);
      Q.neg_neg q;
      introduce exists (a2 b2:Q.rat). x a2 /\ copp x b2 /\ q == Q.add a2 b2
      with a b and ()
    end

(*| A cut plus its negation is zero: `cadd x (copp x) == czero`.

    For the left inverse see `FStar.Real.Dedekind.Mul.cadd_opp_l`. *)
let cadd_opp (x:B.cut) : Lemma (cadd x (copp x) == czero)
  = cadd_opp_sub x; cadd_opp_sub' x;
    B.cle_antisym (cadd x (copp x)) czero

(**** Compatibility of addition with the order *)

(*| Rational rearrangement: `q + (c + (q2 - q)) == q2 + c`.

    Used by `FStar.Real.Dedekind.Add.cadd_mono`. *)
let qshift (q q2 c:Q.rat)
  : Lemma (Q.add q (Q.add c (Q.sub q2 q)) == Q.add q2 c)
  = Q.add_comm c (Q.sub q2 q);
    Q.add_assoc q (Q.sub q2 q) c;
    qadd_sub q q2

(*| Adding the same cut preserves strict order: if `clt x y` then `clt (cadd x z) (cadd y z)`.

    See `FStar.Real.Dedekind.Add.cadd_mono_rev` for the equivalence. *)
let cadd_mono (x y z:B.cut)
  : Lemma (requires B.clt x y) (ensures B.clt (cadd x z) (cadd y z))
  = let q = B.clt_witness x y in
    let q2 = B.cut_above y q in
    let e = Q.sub q2 q in
    qsub_lt q2 q q;
    Q.add_neg q;
    let cc = B.approx z e in
    let c = fst cc in
    let c' = snd cc in
    let w = Q.add q2 c in
    introduce exists (a2 b2:Q.rat). y a2 /\ z b2 /\ w == Q.add a2 b2
    with q2 c and ();
    introduce cadd x z w ==> False
    with eliminate exists (a b:Q.rat). x a /\ z b /\ w == Q.add a b
    with begin
      B.mem_lt_nonmem x a q;
      B.mem_lt_nonmem z b c';
      qlt_add2 a q b c';
      qshift q q2 c;
      Q.lt_irrefl w
    end;
    B.clt_of_witness (cadd x z) (cadd y z) w

(*| Adding the same cut on the right preserves and reflects strict order: `clt (cadd x z) (cadd y z)` iff `clt x y`.

    The reverse direction uses totality of the order (`FStar.Real.Dedekind.Base.clt_total`). *)
let cadd_mono_rev (x y z:B.cut)
  : Lemma (B.clt (cadd x z) (cadd y z) <==> B.clt x y)
  = introduce B.clt x y ==> B.clt (cadd x z) (cadd y z)
    with cadd_mono x y z;
    introduce B.clt (cadd x z) (cadd y z) ==> B.clt x y
    with begin
      B.clt_total x y;
      B.clt_irrefl (cadd x z);
      introduce B.clt y x ==> B.clt x y
      with begin
        cadd_mono y x z;
        B.clt_trans (cadd x z) (cadd y z) (cadd x z);
        B.clt_irrefl (cadd x z)
      end
    end

(**** The embedding is additive *)

(*| Rational rearrangement exchanging the subtracted terms of an inequality: `t - a < q` iff `t - q < a`. *)
let qsub_flip (t a q:Q.rat)
  : Lemma (Q.lt (Q.sub t a) q <==> Q.lt (Q.sub t q) a)
  = Q.lt_add_r (Q.sub t a) q (Q.sub a q);
    qadd_sub q a;
    Q.add_assoc (Q.sub t a) a (Q.neg q);
    qsub_add t a

(*| One inclusion of additivity of the embedding: `rat_cut (p + q)` is below `cadd (rat_cut p) (rat_cut q)`.

    Used by `FStar.Real.Dedekind.Add.rat_add`. *)
let rat_add_sub (p q:Q.rat)
  : Lemma (B.cle (B.rat_cut (Q.add p q)) (cadd (B.rat_cut p) (B.rat_cut q)))
  = introduce forall (t:Q.rat).
        B.rat_cut (Q.add p q) t ==> cadd (B.rat_cut p) (B.rat_cut q) t
    with introduce _ ==> _ with begin
      B.rat_cut_mem (Q.add p q) t;
      qsub_add t q;
      Q.lt_add_r (Q.sub t q) p q;
      let a = Q.mid (Q.sub t q) p in
      Q.mid_spec (Q.sub t q) p;
      let b = Q.sub t a in
      qsub_flip t a q;
      qadd_sub a t;
      B.rat_cut_mem p a;
      B.rat_cut_mem q b;
      introduce exists (a2 b2:Q.rat).
          B.rat_cut p a2 /\ B.rat_cut q b2 /\ t == Q.add a2 b2
      with a b and ()
    end

(*| The other inclusion of additivity of the embedding: `cadd (rat_cut p) (rat_cut q)` is below `rat_cut (p + q)`.

    Used by `FStar.Real.Dedekind.Add.rat_add`. *)
let rat_add_sub' (p q:Q.rat)
  : Lemma (B.cle (cadd (B.rat_cut p) (B.rat_cut q)) (B.rat_cut (Q.add p q)))
  = introduce forall (t:Q.rat).
        cadd (B.rat_cut p) (B.rat_cut q) t ==> B.rat_cut (Q.add p q) t
    with introduce _ ==> _ with
      eliminate exists (a b:Q.rat).
          B.rat_cut p a /\ B.rat_cut q b /\ t == Q.add a b
      with begin
        B.rat_cut_mem p a;
        B.rat_cut_mem q b;
        qlt_add2 a p b q;
        B.rat_cut_mem (Q.add p q) t
      end

(*| The embedding of the rationals into cuts is additive: `rat_cut (p + q) == cadd (rat_cut p) (rat_cut q)`.

    Here `rat_cut` is `FStar.Real.Dedekind.Base.rat_cut`. *)
let rat_add (p q:Q.rat)
  : Lemma (B.rat_cut (Q.add p q) == cadd (B.rat_cut p) (B.rat_cut q))
  = rat_add_sub p q; rat_add_sub' p q;
    B.cle_antisym (B.rat_cut (Q.add p q)) (cadd (B.rat_cut p) (B.rat_cut q))

(**** The embedding respects negation *)

(*| Negation swaps a strict rational inequality: `t < -p` iff `p < -t`. *)
let qneg_lt (t p:Q.rat) : Lemma (Q.lt t (Q.neg p) <==> Q.lt p (Q.neg t))
  = Q.lt_neg t (Q.neg p); Q.neg_neg p;
    Q.lt_neg p (Q.neg t); Q.neg_neg t

(*| One inclusion of the embedding respecting negation: `rat_cut (-p)` is below `copp (rat_cut p)`.

    Used by `FStar.Real.Dedekind.Add.rat_opp`. *)
let rat_opp_sub (p:Q.rat)
  : Lemma (B.cle (B.rat_cut (Q.neg p)) (copp (B.rat_cut p)))
  = introduce forall (t:Q.rat). B.rat_cut (Q.neg p) t ==> copp (B.rat_cut p) t
    with introduce _ ==> _ with begin
      B.rat_cut_mem (Q.neg p) t;
      qneg_lt t p;
      let r = Q.mid Q.zero (Q.sub (Q.neg t) p) in
      qsub_lt (Q.neg t) p p;
      Q.add_neg p;
      Q.mid_spec Q.zero (Q.sub (Q.neg t) p);
      qsub_add (Q.neg t) p;
      Q.lt_add_r r (Q.sub (Q.neg t) p) p;
      Q.add_comm r p;
      Q.lt_add_r (Q.add p r) (Q.neg t) (Q.neg r);
      Q.add_assoc p r (Q.neg r);
      Q.add_neg r;
      Q.add_zero p;
      qneg_add t r;
      B.rat_cut_mem p (Q.neg (Q.add t r));
      Q.lt_asym p (Q.neg (Q.add t r));
      introduce exists (r2:Q.rat).
          Q.lt Q.zero r2 /\ ~(B.rat_cut p (Q.neg (Q.add t r2)))
      with r and ()
    end

(*| The other inclusion of the embedding respecting negation: `copp (rat_cut p)` is below `rat_cut (-p)`.

    Used by `FStar.Real.Dedekind.Add.rat_opp`. *)
let rat_opp_sub' (p:Q.rat)
  : Lemma (B.cle (copp (B.rat_cut p)) (B.rat_cut (Q.neg p)))
  = introduce forall (t:Q.rat). copp (B.rat_cut p) t ==> B.rat_cut (Q.neg p) t
    with introduce _ ==> _ with
      eliminate exists (r:Q.rat).
          Q.lt Q.zero r /\ ~(B.rat_cut p (Q.neg (Q.add t r)))
      with begin
        B.rat_cut_mem p (Q.neg (Q.add t r));
        qneg_add t r;
        qneg_lt_zero' r;
        Q.lt_add_r (Q.neg r) Q.zero (Q.neg t);
        qadd_zero_l (Q.neg t);
        Q.add_comm (Q.neg t) (Q.neg r);
        Q.lt_total p (Q.neg (Q.add t r));
        introduce Q.lt p (Q.neg (Q.add t r)) ==> Q.lt p (Q.neg t)
        with Q.lt_trans p (Q.neg (Q.add t r)) (Q.neg t);
        qneg_lt t p;
        B.rat_cut_mem (Q.neg p) t
      end

(*| The embedding of the rationals into cuts respects negation: `rat_cut (-p) == copp (rat_cut p)`.

    Here `rat_cut` is `FStar.Real.Dedekind.Base.rat_cut`. *)
let rat_opp (p:Q.rat)
  : Lemma (B.rat_cut (Q.neg p) == copp (B.rat_cut p))
  = rat_opp_sub p; rat_opp_sub' p;
    B.cle_antisym (B.rat_cut (Q.neg p)) (copp (B.rat_cut p))
