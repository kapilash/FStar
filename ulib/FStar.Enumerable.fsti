module FStar.Enumerable

open FStar.Fin
open FStar.Bijection
open FStar.Injection

(* This class is for enumerable types, i.e. those in a bijection
   with a prefix of the natural numbers. *)
(*| Typeclass for enumerable types: types in bijection with an initial
    segment `fin n` of the natural numbers.

    Fields:

    - `_cardinal`: the number of elements, read with `FStar.Enumerable.cardinal`.
    - `bij`: a bijection between the type and `fin _cardinal`.

    The class is `erasable`, so its operations are ghost. Instances are
    provided for `fin n`, `unit`, pairs and sums. *)
[@@erasable]
class enumerable (a:Type) = {
  _cardinal : nat;
  bij : a =~ fin _cardinal;
}

(*| The number of elements of an enumerable type. *)
let cardinal (a:Type) {| d:enumerable a |} : GTot nat = d._cardinal

(*| The index of a value in the enumeration of its type, below
    `FStar.Enumerable.cardinal a`.

    The inverse of `FStar.Enumerable.of_nat`. *)
let to_nat (#a:Type) {| d : enumerable a |} (x:a) : GTot (fin (cardinal a #_)) =
  d.bij.right x

(*| The value at a given index in the enumeration of a type.

    The inverse of `FStar.Enumerable.to_nat`. *)
let of_nat (#a:Type) {| d : enumerable a |} (x:fin (cardinal a #_)) : GTot a =
  d.bij.left x

(*| `to_nat (of_nat x) == x`: indexing after decoding is the identity.

    Triggered automatically on `to_nat (of_nat x)`. *)
val to_of_pat (#a:Type) {| d:enumerable a |} (x : fin (cardinal a #_))
  : Lemma (to_nat (of_nat x) == x)
          [SMTPat (to_nat (of_nat x))]

(*| `of_nat (to_nat x) == x`: decoding after indexing is the identity.

    Triggered automatically on `of_nat (to_nat x)`. *)
val of_to_pat (#a:Type) {| d:enumerable a |} (x : a)
  : Lemma (of_nat (to_nat x) == x)
          [SMTPat (of_nat (to_nat x))]

(*| `fin n` is enumerable with cardinal `n`, by the identity bijection. *)
instance enumerable_fin (n:nat) : enumerable (fin n) = {
  _cardinal = n;
  bij = bij_self _;
}

(*| The product of two enumerable types is enumerable; its cardinal is the
    product of the cardinals. *)
instance enumerable_prod (t1 t2 : Type)
  {| d1 : enumerable t1 |} {| d2 : enumerable t2 |}
  : enumerable (t1 & t2)
= {
  _cardinal = cardinal t1 #_ * cardinal t2 #_;
  bij = bij_prod d1.bij d2.bij `bij_comp` bij_nat_prod;
}

(*| The sum `either t1 t2` of two enumerable types is enumerable; its cardinal
    is the sum of the cardinals. *)
instance enumerable_sum (t1 t2 : Type)
  {| d1 : enumerable t1 |} {| d2 : enumerable t2 |}
  : enumerable (either t1 t2)
= {
  _cardinal = cardinal t1 #_ + cardinal t2 #_;
  bij = bij_either d1.bij d2.bij `bij_comp` bij_nat_sum _ _;
}

(*| Two enumerable types in bijection have the same cardinal. *)
val bijection_implies_equal_cardinal
  (a b : Type) {| enumerable a, enumerable b |}
  (bij : bijection a b)
  : Lemma (cardinal a #_ == cardinal b #_)

(*| If an enumerable type injects into another, its cardinal is at most the
    cardinal of the other. *)
val injection_implies_lte_cardinal
  (a b : Type) {| enumerable a, enumerable b |}
  (inj : injection a b)
  : Lemma (cardinal a #_ <= cardinal b #_)

(*| An injection between two enumerable types with the same cardinal is
    surjective, hence a bijection.

    Combine with `FStar.Bijection.bij_inj'` to obtain the bijection. *)
val injection_equal_cardinal_implies_bijection
  (a b : Type) {| enumerable a, enumerable b |}
  (inj : injection a b)
  : Lemma (requires cardinal a #_ == cardinal b #_)
          (ensures  FStar.Functions.is_surj inj.f)

(*| `unit` is enumerable with cardinal `1`. *)
instance enumerable_unit : enumerable unit = {
  _cardinal = 1;
  bij = bij_unit_fin1;
}
