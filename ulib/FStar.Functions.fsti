module FStar.Functions

open FStar.Fin { fin }

(* This module contains basic definitions and lemmas
about functions and sets. *)

(*| The function `f` is injective: it maps distinct arguments to distinct
    results. *)
let is_inj (#a #b : _) (f : a -> GTot b) : prop =
  forall (x1 x2 : a). f x1 == f x2 ==> x1 == x2

(*| The function `f` is surjective: every value of `b` is the image of some
    argument. *)
let is_surj (#a #b : _) (f : a -> GTot b) : prop =
  forall (y:b). exists (x:a). f x == y

(*| The function `f` is bijective: both injective and surjective. *)
let is_bij (#a #b : _) (f : a -> GTot b) : prop =
  is_inj f /\ is_surj f

(*| `y` is the image of some argument under `f`. *)
let in_image (#a #b : _) (f : a -> GTot b) (y : b) : prop =
  exists (x:a). f x == y

(*| The image of `f`: the values of `b` that are the image of some argument. *)
let image_of (#a #b : _) (f : a -> GTot b) : Type =
  y:b{in_image f y}

(*| `g` is a left inverse of `f`: `g (f x) == x` for every `x`. *)
let is_inverse_of (#a #b : _) (g : b -> GTot a) (f : a -> GTot b)  =
  forall (x:a). g (f x) == x

(*| Sets of values of `a`, represented as ghost boolean predicates. *)
let powerset (a:Type u#aa) : Type u#aa = a -> GTot bool

(*| The composition of two injective functions is injective. *)
val inj_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c)
  : Lemma (requires is_inj f /\ is_inj g)
          (ensures is_inj (fun x -> g (f x)))

(*| The composition of two surjective functions is surjective. *)
val surj_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c)
  : Lemma (requires is_surj f /\ is_surj g)
          (ensures is_surj (fun x -> g (f x)))

(*| The composition of two bijective functions is bijective. *)
val bij_comp (#a #b #c : _) (f : a -> GTot b) (g : b -> GTot c) :
 Lemma (requires is_bij f /\ is_bij g)
       (ensures is_bij (fun x -> g (f x)))

(*| Every value is in the image of a surjective function. *)
val lem_surj (#a #b : _) (f : a -> GTot b) (y : b)
  : Lemma (requires is_surj f) (ensures in_image f y)

(*| Returns the inverse of the bijective function `f`, which is itself
    bijective. *)
val inverse_of_bij (#a #b : _) (f : a -> GTot b)
  : Ghost (b -> GTot a)
          (requires is_bij f)
          (ensures fun g -> is_bij g /\ g `is_inverse_of` f /\ f `is_inverse_of` g)

(*| Returns a surjective left inverse of the injective function `f`.

    The inverse maps values outside the image of `f` to arbitrary arguments;
    `def` shows that the domain is nonempty. *)
val inverse_of_inj (#a #b : _) (f : a -> GTot b{is_inj f}) (def : a)
  : Ghost (b -> GTot a)
          (requires is_inj f)
          (ensures fun g -> is_surj g /\ g `is_inverse_of` f)

(*| The pigeonhole principle: no function from `fin n1` to `fin n2`, with
    `n2 < n1`, is injective. *)
val pigeon (n1:nat) (n2:nat{n2 < n1}) (f : fin n1 -> GTot (fin n2))
  : Lemma (~ (is_inj f))
