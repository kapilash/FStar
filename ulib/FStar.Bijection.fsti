module FStar.Bijection

open FStar.Ghost
open FStar.Fin { fin }
open FStar.Injection

(*| Composition of total functions: `o g f` maps `x` to `g (f x)`.

    `FStar.Bijection.oo` is the ghost variant. *)
let o #a #b #c (g : b -> Tot c) (f : a -> Tot b) : a -> Tot c = fun x -> g (f x)
(*| Composition of ghost functions: `oo g f` maps `x` to `g (f x)`.

    `FStar.Bijection.o` is the total variant. *)
let oo #a #b #c (g : b -> GTot c) (f : a -> GTot b) : a -> GTot c = fun x -> g (f x)

(* Note: bijections are erasable. For an executable version,
see cbij below. *)
(*| A bijection between `a` and `b`, as a pair of mutually inverse ghost
    functions; usually written `a =~ b`.

    Fields:

    - `right`: the function from `a` to `b`.
    - `left`: the function from `b` to `a`.
    - `left_right`: `left (right x) == x` for every `x`.
    - `right_left`: `right (left y) == y` for every `y`.

    The type is `erasable`, and its functions are ghost. For a computationally
    relevant version, see `FStar.Bijection.cbij`. *)
noeq
[@@erasable]
type bijection (a b : Type) = {
  (* Functions between the types, the name indicates
  the direction we're "moving" in *)
  right : a -> GTot b;
  left  : b -> GTot a;

  (* Proofs that the functions are inverses of each other. As
  usual the name here is a tough choice. We call the first one
  "right_left" because it says something about "right (left x)". *)
  left_right : x:a -> squash (left (right x) == x);
  right_left : y:b -> squash (right (left y) == y);
}

(*| Notation: `a =~ b` is `FStar.Bijection.bijection a b`. *)
let ( =~ ) a b = bijection a b

(*| Going right then left through a bijection is the identity:
    `d.left (d.right x) == x`.

    Triggered automatically on `d.right x`. *)
val bij_inv_fwd (#a #b : _) (d : a =~ b) (x:a)
  : Lemma (x == d.left (d.right x))
          [SMTPat (d.right x)]

(*| Going left then right through a bijection is the identity:
    `d.right (d.left y) == y`.

    Triggered automatically on `d.left y`. *)
val bij_inv_bk (#a #b : _) (d : a =~ b) (y:b)
  : Lemma (y == d.right (d.left y))
          [SMTPat (d.left y)]

(* Sometimes useful to specify implicits. See #3804. *)
(*| Builds a bijection from two functions and the proofs that they are
    mutually inverse.

    The same as the record constructor, but with implicit type arguments,
    which sometimes helps inference. *)
let mk_bijection
  (#a #b : _)
  (right : a -> GTot b)
  (left  : b -> GTot a)
  (right_left : (x:b -> squash (right (left x) == x)))
  (left_right : (x:a -> squash (left (right x) == x)))
  : (a =~ b) =
  Mkbijection right left left_right right_left

(* Move values across bijections. *)
(*| Moves a value of `a` to `b` through a bijection: `x >> bij` is
    `bij.right x`. *)
let ( >> ) (#a #b : Type) (x : a) (bij : a =~ b) : GTot b = bij.right x
(*| Moves a value of `b` back to `a` through a bijection: `y << bij` is
    `bij.left y`. *)
let ( << ) (#a #b : Type) (x : b) (bij : a =~ b) : GTot a = bij.left x

(*| `x >> d == y` holds exactly when `x == y << d`.

    Triggered automatically when both `d.right x` and `d.left y` appear. *)
val inv_lemma_pat (#a #b : _) (d : a =~ b) (x:a) (y:b)
  : Lemma ((x >> d) == y <==> x == (y << d))
          [SMTPat (d.right x); SMTPat (d.left y)]

(*| The identity bijection on `a`. *)
let bij_self (a:Type) : (a =~ a) =
{
  right = id;
  left = id;
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

(*| The inverse of a bijection, from `b` to `a`. *)
let bij_sym (#a #b : Type) (d : a =~ b) : (b =~ a) =
{
  right = d.left;
  left = d.right;
  right_left = d.left_right;
  left_right = d.right_left;
}

(*| Composition of bijections: from `a =~ b` and `b =~ c`, a bijection
    `a =~ c`. *)
let bij_comp (#a #b #c : Type) (ab : a =~ b) (bc : b =~ c) : (a =~ c) =
{
  right = bc.right `oo` ab.right;
  left = ab.left `oo` bc.left;
  right_left = (fun x -> ab.right_left (bc.left x); bc.right_left x);
  left_right = (fun x -> bc.left_right (ab.right x); ab.left_right x);
}

(*| Lifts a bijection between `a` and `b` to one between `erased a` and
    `erased b`. *)
let bij_erase (#a #b : Type) (bij : a =~ b) : (erased a =~ erased b) =
{
  right = (fun (x : erased a) -> bij.right x <: erased b);
  left = (fun (x : erased b) -> bij.left x <: erased a);
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}


(*| The bijection swapping the components of a pair, from `a & b` to `b & a`. *)
let bij_flip_prod (#a #b : Type) : (a & b =~ b & a) =
{
  right = (fun (x, y) -> (y, x));
  left = (fun (y, x) -> (x, y));
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

(*| The componentwise product of two bijections, from `a & c` to `b & d`. *)
let bij_prod (#a #b #c #d : Type) (ab : a =~ b) (cd : c =~ d) : (a & c =~ b & d) =
{
  right = (fun (x, y) -> (ab.right x, cd.right y));
  left = (fun (x, y) -> (ab.left x, cd.left y));
  right_left = (fun x ->
    let (x1, x2) = x in
    ab.right_left x1; cd.right_left x2);
  left_right = (fun x ->
    let (x1, x2) = x in
    ab.left_right x1; cd.left_right x2);
}

(*| The componentwise sum of two bijections, from `either a c` to
    `either b d`. *)
let bij_either (#a #b #c #d : Type)
  (ab : a =~ b) (cd : c =~ d) : (either a c =~ either b d) =
{
  right = (fun x -> match x with
    | Inl x -> Inl (ab.right x)
    | Inr y -> Inr (cd.right y));
  left = (fun x -> match x with
    | Inl x -> Inl (ab.left x)
    | Inr y -> Inr (cd.left y));
  left_right = (fun _ -> ());
  right_left = (fun _ -> ());
}

(*| The bijection swapping the sides of a sum, from `either a b` to
    `either b a`. *)
let bij_flip_sum (#a #b : Type) : (either a b =~ either b a) =
{
  right = (function | Inl x -> Inr x | Inr y -> Inl y);
  left = (function | Inl x -> Inr x | Inr y -> Inl y);
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

(*| The bijection between `unit` and `FStar.Fin.fin 1`. *)
let bij_unit_fin1 : bijection unit (fin 1) = {
  right = (fun _ -> 0 <: fin 1);
  left = (fun _ -> ());
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

(* weird typing errors without hoisting. *)
(*| Encodes a pair `(i, j)` of `fin n1 & fin n2` as the index `i * n2 + j` of
    `fin (n1 * n2)`.

    The forward function of `FStar.Bijection.bij_nat_prod`; the inverse is
    `FStar.Bijection.prod_left`. *)
unfold
inline_for_extraction noextract
let prod_right (n1 n2 : nat) : fin n1 & fin n2 -> fin (n1 * n2) =
  // fun (x, y) -> (x * n2 + y)
  fun xy -> (xy._1 * n2 + xy._2)

(*| Decodes an index `i` of `fin (n1 * n2)` as the pair `(i / n2, i % n2)`.

    The backward function of `FStar.Bijection.bij_nat_prod`; the inverse of
    `FStar.Bijection.prod_right`. *)
unfold
inline_for_extraction noextract
let prod_left (n1 n2 : nat) : fin (n1 * n2) -> fin n1 & fin n2 =
  fun i -> (i / n2, i % n2)

(*| The bijection between `fin n1 & fin n2` and `fin (n1 * n2)`, by
    row-major encoding (`FStar.Bijection.prod_right` and
    `FStar.Bijection.prod_left`). *)
unfold
let bij_nat_prod (#n1 #n2 : nat) : (fin n1 & fin n2 =~ fin (n1 * n2)) =
{
  right = prod_right n1 n2;
  left = prod_left n1 n2;
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

(*| A bijection between `fin n1` and `fin n2` implies `n1 == n2`.

    Prefer `FStar.Bijection.bij_cardinal`, which only needs the existence of
    a bijection. *)
val __bij_cardinal (n1 n2 : nat) (bij : fin n1 =~ fin n2)
  : Lemma (n1 == n2)

(*| If some bijection between `fin n1` and `fin n2` exists, then `n1 == n2`. *)
val bij_cardinal (n1 n2 : nat)
  : Lemma (requires exists (b : fin n1 =~ fin n2). True)
          (ensures n1 == n2)

(*| The bijection between `either (fin n1) (fin n2)` and `fin (n1 + n2)`:
    `Inl i` maps to `i` and `Inr j` maps to `n1 + j`. *)
let bij_nat_sum (n1 n2 : nat)
  : (either (fin n1) (fin n2) =~ fin (n1 + n2)) =
{
  right = (fun (x : either (fin n1) (fin n2)) ->
    (match x with
     | Inl i -> i
     | Inr j -> n1 + j) <: fin (n1 + n2));
  left = (fun (i : fin (n1 + n2)) ->
    if i < n1
    then Inl i
    else Inr (i - n1));
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}

(***** Computationally relevant bijections *****)

(*| A computationally relevant bijection: an erased `FStar.Bijection.bijection`
    together with executable functions that agree with it; usually written
    `a ==~ b`.

    Fields:

    - `bij`: the underlying (erased) bijection.
    - `cright`: a total function equal to `bij.right` pointwise.
    - `cleft`: a total function equal to `bij.left` pointwise.

    Built with `FStar.Bijection.mk_cbij`. *)
noeq type cbij (a b: Type) = {
  bij: (a =~ b);
  cright: cright: (a -> b) { forall x. cright x == bij.right x };
  cleft: cleft: (b -> a) { forall x. cleft x == bij.left x };
}

(*| Builds a computationally relevant bijection from two total functions and
    the proofs that they are mutually inverse. *)
let mk_cbij
  (#a #b : _)
  (right : a -> b) (left : b -> a)
  (right_left : (x:b -> squash (right (left x) == x)))
  (left_right : (x:a -> squash (left (right x) == x)))
  : cbij a b =
{
  bij = {
    right = (fun x -> right x);
    left  = (fun x -> left x);
    right_left = right_left;
    left_right = left_right;
  };
  cright = right;
  cleft = left;
}

(*| Notation: `a ==~ b` is `FStar.Bijection.cbij a b`. *)
inline_for_extraction
let (==~) = cbij

(*| The identity computationally relevant bijection on `a`. *)
inline_for_extraction noextract
let cbij_self (a:Type) : (a ==~ a) = {
  bij = bij_self _;
  cright = id;
  cleft = id;
}

(*| The componentwise product of two computationally relevant bijections, from
    `a & c` to `b & d`. *)
inline_for_extraction noextract
let cbij_prod (#a #b #c #d : Type) (ab : a ==~ b) (cd : c ==~ d) : (a & c ==~ b & d) =
{
  bij = bij_prod ab.bij cd.bij;
  cright = (fun (x, y) -> (ab.cright x, cd.cright y));
  cleft = (fun (x, y) -> (ab.cleft x, cd.cleft y));
}

(*| Composition of computationally relevant bijections: from `a ==~ b` and
    `b ==~ c`, a bijection `a ==~ c`. *)
inline_for_extraction noextract
let cbij_comp (#a #b #c : Type) (ab : a ==~ b) (bc : b ==~ c) : (a ==~ c) =
{
  bij = bij_comp ab.bij bc.bij;
  cright = (fun x -> bc.cright (ab.cright x));
  cleft = (fun x -> ab.cleft (bc.cleft x));
}


(***** Injections from bijections *****)

(*| The forward function of a bijection, as an injection from `a` to `b`. *)
let inj_bij (#a #b : Type) (bij : a =~ b) : (a @~> b) =
  {
    f = bij.right;
    is_inj = (fun _ _ _ -> ());
  }

(*| The backward function of a bijection, as an injection from `b` to `a`. *)
let inj_bij' (#a #b : Type) (bij : a =~ b) : (b @~> a) =
  {
    f = bij.left;
    is_inj = (fun _ _ _ -> ());
  }

(*| An injection from `a` to `b` is a bijection between `a` and its image
    `FStar.Injection.image_of inj`.

    The inverse is obtained classically, via `FStar.Functions.inverse_of_bij`. *)
let bij_inj (#a #b : Type) (inj : a @~> b)
  : (a =~ image_of inj)
= let right : a -> GTot (image_of inj) = (fun x -> inj.f x) in
  {
    right = right;
    left = FStar.Functions.inverse_of_bij right;
    right_left = (fun _ -> ());
    left_right = (fun _ -> ());
  }

(*| A surjective injection is a bijection.

    The caller must prove `FStar.Functions.is_surj inj.f`. The inverse is
    obtained classically, via `FStar.Functions.inverse_of_bij`. *)
let bij_inj' (#a #b : Type) (inj : a @~> b)
  : Ghost (a =~ b)
          (requires Functions.is_surj inj.f)
          (ensures fun _ -> True)
= {
  right = inj.f;
  left = FStar.Functions.inverse_of_bij inj.f;
  right_left = (fun _ -> ());
  left_right = (fun _ -> ());
}
