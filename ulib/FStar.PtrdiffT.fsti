module FStar.PtrdiffT

module I16 = FStar.Int16
module US = FStar.SizeT

(*| The type of pointer differences, modelling C's `ptrdiff_t`.

    `t` is abstract, with decidable equality. Its values are exactly the
    integers `x` such that `FStar.PtrdiffT.fits x`, read with
    `FStar.PtrdiffT.v`. The width is a platform parameter that the interface
    does not fix. The F\* implementation is only a model; KaRaMeL extracts
    `t` natively to C's `ptrdiff_t`.

    ```fstar
    let hundred : FStar.PtrdiffT.t = FStar.PtrdiffT.mk 100s
    ``` *)
val t : eqtype

(*| Holds when the integer `x` is representable as a `FStar.PtrdiffT.t` on
    the target platform.

    `fits` is abstract. The implementation models it as
    `min_bound <= x <= max_bound` for an assumed, platform-dependent
    `max_bound` of at least `pow2 15 - 1`, with `min_bound` equal to
    `- (max_bound + 1)`; none of this is exported. Clients only know that
    fitting is closed under decreasing the absolute value
    (`FStar.PtrdiffT.fits_lt`) and that every value of `t`, in particular
    every value built by `FStar.PtrdiffT.mk` from a 16-bit integer, fits. No
    upper bound is exposed. *)
val fits (x: int) : Tot prop

(*| If `y` fits and `abs x < abs y`, then `x` fits.

    Triggered automatically when both `FStar.PtrdiffT.fits x` and
    `FStar.PtrdiffT.fits y` appear. *)
val fits_lt (x y: int) : Lemma
  (requires (abs x < abs y /\ fits y))
  (ensures (fits x))
  [SMTPat (fits x); SMTPat (fits y)]

(*| The integer denoted by a pointer difference; the result always satisfies
    `FStar.PtrdiffT.fits`.

    `v` is a specification function: it is marked `noextract_to "krml"`, so
    code extracted to C must not use it. *)
[@@noextract_to "krml"]
val v (x: t) : Pure int
  (requires True)
  (ensures (fun y -> fits y))

(*| Converts an integer that fits into a pointer difference, with
    `v (int_to_t x) == x`.

    Requires `FStar.PtrdiffT.fits x`. Like `FStar.PtrdiffT.v` it is marked
    `noextract_to "krml"`; to build values in extracted code use
    `FStar.PtrdiffT.mk`. *)
[@@noextract_to "krml"]
val int_to_t (x: int) : Pure t
  (requires (fits x))
  (ensures (fun y -> v y == x))

/// v and int_to_t are inverses
(*| Converting the value of a pointer difference back gives the same value:
    `int_to_t (v x) == x`.

    Triggered automatically on `FStar.PtrdiffT.v x`. *)
val ptrdiff_v_inj (x: t)
  : Lemma
    (ensures int_to_t (v x) == x)
    [SMTPat (v x)]

(*| The value of `int_to_t x` is `x`, for any `x` that fits.

    Triggered automatically on `FStar.PtrdiffT.int_to_t x`. *)
val ptrdiff_int_to_t_inj (x: int)
  : Lemma
    (requires fits x)
    (ensures v (int_to_t x) == x)
    [SMTPat (int_to_t x)]

/// According to the C standard, "the bit width of ptrdiff_t is not less than 17 since c99,
/// 16 since C23"
/// (https://en.cppreference.com/w/c/types/ptrdiff_t)
/// We therefore only offer a function to create a ptrdiff_t when we are sure it fits
(*| Builds a pointer difference from a 16-bit signed integer, preserving its
    value.

    Always defined: C guarantees that `ptrdiff_t` is at least 16 bits wide
    (17 bits before C23), so this is the only constructor that needs no
    proof. It is `noextract` and `inline_for_extraction`. *)
noextract inline_for_extraction
val mk (x: I16.t) : Pure t
  (requires True)
  (ensures (fun y -> v y == I16.v x))

(*| The pointer difference `0`, built with `FStar.PtrdiffT.mk`. *)
noextract inline_for_extraction
let zero : (zero_ptrdiff: t { v zero_ptrdiff == 0 }) =
  mk 0s

(*| Casts a non-negative pointer difference to a size, preserving its value.

    The argument must satisfy `v x >= 0`; the cast is restricted to
    non-negative values to avoid reasoning about modular arithmetic. The
    result is a `FStar.SizeT.t` with `FStar.SizeT.v` equal to `v x`.

    ```fstar
    let to_size (x: FStar.PtrdiffT.t{FStar.PtrdiffT.v x >= 0}) : FStar.SizeT.t =
      FStar.PtrdiffT.ptrdifft_to_sizet x
    ``` *)
val ptrdifft_to_sizet (x:t{v x >= 0}) : Pure US.t
  (requires True)
  (ensures fun c -> v x == US.v c)

(*| Sum of two pointer differences: `v (add x y) == v x + v y`.

    Requires the sum to fit (`FStar.PtrdiffT.fits (v x + v y)`); there is no
    wrapping variant. Infix: `FStar.PtrdiffT.op_Plus`. *)
val add (x y: t) : Pure t
  (requires (fits (v x + v y)))
  (ensures (fun z -> v z == v x + v y))

(*| Quotient of a non-negative pointer difference by a positive one:
    `v (div a b) == v a / v b`.

    Requires `v a >= 0` and `v b > 0`. Like `FStar.PtrdiffT.rem`, division
    is only offered on these arguments, so that no overflow can occur; on
    them, truncating and rounding-down division coincide. *)
val div (a:t{v a >= 0}) (b:t{v b > 0}) : Pure t
  (requires True)
  (ensures fun c -> v a / v b == v c)

(*| Specification of the remainder of `a` by a non-zero `b`, as
    `a - (a / b) * b`.

    With F\*'s `/`, this is `a % b`, a value in `[0, abs b)` that is known to
    fit. Ghost (`GTot`); used to specify `FStar.PtrdiffT.rem`, in the style
    of `FStar.Int.mod` (which, unlike this function, truncates towards zero). *)
let mod_spec (a:int{fits a}) (b:int{fits b /\ b <> 0}) : GTot (n:int{fits n}) =
  let res = a - ((a/b) * b) in
  fits_lt res b;
  res

(*| Remainder of a non-negative pointer difference by a positive one:
    `v (rem a b) == mod_spec (v a) (v b)`, that is `v a % v b`.

    Requires `v a >= 0` and `v b > 0`. C defines the remainder only when the
    quotient is representable; restricting to these arguments avoids a
    `fits (v a / v b)` precondition. *)
val rem (a:t{v a >= 0}) (b:t{v b > 0}) : Pure t
  (requires True)
  (ensures (fun c -> mod_spec (v a) (v b) = v c))

(*| Strict greater-than test on pointer differences, returning `v x > v y`.
    Infix: `FStar.PtrdiffT.op_Greater`. *)
val gt (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x > v y)))

(*| Greater-than-or-equal test on pointer differences, returning
    `v x >= v y`. Infix: `FStar.PtrdiffT.op_Greater_Equals`. *)
val gte (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x >= v y)))

(*| Strict less-than test on pointer differences, returning `v x < v y`.
    Infix: `FStar.PtrdiffT.op_Less`. *)
val lt (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x < v y)))

(*| Less-than-or-equal test on pointer differences, returning `v x <= v y`.
    Infix: `FStar.PtrdiffT.op_Less_Equals`. *)
val lte (x y: t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x <= v y)))

(* Infix notations *)

(*| Infix notation for `FStar.PtrdiffT.add`; requires the sum to fit. *)
inline_for_extraction unfold let ( + ) = add
(*| Infix notation for `FStar.PtrdiffT.gt`. *)
inline_for_extraction unfold let ( > ) = gt
(*| Infix notation for `FStar.PtrdiffT.gte`. *)
inline_for_extraction unfold let ( >= ) = gte
(*| Infix notation for `FStar.PtrdiffT.lt`. *)
inline_for_extraction unfold let ( < ) = lt
(*| Infix notation for `FStar.PtrdiffT.lte`. *)
inline_for_extraction unfold let ( <= ) = lte

(* Deprecated infix notations: the spellings the five operators above had
   before type-based overloading made the [^] suffix unnecessary. *)
(*| Deprecated spelling of `FStar.PtrdiffT.op_Plus` (`FStar.PtrdiffT.add`). *)
[@@deprecated "use ( + )"]  inline_for_extraction unfold let ( +^ )  = add
(*| Deprecated spelling of `FStar.PtrdiffT.op_Greater` (`FStar.PtrdiffT.gt`). *)
[@@deprecated "use ( > )"]  inline_for_extraction unfold let ( >^ )  = gt
(*| Deprecated spelling of `FStar.PtrdiffT.op_Greater_Equals`
    (`FStar.PtrdiffT.gte`). *)
[@@deprecated "use ( >= )"] inline_for_extraction unfold let ( >=^ ) = gte
(*| Deprecated spelling of `FStar.PtrdiffT.op_Less` (`FStar.PtrdiffT.lt`). *)
[@@deprecated "use ( < )"]  inline_for_extraction unfold let ( <^ )  = lt
(*| Deprecated spelling of `FStar.PtrdiffT.op_Less_Equals`
    (`FStar.PtrdiffT.lte`). *)
[@@deprecated "use ( <= )"] inline_for_extraction unfold let ( <=^ ) = lte
