module FStar.SizeT


module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64

(*| The type of machine sizes, modelling C's `size_t`.

    `t` is abstract, with decidable equality. Its values are exactly the
    naturals `x` such that `FStar.SizeT.fits x`, read with `FStar.SizeT.v`
    and built with `FStar.SizeT.uint_to_t`. Literals are written with the
    `sz` suffix, as in `1sz`.

    The width of `t` is a platform parameter that the interface does not fix:
    it is only known to be at least 16 bits. The F\* implementation is only
    a model; KaRaMeL extracts `t` natively to C's `size_t`.

    ```fstar
    let small_size : FStar.SizeT.t = FStar.SizeT.uint_to_t 1000
    ``` *)
new
val t : eqtype

(*| Holds when the integer `x` is representable as a `FStar.SizeT.t` on the
    target platform.

    `fits` is abstract. The implementation models it as `0 <= x < bound`
    for an assumed, platform-dependent `bound` of at least `pow2 16`, but
    neither the definition nor `bound` is exported. Clients only know the
    following facts.

    - `fits x` implies `x >= 0` (`FStar.SizeT.fits_nonneg`).
    - Every `x < pow2 16` fits (`FStar.SizeT.fits_at_least_16`).
    - Fitting is downward closed on naturals (`FStar.SizeT.fits_lte`).
    - Under `FStar.SizeT.fits_u32`, every `x < pow2 32` fits.
    - Under `FStar.SizeT.fits_u64`, every `x < pow2 64` fits.

    No upper bound is exposed: one cannot prove that a given natural does
    not fit, nor that a value of `t` fits in 32 or 64 bits. *)
val fits (x : int) : Tot prop

(*| Only non-negative integers fit in a `FStar.SizeT.t`.

    Triggered automatically on `FStar.SizeT.fits x`. *)
val fits_nonneg (x:int)
  : Lemma (requires fits x)
          (ensures x >= 0)
          [SMTPat (fits x)]

/// According to the C standard, "the bit width of t is not less than 16 since c99"
/// (https://en.cppreference.com/w/c/types/size_t)

(*| Every natural below `pow2 16` fits in a `FStar.SizeT.t`.

    This reflects the C guarantee that `size_t` is at least 16 bits wide; it
    is the only width the interface guarantees unconditionally. Triggered
    automatically on `FStar.SizeT.fits x`. *)
val fits_at_least_16 (x:nat)
  : Lemma
    (requires 0 <= x /\ x < pow2 16)
    (ensures fits x)
    [SMTPat (fits x)]

(*| The natural number denoted by a size; the result always satisfies
    `FStar.SizeT.fits`.

    `v` is a specification function: it is marked `noextract_to "krml"`, so
    code extracted to C must not use it. *)
[@@noextract_to "krml"]
val v (x: t) : Pure nat
  (requires True)
  (ensures (fun y -> fits y))

/// We therefore offer two functions to create a t value.
/// Any value that fits in a uint_16 can be cast directly to t
/// Any value that might not fit in a uint_16 needs to satisfy the `fits_u32`
/// or `fits_u64` predicates. These predicates can only be introduced through a
/// stateful function (currently in Steel.ST.HigherArray), which will be extracted
/// to a static_assert by krml
(*| Converts an integer that fits into a size, with `v (uint_to_t x) == x`.

    Requires `FStar.SizeT.fits x`. For concrete values below `pow2 16` this is
    discharged automatically; otherwise use `FStar.SizeT.fits_u32`,
    `FStar.SizeT.fits_u64` or a bound already known for another size. See
    also the casts `FStar.SizeT.uint16_to_sizet`,
    `FStar.SizeT.uint32_to_sizet` and `FStar.SizeT.uint64_to_sizet`. *)
val uint_to_t (x: int) : Pure t
  (requires (fits x))
  (ensures (fun y -> v y == x))

/// v and uint_to_t are inverses
(*| Converting the value of a size back gives the same size:
    `uint_to_t (v x) == x`.

    Triggered automatically on `FStar.SizeT.v x`. *)
val size_v_inj (x: t)
  : Lemma
    (ensures uint_to_t (v x) == x)
    [SMTPat (v x)]

(*| The value of `uint_to_t x` is `x`, for any `x` that fits.

    Triggered automatically on `FStar.SizeT.uint_to_t x`. *)
val size_uint_to_t_inj (x: int)
  : Lemma
    (requires fits x)
    (ensures v (uint_to_t x) == x)
    [SMTPat (uint_to_t x)]

(*| Assumption that sizes are at least 32 bits wide on the target platform.

    `fits_u32` is an abstract proposition that the interface gives no way to
    prove: it is meant to be introduced by a platform check that KaRaMeL
    extracts to a static assertion. Under it, every natural below `pow2 32`
    fits (`FStar.SizeT.fits_u32_implies_fits`) and 32-bit values can be cast
    with `FStar.SizeT.uint32_to_sizet`. *)
val fits_u32 : prop
(*| Assumption that sizes are 64 bits wide on the target platform.

    Like `FStar.SizeT.fits_u32`, it is abstract and cannot be proved from this
    interface. It implies `FStar.SizeT.fits_u32`
    (`FStar.SizeT.fits_u64_implies_fits_32`) and that every natural below
    `pow2 64` fits (`FStar.SizeT.fits_u64_implies_fits`). *)
val fits_u64 : prop

(*| A platform with 64-bit sizes also has sizes of at least 32 bits:
    `FStar.SizeT.fits_u64` implies `FStar.SizeT.fits_u32`.

    Not an SMT pattern; call it explicitly. *)
val fits_u64_implies_fits_32 (_:unit)
  : Lemma
    (requires fits_u64)
    (ensures fits_u32)

(*| Under `FStar.SizeT.fits_u32`, every natural below `pow2 32` fits in a
    size.

    Not an SMT pattern; call it explicitly. *)
val fits_u32_implies_fits (x:int)
  : Lemma
    (requires fits_u32 /\ 0 <= x /\ x < pow2 32)
    (ensures fits x)

(*| Under `FStar.SizeT.fits_u64`, every natural below `pow2 64` fits in a
    size.

    Not an SMT pattern; call it explicitly. *)
val fits_u64_implies_fits (x:int)
  : Lemma
    (requires fits_u64 /\ 0 <= x /\ x < pow2 64)
    (ensures fits x)

/// Creates a size_t when given a uint32 literal. Note, this will not
/// extract if [x] is not a literal (e.g., 12ul). If you want to do a
/// cast, see `uint32_to_sizet` below
(*| Builds a size from a 32-bit unsigned literal, preserving its value.

    Requires `FStar.SizeT.fits_u32` or that the value fits. It is
    `noextract` and `inline_for_extraction`: it only extracts when applied to
    a literal such as `12ul`. To convert a computed value, use
    `FStar.SizeT.uint32_to_sizet`. *)
noextract inline_for_extraction
val of_u32 (x: U32.t) : Pure t
  (requires fits_u32 \/ fits (U32.v x))
  (ensures (fun y -> v y == U32.v x))

/// Creates a size_t when given a uint64 literal. Note, this will not
/// extract if [x] is not a literal (e.g., 12uL). If you want to do a
/// cast, see `uint64_to_sizet` below
(*| Builds a size from a 64-bit unsigned literal, preserving its value.

    Requires `FStar.SizeT.fits_u64` or that the value fits. It is
    `noextract` and `inline_for_extraction`: it only extracts when applied to
    a literal such as `12uL`. To convert a computed value, use
    `FStar.SizeT.uint64_to_sizet`. *)
noextract inline_for_extraction
val of_u64 (x: U64.t) : Pure t
  (requires fits_u64 \/ fits (U64.v x))
  (ensures (fun y -> v y == U64.v x))

(*| Casts a 16-bit unsigned integer to a size, preserving its value.

    Always defined, since sizes are at least 16 bits wide. *)
val uint16_to_sizet (x:U16.t) : Pure t
  (requires True)
  (ensures fun y -> v y == U16.v x)

(*| Casts a 32-bit unsigned integer to a size, preserving its value.

    Requires `FStar.SizeT.fits_u32` or that the particular value fits.

    ```fstar
    let widen_u32 (x: FStar.UInt32.t)
      : Pure FStar.SizeT.t
        (requires FStar.SizeT.fits_u32)
        (ensures fun y -> FStar.SizeT.v y == FStar.UInt32.v x)
      = FStar.SizeT.uint32_to_sizet x
    ``` *)
val uint32_to_sizet (x:U32.t) : Pure t
  (requires fits_u32 \/ fits (U32.v x))
  (ensures fun y -> v y == U32.v x)

(*| Casts a 64-bit unsigned integer to a size, preserving its value.

    Requires `FStar.SizeT.fits_u64` or that the particular value fits. *)
val uint64_to_sizet (x:U64.t) : Pure t
  (requires fits_u64 \/ fits (U64.v x))
  (ensures fun y -> v y == U64.v x)

(*| Casts a size to a 32-bit unsigned integer, truncating: the result is
    `v x % pow2 32`.

    Total; no precondition. The value is preserved when `v x < pow2 32`. *)
val sizet_to_uint32 (x:t) : Pure U32.t
  (requires True)
  (ensures fun y -> U32.v y == v x % pow2 32)

(*| Casts a size to a 64-bit unsigned integer, truncating: the result is
    `v x % pow2 64`.

    Total; no precondition. The value is preserved when `v x < pow2 64`;
    the interface does not state that every size is below `pow2 64`. *)
val sizet_to_uint64 (x:t) : Pure U64.t
  (requires True)
  (ensures fun y -> U64.v y == v x % pow2 64)

(*| Fitting is downward closed: if `y` fits and `x <= y`, then `x` fits.

    Triggered automatically when both `FStar.SizeT.fits x` and
    `FStar.SizeT.fits y` appear. *)
val fits_lte (x y: nat) : Lemma
  (requires (x <= y /\ fits y))
  (ensures (fits x))
  [SMTPat (fits x); SMTPat (fits y)]

(* Non-overflowing arithmetic operations *)

(*| Sum of two sizes: `v (add x y) == v x + v y`.

    Requires the sum to fit (`FStar.SizeT.fits (v x + v y)`); there is no
    wrapping variant. Infix: `FStar.SizeT.op_Plus`.

    ```fstar
    let sum_sizes (x y: FStar.SizeT.t)
      : Pure FStar.SizeT.t
        (requires FStar.SizeT.fits (FStar.SizeT.v x + FStar.SizeT.v y))
        (ensures fun z -> FStar.SizeT.v z == FStar.SizeT.v x + FStar.SizeT.v y)
      = FStar.SizeT.add x y
    ``` *)
val add (x y: t) : Pure t
  (requires (fits (v x + v y)))
  (ensures (fun z -> v z == v x + v y))

(*| Difference of two sizes: `v (sub x y) == v x - v y`.

    Requires `v x >= v y`; there is no wrapping variant. Infix:
    `FStar.SizeT.op_Minus`.

    ```fstar
    let pred_size (x: FStar.SizeT.t{FStar.SizeT.v x > 0}) : FStar.SizeT.t =
      FStar.SizeT.(x - 1sz)
    ``` *)
val sub (x y: t) : Pure t
  (requires (v x >= v y))
  (ensures (fun z -> v z == v x - v y))

(*| Product of two sizes: `v (mul x y) == v x * v y`.

    Requires the product to fit (`FStar.SizeT.fits (v x * v y)`); there is
    no wrapping variant. Infix: `FStar.SizeT.op_Star`. *)
val mul (x y: t) : Pure t
  (requires (fits (v x * v y)))
  (ensures (fun z -> v z == v x * v y))

(*| Quotient of two sizes, rounding down: `v (div a b) == v a / v b`.

    Requires a non-zero divisor (`v b <> 0`). Infix: `FStar.SizeT.op_Slash`. *)
val div (a:t) (b:t{v b <> 0}) : Pure t
  (requires (True))
  (ensures (fun c -> v a / v b = v c))

(*| Specification of the remainder of `a` by a non-zero `b`, as
    `a - (a / b) * b`.

    For the naturals that fit in a size this is `a % b`, and the result is
    known to fit. Ghost (`GTot`); used to specify `FStar.SizeT.rem`, in the
    style of `FStar.UInt.mod`. *)
let mod_spec (a:int{fits a}) (b:int{fits b /\ b <> 0}) : GTot (n:nat{fits n}) =
  let res = a - ((a/b) * b) in
  fits_lte res a;
  res

(*| Remainder of the division of `a` by a non-zero `b`:
    `v (rem a b) == mod_spec (v a) (v b)`, that is `v a % v b`.

    Requires `v b <> 0`. Infix: `FStar.SizeT.op_Percent`. *)
val rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires True)
  (ensures (fun c -> mod_spec (v a) (v b) = v c))

(*| Equality test on sizes, returning `v x = v y`. Infix:
    `FStar.SizeT.op_Equals_Hat`. *)
val eq (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x = v y)))

(*| Disequality test on sizes, returning `v x <> v y`. Infix:
    `FStar.SizeT.op_Less_Greater_Hat`. *)
val ne (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x <> v y)))

(*| Strict greater-than test on sizes, returning `v x > v y`. Infix:
    `FStar.SizeT.op_Greater`. *)
val gt (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x > v y)))

(*| Greater-than-or-equal test on sizes, returning `v x >= v y`. Infix:
    `FStar.SizeT.op_Greater_Equals`. *)
val gte (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x >= v y)))

(*| Strict less-than test on sizes, returning `v x < v y`. Infix:
    `FStar.SizeT.op_Less`. *)
val lt (x y:t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x < v y)))

(*| Less-than-or-equal test on sizes, returning `v x <= v y`. Infix:
    `FStar.SizeT.op_Less_Equals`. *)
val lte (x y: t) : Pure bool
  (requires True)
  (ensures (fun z -> z == (v x <= v y)))

(* Infix notations *)

(*| Infix notation for `FStar.SizeT.add`; requires the sum to fit. *)
inline_for_extraction unfold let ( + )  = add
(*| Infix notation for `FStar.SizeT.sub`; requires `v x >= v y`. *)
inline_for_extraction unfold let ( - )  = sub
(*| Infix notation for `FStar.SizeT.mul`; requires the product to fit. *)
inline_for_extraction unfold let ( * )  = mul
(*| Infix notation for `FStar.SizeT.div`; requires a non-zero divisor. *)
inline_for_extraction unfold let ( / )  = div
(*| Infix notation for `FStar.SizeT.rem`; requires a non-zero divisor. *)
inline_for_extraction unfold let ( % )  = rem
(*| Infix notation for `FStar.SizeT.eq`. *)
inline_for_extraction unfold let ( =^ )  = eq
(*| Infix notation for `FStar.SizeT.ne`. *)
inline_for_extraction unfold let ( <>^ ) = ne
(*| Infix notation for `FStar.SizeT.gt`. *)
inline_for_extraction unfold let ( > )  = gt
(*| Infix notation for `FStar.SizeT.gte`. *)
inline_for_extraction unfold let ( >= ) = gte
(*| Infix notation for `FStar.SizeT.lt`. *)
inline_for_extraction unfold let ( < )  = lt
(*| Infix notation for `FStar.SizeT.lte`. *)
inline_for_extraction unfold let ( <= ) = lte

(* Deprecated infix notations: the spellings the nine operators above had
   before type-based overloading made the [^] suffix unnecessary. *)
(*| Deprecated spelling of `FStar.SizeT.op_Plus` (`FStar.SizeT.add`). *)
[@@deprecated "use ( + )"]  inline_for_extraction unfold let ( +^ )  = add
(*| Deprecated spelling of `FStar.SizeT.op_Minus` (`FStar.SizeT.sub`). *)
[@@deprecated "use ( - )"]  inline_for_extraction unfold let ( -^ )  = sub
(*| Deprecated spelling of `FStar.SizeT.op_Star` (`FStar.SizeT.mul`). *)
[@@deprecated "use ( * )"]  inline_for_extraction unfold let ( *^ )  = mul
(*| Deprecated spelling of `FStar.SizeT.op_Slash` (`FStar.SizeT.div`). *)
[@@deprecated "use ( / )"]  inline_for_extraction unfold let ( /^ )  = div
(*| Deprecated spelling of `FStar.SizeT.op_Percent` (`FStar.SizeT.rem`). *)
[@@deprecated "use ( % )"]  inline_for_extraction unfold let ( %^ )  = rem
(*| Deprecated spelling of `FStar.SizeT.op_Greater` (`FStar.SizeT.gt`). *)
[@@deprecated "use ( > )"]  inline_for_extraction unfold let ( >^ )  = gt
(*| Deprecated spelling of `FStar.SizeT.op_Greater_Equals`
    (`FStar.SizeT.gte`). *)
[@@deprecated "use ( >= )"] inline_for_extraction unfold let ( >=^ ) = gte
(*| Deprecated spelling of `FStar.SizeT.op_Less` (`FStar.SizeT.lt`). *)
[@@deprecated "use ( < )"]  inline_for_extraction unfold let ( <^ )  = lt
(*| Deprecated spelling of `FStar.SizeT.op_Less_Equals` (`FStar.SizeT.lte`). *)
[@@deprecated "use ( <= )"] inline_for_extraction unfold let ( <=^ ) = lte

//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __uint_to_t (x:int) : Tot t
    = assume (x >= 0 /\ fits x); uint_to_t x
