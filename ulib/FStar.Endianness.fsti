module FStar.Endianness

/// A library of lemmas for reasoning about sequences of machine integers and
/// their (little|big)-endian representation as a sequence of bytes.
///
/// The functions in this module aim to be as generic as possible, in order to
/// facilitate compatibility with:
/// - Vale's model of machine integers (nat64 et al.), which does not rely on
///   FStar's machine integers
/// - HACL*'s Lib.IntTypes module, which exposes a universal indexed integer
///   type but uses F* machine integers under the hood.
///
/// To achieve maximum compatibility, we try to state most lemmas using nat
/// rather than UIntX.
///
/// To limit context pollution, the definitions of the recursive functions are
/// abstract; please add lemmas as you see fit. In extreme cases, ``friend``'ing
/// might be de rigueur.
///
/// .. note::
///
///    This module supersedes the poorly-named ``FStar.Krml.Endianness``.

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S = FStar.Seq

(*| Byte sequences: `FStar.Seq.Base.seq FStar.UInt8.t`, the type on which this module's encodings are specified.

    Marked `noextract_to "krml"`: it is a specification type, not extracted by KaRaMeL. *)
[@@ noextract_to "krml"]
type bytes = S.seq U8.t



/// Definition of little and big-endianness
/// ---------------------------------------
///
/// This is our spec, to be audited. From bytes to nat.

(*| Interprets a byte sequence as a little-endian natural number: the first byte is the least significant.

    The empty sequence denotes 0. The definition is abstract; unfold one step with `FStar.Endianness.reveal_le_to_n`, and bound the result with `FStar.Endianness.lemma_le_to_n_is_bounded`.

    ```fstar
    let _ = assert (FStar.Endianness.le_to_n (FStar.Endianness.n_to_le 2 258) == 258)
    ``` *)
val le_to_n : b:bytes -> Tot nat

(*| Interprets a byte sequence as a big-endian natural number: the last byte is the least significant.

    The empty sequence denotes 0. The definition is abstract; unfold one step with `FStar.Endianness.reveal_be_to_n`, and bound the result with `FStar.Endianness.lemma_be_to_n_is_bounded`. *)
val be_to_n : b:bytes -> Tot nat

/// Induction for le_to_n and be_to_n

(*| Unfolds `le_to_n` one step: 0 on the empty sequence, otherwise the first byte plus `pow2 8` times `le_to_n` of the tail.

    Use it for proofs by induction on the sequence. *)
val reveal_le_to_n (b:bytes)
  : Lemma
    (le_to_n b ==
     (match Seq.length b with
      | 0 -> 0
      | _ -> U8.v (S.head b) + pow2 8 * le_to_n (S.tail b)))

(*| Unfolds `be_to_n` one step: 0 on the empty sequence, otherwise the last byte plus `pow2 8` times `be_to_n` of the sequence without its last byte.

    Use it for proofs by induction on the sequence. *)
val reveal_be_to_n (b:bytes)
  : Lemma
    (be_to_n b ==
     (match Seq.length b with
      | 0 -> 0
      | _ -> U8.v (S.last b) + pow2 8 * be_to_n (S.slice b 0 (S.length b - 1))))

(*| `le_to_n b < pow2 (8 * length b)`: a little-endian number fits in as many bytes as it has. *)
val lemma_le_to_n_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (le_to_n b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))

(*| `be_to_n b < pow2 (8 * length b)`: a big-endian number fits in as many bytes as it has. *)
val lemma_be_to_n_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (be_to_n b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))


/// Inverse operations
/// ------------------
///
/// From nat to bytes, and their functional correctness.

(*| Encodes `n < pow2 (8 * len)` as a little-endian byte sequence of exactly `len` bytes.

    The refinement states the length and that `le_to_n` of the result is `n`. Leading high-order bytes are zero when `n` needs fewer bytes. *)
val n_to_le : len:nat -> n:nat{n < pow2 (8 * len)} ->
  Tot (b:bytes{S.length b == len /\ n == le_to_n b})
  (decreases len)

(*| Encodes `n < pow2 (8 * len)` as a big-endian byte sequence of exactly `len` bytes.

    The refinement states the length and that `be_to_n` of the result is `n`. Leading high-order bytes are zero when `n` needs fewer bytes. *)
val n_to_be:
  len:nat -> n:nat{n < pow2 (8 * len)} ->
  Tot (b:bytes{S.length b == len /\ n == be_to_n b})
  (decreases len)

/// Injectivity
/// -----------

(*| `n_to_le len` is injective: equal encodings come from equal numbers. *)
val n_to_le_inj (len: nat) (n1 n2: (n:nat{n < pow2 (8 * len)})):
  Lemma (requires (n_to_le len n1 == n_to_le len n2))
        (ensures (n1 == n2))

(*| `n_to_be len` is injective: equal encodings come from equal numbers. *)
val n_to_be_inj (len: nat) (n1 n2: (n:nat{n < pow2 (8 * len)})) :
  Lemma (requires (n_to_be len n1 == n_to_be len n2))
        (ensures (n1 == n2))

(*| Byte sequences of the same length with the same big-endian value are equal (as `FStar.Seq.Base.equal`). *)
val be_to_n_inj
  (b1 b2: Seq.seq U8.t)
: Lemma
  (requires (Seq.length b1 == Seq.length b2 /\ be_to_n b1 == be_to_n b2))
  (ensures (Seq.equal b1 b2))
  (decreases (Seq.length b1))

(*| Byte sequences of the same length with the same little-endian value are equal (as `FStar.Seq.Base.equal`). *)
val le_to_n_inj
  (b1 b2: Seq.seq U8.t)
: Lemma
  (requires (Seq.length b1 == Seq.length b2 /\ le_to_n b1 == le_to_n b2))
  (ensures (Seq.equal b1 b2))
  (decreases (Seq.length b1))

/// Roundtripping
/// -------------

(*| Re-encoding a decoded sequence gives it back: `n_to_be len (be_to_n s) == s` when `length s == len`; also states the bound needed by `n_to_be`.

    Triggered automatically on `n_to_be len (be_to_n s)`. *)
val n_to_be_be_to_n (len: nat) (s: Seq.seq U8.t) : Lemma
  (requires (Seq.length s == len))
  (ensures (
    be_to_n s < pow2 (8 * len) /\
    n_to_be len (be_to_n s) == s
  ))
  [SMTPat (n_to_be len (be_to_n s))]

(*| Re-encoding a decoded sequence gives it back: `n_to_le len (le_to_n s) == s` when `length s == len`; also states the bound needed by `n_to_le`.

    Triggered automatically on `n_to_le len (le_to_n s)`. *)
val n_to_le_le_to_n (len: nat) (s: Seq.seq U8.t) : Lemma
  (requires (Seq.length s == len))
  (ensures (
    le_to_n s < pow2 (8 * len) /\
    n_to_le len (le_to_n s) == s
  ))
  [SMTPat (n_to_le len (le_to_n s))]


/// Specializations for F* machine integers
/// ---------------------------------------
///
/// These are useful because they take care of calling the right ``*_is_bounded`` lemmas.

(*| Reads 4 bytes as a little-endian `FStar.UInt32.t`, whose value is `le_to_n b`. *)
let uint32_of_le (b: bytes { S.length b = 4 }) =
  let n = le_to_n b in
  lemma_le_to_n_is_bounded b;
  UInt32.uint_to_t n

(*| Writes a `FStar.UInt32.t` as 4 little-endian bytes: `n_to_le 4 (v x)`. *)
let le_of_uint32 (x: UInt32.t): b:bytes{ S.length b = 4 } =
  n_to_le 4 (UInt32.v x)

(*| Reads 4 bytes as a big-endian `FStar.UInt32.t`, whose value is `be_to_n b`. *)
let uint32_of_be (b: bytes { S.length b = 4 }) =
  let n = be_to_n b in
  lemma_be_to_n_is_bounded b;
  UInt32.uint_to_t n

(*| Writes a `FStar.UInt32.t` as 4 big-endian bytes: `n_to_be 4 (v x)`. *)
let be_of_uint32 (x: UInt32.t): b:bytes{ S.length b = 4 } =
  n_to_be 4 (UInt32.v x)

(*| Reads 8 bytes as a little-endian `FStar.UInt64.t`, whose value is `le_to_n b`. *)
let uint64_of_le (b: bytes { S.length b = 8 }) =
  let n = le_to_n b in
  lemma_le_to_n_is_bounded b;
  UInt64.uint_to_t n

(*| Writes a `FStar.UInt64.t` as 8 little-endian bytes: `n_to_le 8 (v x)`. *)
let le_of_uint64 (x: UInt64.t): b:bytes{ S.length b = 8 } =
  n_to_le 8 (UInt64.v x)

(*| Reads 8 bytes as a big-endian `FStar.UInt64.t`, whose value is `be_to_n b`. *)
let uint64_of_be (b: bytes { S.length b = 8 }) =
  let n = be_to_n b in
  lemma_be_to_n_is_bounded b;
  UInt64.uint_to_t n

(*| Writes a `FStar.UInt64.t` as 8 big-endian bytes: `n_to_be 8 (v x)`. *)
let be_of_uint64 (x: UInt64.t): b:bytes{ S.length b = 8 } =
  n_to_be 8 (UInt64.v x)


/// Lifting {le,be}_to_n / n_to_{le,be} to sequences
/// ------------------------------------------------
///
/// TODO: 16-bit (but is it really needed?)
/// TODO: should these be specializations of generic functions that chop on
///       N-byte boundaries, and operate on bounded nats instead of uints?

(*| Reads `4 * l` bytes as a sequence of `l` little-endian 32-bit words.

    Word `i` is `uint32_of_le` of bytes `4 * i` to `4 * i + 4`; see `FStar.Endianness.offset_uint32_le`. *)
val seq_uint32_of_le (l: nat) (b: bytes{ S.length b = 4 * l }):
  s:S.seq UInt32.t { S.length s = l }

(*| Writes a sequence of 32-bit words as the concatenation of their 4-byte little-endian encodings.

    The interface states the length; see `FStar.Endianness.le_of_seq_uint32_base` and `FStar.Endianness.le_of_seq_uint32_append` for the content. *)
val le_of_seq_uint32 (s: S.seq UInt32.t):
  Tot (b:bytes { S.length b = 4 * S.length s })
    (decreases (S.length s))

(*| Reads `4 * l` bytes as a sequence of `l` big-endian 32-bit words.

    Word `i` is `uint32_of_be` of bytes `4 * i` to `4 * i + 4`; see `FStar.Endianness.offset_uint32_be`. *)
val seq_uint32_of_be (l: nat) (b: bytes{ S.length b = 4 * l }):
  s:S.seq UInt32.t { S.length s = l }

(*| Writes a sequence of 32-bit words as the concatenation of their 4-byte big-endian encodings.

    The interface states the length; see `FStar.Endianness.be_of_seq_uint32_base`, `FStar.Endianness.be_of_seq_uint32_append` and the round-trip lemmas for the content. *)
val be_of_seq_uint32 (s: S.seq UInt32.t):
  Tot (b:bytes { S.length b = 4 * S.length s })
    (decreases (S.length s))

(*| Reads `8 * l` bytes as a sequence of `l` little-endian 64-bit words.

    Word `i` is `uint64_of_le` of bytes `8 * i` to `8 * i + 8`; see `FStar.Endianness.offset_uint64_le`. *)
val seq_uint64_of_le (l: nat) (b: bytes{ S.length b = 8 * l }):
  s:S.seq UInt64.t { S.length s = l }

(*| Writes a sequence of 64-bit words as the concatenation of their 8-byte little-endian encodings.

    The interface states only the length; this module has no lemma about its content. *)
val le_of_seq_uint64 (s: S.seq UInt64.t):
  Tot (b:bytes { S.length b = 8 * S.length s })
    (decreases (S.length s))

(*| Reads `8 * l` bytes as a sequence of `l` big-endian 64-bit words.

    Word `i` is `uint64_of_be` of bytes `8 * i` to `8 * i + 8`; see `FStar.Endianness.offset_uint64_be`. *)
val seq_uint64_of_be (l: nat) (b: bytes{ S.length b = 8 * l }):
  s:S.seq UInt64.t { S.length s = l }

(*| Writes a sequence of 64-bit words as the concatenation of their 8-byte big-endian encodings.

    The interface states the length; see `FStar.Endianness.be_of_seq_uint64_base` and `FStar.Endianness.be_of_seq_uint64_append` for the content. *)
val be_of_seq_uint64 (s: S.seq UInt64.t):
  Tot (b:bytes { S.length b = 8 * S.length s })
    (decreases (S.length s))


/// Complete specification of the combinators above, relating them to {le,be}_to_ / n_to_{le,be}
/// --------------------------------------------------------------------------------------------

(*| Word `i` of `seq_uint32_of_be n b` is `uint32_of_be` of the 4 bytes of `b` at offset `4 * i`; requires `length b = 4 * n` and `i < n`.

    Triggered automatically on `index (seq_uint32_of_be n b) i`. *)
val offset_uint32_be (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 4 * n /\
      i < n))
    (ensures (
      S.index (seq_uint32_of_be n b) i == uint32_of_be (S.slice b (4 * i) (4 * i + 4))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint32_of_be n b) i) ]

(*| Word `i` of `seq_uint32_of_le n b` is `uint32_of_le` of the 4 bytes of `b` at offset `4 * i`; requires `length b = 4 * n` and `i < n`.

    Triggered automatically on `index (seq_uint32_of_le n b) i`. *)
val offset_uint32_le (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 4 * n /\
      i < n))
    (ensures (
      S.index (seq_uint32_of_le n b) i == uint32_of_le (S.slice b (4 * i) (4 * i + 4))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint32_of_le n b) i) ]

(*| Word `i` of `seq_uint64_of_be n b` is `uint64_of_be` of the 8 bytes of `b` at offset `8 * i`; requires `length b = 8 * n` and `i < n`.

    Triggered automatically on `index (seq_uint64_of_be n b) i`. *)
val offset_uint64_be (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 8 * n /\
      i < n))
    (ensures (
      S.index (seq_uint64_of_be n b) i == uint64_of_be (S.slice b (8 * i) (8 * i + 8))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint64_of_be n b) i) ]

(*| Word `i` of `seq_uint64_of_le n b` is `uint64_of_le` of the 8 bytes of `b` at offset `8 * i`; requires `length b = 8 * n` and `i < n`.

    Triggered automatically on `index (seq_uint64_of_le n b) i`. *)
val offset_uint64_le (b: bytes) (n: nat) (i: nat):
  Lemma
    (requires (
      S.length b = 8 * n /\
      i < n))
    (ensures (
      S.index (seq_uint64_of_le n b) i == uint64_of_le (S.slice b (8 * i) (8 * i + 8))))
    (decreases (
      S.length b))
    [ SMTPat (S.index (seq_uint64_of_le n b) i) ]


/// Reasoning about appending such sequences
/// ----------------------------------------
///
/// TODO: this is fairly incomplete
/// TODO: the *_base cases seem ad-hoc and derivable trivially from offset above; why have them?

(*| A 4-byte sequence whose big-endian value is the only word of a one-element sequence `s1` is `be_of_seq_uint32 s1`.

    Triggered automatically when both `be_to_n s2` and `v (index s1 0)` appear. *)
val be_of_seq_uint32_base (s1: S.seq U32.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 4 /\
    be_to_n s2 = U32.v (S.index s1 0)))
  (ensures (S.equal s2 (be_of_seq_uint32 s1)))
  [ SMTPat (be_to_n s2); SMTPat (U32.v (S.index s1 0)) ]

(*| A 4-byte sequence whose little-endian value is the only word of a one-element sequence `s1` is `le_of_seq_uint32 s1`.

    Triggered automatically when both `le_to_n s2` and `v (index s1 0)` appear. *)
val le_of_seq_uint32_base (s1: S.seq U32.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 4 /\
    le_to_n s2 = U32.v (S.index s1 0)))
  (ensures (S.equal s2 (le_of_seq_uint32 s1)))
  [ SMTPat (le_to_n s2); SMTPat (U32.v (S.index s1 0)) ]

(*| An 8-byte sequence whose big-endian value is the only word of a one-element sequence `s1` is `be_of_seq_uint64 s1`.

    Triggered automatically when both `be_to_n s2` and `v (index s1 0)` appear. *)
val be_of_seq_uint64_base (s1: S.seq U64.t) (s2: S.seq U8.t): Lemma
  (requires (
    S.length s1 = 1 /\
    S.length s2 = 8 /\
    be_to_n s2 = U64.v (S.index s1 0)))
  (ensures (S.equal s2 (be_of_seq_uint64 s1)))
  [ SMTPat (be_to_n s2); SMTPat (U64.v (S.index s1 0)) ]

(*| `be_of_seq_uint32` distributes over `FStar.Seq.Base.append` (as `FStar.Seq.Base.equal`).

    Triggered automatically on `append (be_of_seq_uint32 s1) (be_of_seq_uint32 s2)`. *)
val be_of_seq_uint32_append (s1 s2: S.seq U32.t): Lemma
  (ensures (
    S.equal (be_of_seq_uint32 (S.append s1 s2))
      (S.append (be_of_seq_uint32 s1) (be_of_seq_uint32 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (be_of_seq_uint32 s1) (be_of_seq_uint32 s2)) ]

(*| `le_of_seq_uint32` distributes over `FStar.Seq.Base.append` (as `FStar.Seq.Base.equal`).

    Triggered automatically on `append (le_of_seq_uint32 s1) (le_of_seq_uint32 s2)`. *)
val le_of_seq_uint32_append (s1 s2: S.seq U32.t): Lemma
  (ensures (
    S.equal (le_of_seq_uint32 (S.append s1 s2))
      (S.append (le_of_seq_uint32 s1) (le_of_seq_uint32 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (le_of_seq_uint32 s1) (le_of_seq_uint32 s2)) ]

(*| `be_of_seq_uint64` distributes over `FStar.Seq.Base.append` (as `FStar.Seq.Base.equal`).

    Triggered automatically on `append (be_of_seq_uint64 s1) (be_of_seq_uint64 s2)`. *)
val be_of_seq_uint64_append (s1 s2: S.seq U64.t): Lemma
  (ensures (
    S.equal (be_of_seq_uint64 (S.append s1 s2))
      (S.append (be_of_seq_uint64 s1) (be_of_seq_uint64 s2))))
  (decreases (
    S.length s1))
  [ SMTPat (S.append (be_of_seq_uint64 s1) (be_of_seq_uint64 s2)) ]

/// Roundtripping
/// -------------
///
/// TODO: also incomplete

(*| Decoding the big-endian encoding of `n` words gives the words back (as `FStar.Seq.Base.equal`).

    Triggered automatically on `seq_uint32_of_be n (be_of_seq_uint32 s)`. *)
val seq_uint32_of_be_be_of_seq_uint32 (n: nat) (s: S.seq U32.t) : Lemma
  (requires (n == S.length s))
  (ensures (seq_uint32_of_be n (be_of_seq_uint32 s) `S.equal` s))
  (decreases n)
  [SMTPat (seq_uint32_of_be n (be_of_seq_uint32 s))]

(*| Re-encoding `4 * n` bytes decoded as `n` big-endian words gives the bytes back (as `FStar.Seq.Base.equal`).

    Triggered automatically on `be_of_seq_uint32 (seq_uint32_of_be n s)`. *)
val be_of_seq_uint32_seq_uint32_of_be (n: nat) (s: S.seq U8.t) : Lemma
  (requires (4 * n == S.length s))
  (ensures (be_of_seq_uint32 (seq_uint32_of_be n s) `S.equal` s))
  (decreases n)
  [SMTPat (be_of_seq_uint32 (seq_uint32_of_be n s))]

/// Reasoning about slicing such sequences
/// --------------------------------------
///
/// (Needs SMTPats above for roundtripping in their proof, hence why they're at the end.)

(*| Slicing words `lo` to `hi` of `seq_uint32_of_be n s` is decoding bytes `4 * lo` to `4 * hi` of `s` (as `FStar.Seq.Base.equal`); requires `lo <= hi <= n`. *)
val slice_seq_uint32_of_be (n: nat) (s: S.seq U8.t) (lo: nat) (hi: nat) : Lemma
  (requires (4 * n == S.length s /\ lo <= hi /\ hi <= n))
  (ensures (S.slice (seq_uint32_of_be n s) lo hi) `S.equal` seq_uint32_of_be (hi - lo) (S.slice s (4 * lo) (4 * hi)))

(*| Encoding words `lo` to `hi` of `s` big-endian gives bytes `4 * lo` to `4 * hi` of the encoding of `s` (as `FStar.Seq.Base.equal`); requires `lo <= hi <= length s`. *)
val be_of_seq_uint32_slice (s: S.seq U32.t) (lo: nat) (hi: nat) : Lemma
  (requires (lo <= hi /\ hi <= S.length s))
  (ensures (be_of_seq_uint32 (S.slice s lo hi) `S.equal` S.slice (be_of_seq_uint32 s) (4 * lo) (4 * hi)))


/// Some reasoning about zero bytes

(*| A byte sequence of zeros has little-endian value 0. *)
let rec le_to_n_zeros (s:bytes)
  : Lemma
    (requires
      forall (i:nat). i < Seq.length s ==> Seq.index s i == 0uy)
    (ensures le_to_n s == 0)
    (decreases (Seq.length s))
  = reveal_le_to_n s;
    if Seq.length s = 0 then ()
    else le_to_n_zeros (Seq.tail s)

(*| A byte sequence of zeros has big-endian value 0. *)
let rec be_to_n_zeros (s:bytes)
  : Lemma
    (requires
      forall (i:nat). i < Seq.length s ==> Seq.index s i == 0uy)
    (ensures be_to_n s == 0)
    (decreases (Seq.length s))
  = reveal_be_to_n s;
    if Seq.length s = 0 then ()
    else be_to_n_zeros (Seq.slice s 0 (Seq.length s - 1))
