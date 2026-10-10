(*
      Copyright 2008-2017 Microsoft Research

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

(*

   A library for vectors, i.e., immutable arrays, whose length is
   representable by a machine integer, FStar.UInt32.t.

   This is closely related to FStar.Seq, with the following main
   differences:

   The type `raw a l`: A raw vector

     1. Raw vectors receive special treatment during extraction,
        especially by KaRaMeL, which extracts a vector to a raw C
        pointer. When extracting to OCaml, a `raw a l` is a
        `Batteries.Vect t a`

     2. The length of a vector is representable in a U32.t

     3. The interface is designed around a length-indexed type: this
        enables the compilation to raw pointers, since this ensures
        that all functions that manipulate vectors always have a U32
        variable describing that vector's length in scope.

        A length-indexed interface is also suitable for clients for whom
        proving properties about the length is a primary concern: the
        signatures in this interface carry intrinsic proofs about length
        properties, simplifying proof obligations in client code.

     4. Raw vectors lack decidable equality (since that cannot be
        implemented given the representation choice in KaRaMeL)

   The type `t a`: A dynamically sized vector

     1. Conceptually, a `t a` is a pair of a `len:U32.t` and a `raw a
        len`. They are implemented as such by KaRaMeL. When extracting
        to OCaml, `t a` is identical to `raw a _`, i.e., it is still
        extracted to a `Batteries.Vect.t a`

     2. Unlike raw vectors, `t a` supports decidable equality when it
        is supported by `a`. This is the main reason `t a` is provided
        at an abstract type, rather than being exposed as a pair of a
        U32 and a raw vector, since the latter does not support
        decidable equality.

   @summary Immutable vectors whose length is less than  `pow2 32`
*)

module FStar.Vector.Base
module U32 = FStar.UInt32
module S = FStar.Seq

////////////////////////////////////////////////////////////////////////////////
/// The basic model of raw vectors as u32-length sequences
////////////////////////////////////////////////////////////////////////////////

(*| The type of vector lengths and indices, 32-bit unsigned integers
    (`FStar.UInt32.t`). *)
let len_t = U32.t

(*| The abstract type of immutable vectors of `a` with length `l`.

    Logically, a `raw a l` is a sequence of length `U32.v l`: see
    `FStar.Vector.Base.reveal` and `FStar.Vector.Base.hide`. Unlike
    `FStar.Vector.Base.t`, it does not support decidable equality. It is
    designed for extraction by KaRaMeL to a C pointer, which is why every
    operation keeps the length in its type. *)
val raw ([@@@strictly_positive] a:Type u#a)
        (l:len_t)
  : Type u#a

(*| The length of a raw vector as a `nat`, for use in specifications and
    proofs. *)
let raw_length (#a:Type) (#l:len_t) (v:raw a l) : GTot nat = U32.v l

(**
    Abstractly, a `vec a l` is just a sequence whose length is `U32.v l`.
    `reveal` and `hide` build an isomorphism establishing this
**)

(*| The sequence of elements of a raw vector.

    Ghost: only specifications and proofs can use it. With
    `FStar.Vector.Base.hide`, it establishes that `raw a l` is in bijection
    with the sequences of length `U32.v l`. *)
val reveal:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> GTot (s:S.seq a{S.length s = raw_length v})

(*| The raw vector with the elements of a sequence whose length is less than
    `pow2 32`.

    Ghost. The inverse of `FStar.Vector.Base.reveal`. *)
val hide:
    #a:Type
  -> s:S.seq a{S.length s < pow2 32}
  -> GTot (raw a (U32.uint_to_t (S.length s)))

(*| Hiding the sequence of a raw vector gives back the vector.

    Triggered automatically on `reveal v`. *)
val hide_reveal:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> Lemma (ensures (hide (reveal v) == v))
          [SMTPat (reveal v)]

(*| Revealing a hidden sequence gives back the sequence.

    Triggered automatically on `hide s`. *)
val reveal_hide:
    #a:Type
  -> s:S.seq a{S.length s < pow2 32}
  -> Lemma (ensures (reveal (hide s) == s))
          [SMTPat (hide s)]

(*| Extensional equality of raw vectors: their sequences are equal by
    `FStar.Seq.Base.equal`.

    Use `FStar.Vector.Base.extensionality` to turn it into `==`. *)
let equal (#a:Type) (#l:len_t) (v1:raw a l) (v2:raw a l) =
    Seq.equal (reveal v1) (reveal v2)

(*| Extensionally equal raw vectors are equal.

    Requires `FStar.Vector.Base.equal v1 v2` and concludes `v1 == v2`. *)
val extensionality:
    #a:Type
  -> #l:len_t
  -> v1:raw a l
  -> v2:raw a l
  -> Lemma (requires (equal v1 v2))
          (ensures (v1 == v2))

////////////////////////////////////////////////////////////////////////////////
/// end of the basic model
////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
/// A small set of basic operations on raw vectors, corresponding to the operations
/// on sequences. Other operations can be derived from these, as we do for seq.
///    -- init, index, update, append, slice
////////////////////////////////////////////////////////////////////////////////

(*| The type of valid indices of the raw vector `v`: `len_t` values smaller
    than its length. *)
let index_t (#a:Type) (#l:len_t) (v:raw a l) =
    m:len_t{U32.v m < U32.v l}

(*| Builds a raw vector of length `l` whose element at position `i` is
    `contents i`.

    Its sequence is `FStar.Seq.Base.init (U32.v l) contents`, as stated by
    `FStar.Vector.Base.reveal_init`, which is triggered automatically:

    ```fstar
    let squares : FStar.Vector.Base.raw int 4ul =
      FStar.Vector.Base.init 4ul (fun i -> i * i)

    let _ = assert (FStar.Vector.Base.index squares 3ul == 9)
    ``` *)
val init:
    #a:Type
  -> l:len_t
  -> contents: (i:nat { i < U32.v l } -> Tot a)
  -> Tot (raw a l)

(*| Returns the element at position `i` of `v`.

    Specified by `FStar.Vector.Base.reveal_index`. Also written `v.[i]`. *)
val index:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:index_t v
  -> Tot a

(*| Notation: `v.[i]` is `FStar.Vector.Base.index v i`. *)
unfold let ( .[] ) #a #l = index #a #l

(*| Returns a vector that differs from `v` only at position `i`, where it
    holds `x`.

    The vector `v` is unchanged. Specified by
    `FStar.Vector.Base.reveal_update`. Also written `v.[i] <- x`. *)
val update:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:index_t v
  -> x:a
  -> Tot (raw a l)

(*| Notation: `v.[i] <- x` is `FStar.Vector.Base.update v i x`. *)
unfold let ( .[]<- ) #a #l = update #a #l

(*| Concatenates two raw vectors.

    The precondition requires the sum of the lengths to fit in 32 bits.
    Specified by `FStar.Vector.Base.reveal_append`. Also written `v1 @| v2`. *)
val append:
    #a:Type
  -> #l1:len_t
  -> #l2:len_t
  -> v1:raw a l1
  -> v2:raw a l2{UInt.size U32.(v l1 + v l2) U32.n}
  -> Tot (raw a U32.(l1 + l2))

(*| Notation: `v1 @| v2` is `FStar.Vector.Base.append v1 v2`. *)
unfold let (@|) #a #l1 #l2 = append #a #l1 #l2

(*| Returns the sub-vector of `v` from position `i` up to, but not including,
    position `j`.

    Requires `i <= j <= l`; the result has length `j - i`. Specified by
    `FStar.Vector.Base.reveal_sub`. For dynamically sized vectors, see
    `FStar.Vector.Base.slice`. *)
val sub:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:len_t
  -> j:len_t{U32.(v i <= v j /\ v j <= v l)}
  -> Tot (raw a U32.(j - i))

////////////////////////////////////////////////////////////////////////////////
/// Lemmas about the basic operations, all rather boring
///    -- Each is just a lifting specifying the corresponding operation on seq
////////////////////////////////////////////////////////////////////////////////

(*| The sequence of `init l contents` is `FStar.Seq.Base.init (U32.v l) contents`.

    Triggered automatically on `init l contents`. *)
val reveal_init:
    #a:Type
  -> l:len_t
  -> contents: (i:nat { i < U32.v l } -> Tot a)
  -> Lemma
    (ensures (reveal (init l contents) == Seq.init (U32.v l) contents))
    [SMTPat (init l contents)]

(*| Indexing a raw vector is indexing its sequence: `v.[i]` equals
    `FStar.Seq.Base.index (reveal v) (U32.v i)`.

    Triggered automatically on `v.[i]`. *)
val reveal_index:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:index_t v
  -> Lemma
    (ensures (v.[i] == Seq.index (reveal v) (U32.v i)))
    [SMTPat (v.[i])]

(*| The sequence of `v.[i] <- x` is `FStar.Seq.Base.upd (reveal v) (U32.v i) x`.

    Triggered automatically on `v.[i] <- x`. *)
val reveal_update:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:index_t v
  -> x:a
  -> Lemma
    (ensures (reveal (v.[i] <- x) == Seq.upd (reveal v) (U32.v i) x))
    [SMTPat (v.[i] <- x)]

(*| The sequence of `v1 @| v2` is the concatenation of the sequences of `v1`
    and `v2`, by `FStar.Seq.Base.append`.

    Triggered automatically on `v1 @| v2`. *)
val reveal_append:
    #a:Type
  -> #l1:len_t
  -> #l2:len_t
  -> v1:raw a l1
  -> v2:raw a l2{UInt.size U32.(v l1 + v l2) U32.n}
  -> Lemma
    (ensures (reveal (v1 @| v2) == Seq.append (reveal v1) (reveal v2)))
    [SMTPat (v1 @| v2)]

(*| The sequence of `sub v i j` is `FStar.Seq.Base.slice (reveal v) (U32.v i) (U32.v j)`.

    Triggered automatically on `sub v i j`. *)
val reveal_sub:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> i:len_t
  -> j:len_t{U32.(v i <= v j /\ v j <= v l)}
  -> Lemma
    (ensures (reveal (sub v i j) == S.slice (reveal v) (U32.v i) (U32.v j)))
    [SMTPat (sub v i j)]

////////////////////////////////////////////////////////////////////////////////
/// Now, we have `Vector.Base.t`, abstractly, a raw vector paired with its u32 length
////////////////////////////////////////////////////////////////////////////////
(*| The abstract type of dynamically sized immutable vectors of `a`.

    Conceptually a pair of a length `len_t` and a `raw a` vector of that
    length: see `FStar.Vector.Base.len`, `FStar.Vector.Base.as_raw` and
    `FStar.Vector.Base.from_raw`. Unlike `FStar.Vector.Base.raw`, it has
    decidable equality when `a` does (`FStar.Vector.Base.t_has_eq`), which
    is why it is abstract rather than an exposed pair. *)
val t:
    a:Type u#a
  -> Type u#a

(*| A `t a` has decidable equality when `a` has.

    Triggered automatically on `hasEq (t a)`. *)
val t_has_eq:
    a:Type u#a
  -> Lemma
    (requires (hasEq a))
    (ensures  (hasEq (t a)))
    [SMTPat (hasEq (t a))]

(*| The length of a dynamically sized vector, as a `len_t`.

    Computable at run time; `FStar.Vector.Base.length` gives it as a `nat`. *)
val len:
    #a:Type
  -> t a
  -> len_t

(*| The length of a dynamically sized vector as a `nat`.

    Defined as `U32.v (len x)`; see `FStar.Vector.Base.len`. Marked with a
    deprecation note saying it will be moved to the ghost effect. *)
[@@"deprecated: this will be moved to the ghost effect"]
let length (#a:Type) (x:t a) : nat = U32.v (len x)

(*| Returns the raw vector underlying a dynamically sized vector, with length
    `len x`.

    The inverse of `FStar.Vector.Base.from_raw`. *)
val as_raw:
    #a:Type
  -> x:t a
  -> raw a (len x)

(*| Packs a raw vector as a dynamically sized vector of the same length.

    The inverse of `FStar.Vector.Base.as_raw`. *)
val from_raw:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> x:t a{len x = l}

(*| Unpacking a packed raw vector gives back the original raw vector.

    Triggered automatically on `from_raw v`. *)
val as_raw_from_raw:
    #a:Type
  -> #l:len_t
  -> v:raw a l
  -> Lemma (ensures (as_raw (from_raw v) == v))
          [SMTPat (from_raw v)]

(*| Packing the raw vector of a dynamically sized vector gives back the
    original vector.

    Triggered automatically on `as_raw x`. *)
val from_raw_as_raw:
    #a:Type
  -> x:t a
  -> Lemma (ensures (from_raw (as_raw x) == x))
          [SMTPat (as_raw x)]

(*| Notation: `x.(i)` is the element at position `i` of the dynamically sized
    vector `x`.

    Defined as `(as_raw x).[i]`; see `FStar.Vector.Base.index`. *)
unfold
let ( .() )
    (#a:Type)
    (x:t a)
    (i:index_t (as_raw x))
  : Tot a
  = (as_raw x).[i]

(*| Notation: `x.(i) <- v` is the dynamically sized vector that differs from
    `x` only at position `i`, where it holds `v`.

    Defined with `FStar.Vector.Base.update`. *)
unfold
let ( .()<- )
    (#a:Type)
    (x:t a)
    (i:index_t (as_raw x))
    (v:a)
  : Tot (t a)
  = from_raw ((as_raw x).[i] <- v)

(*| Appends two dynamically sized vectors.

    The precondition requires the sum of the lengths to fit in 32 bits.
    Defined with `FStar.Vector.Base.append`. *)
unfold
let (@@)
    (#a:Type)
    (x1:t a)
    (x2:t a{UInt.size (length x1 + length x2) U32.n})
  : Tot (t a)
  = from_raw (as_raw x1 @| as_raw x2)

(*| Returns the sub-vector of a dynamically sized vector from position `i` up
    to, but not including, position `j`.

    Requires `i <= j <= length x`. Defined with `FStar.Vector.Base.sub`. *)
unfold
let slice
    (#a:Type)
    (x:t a)
    (i:len_t)
    (j:len_t{U32.(v i <= v j /\ v j <= length x)})
  : Tot (t a)
  = from_raw (sub (as_raw x) i j)

(*| A placeholder of type `unit` with no documented purpose; client code
    has no reason to use it. *)
val dummy : unit
