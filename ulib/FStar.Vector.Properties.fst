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

module FStar.Vector.Properties
open FStar.Vector.Base
module U32 = FStar.UInt32

(*| Views a raw vector of length `l` at a length `m` that is provably equal
    to `l`.

    The identity. A workaround for type inference: when a `raw a (l1 + l2)`
    is expected as a `raw a (m1 + m2)`, F\* tries to prove `l1 = m1` and
    `l2 = m2`, which is often too strong; coercing asks only for the
    equality of the sums. *)
unfold
let coerce
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (m:len_t{l == m})
  : Tot (raw a m)
  = v

(*| States that applying the arithmetic operation `op` to the values of `l1`
    and `l2` gives a result that fits in 32 bits.

    For example, `ok (+) l1 l2` is the precondition of
    `FStar.Vector.Base.append`. *)
unfold
let ok
    (op:int -> int -> int)
    (l1:len_t)
    (l2:len_t)
  : prop
  = UInt.size U32.(op (v l1) (v l2)) U32.n

/// Most lemmas from FStar.Seq.Properties can just be lifted
/// to vectors, although the lengths have to be bounds checked
(*| Appending raw vectors is injective when one of the two pairs of parts has
    equal lengths.

    If `u1 @| u2` and `v1 @| v2` are extensionally equal and `l1 == m1` or
    `l2 == m2`, then both length pairs are equal and `u1`, `u2` are
    extensionally equal to `v1`, `v2` (`FStar.Vector.Base.equal`). The lift
    of `FStar.Seq.Properties.lemma_append_inj`. *)
let append_inj
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (#m1:len_t)
    (#m2:len_t)
    (u1:raw a l1)
    (u2:raw a l2{ok (+) l1 l2})
    (v1:raw a m1)
    (v2:raw a m2{ok (+) m1 m2})
  : Lemma
    (requires (let open U32 in
               m1 + m2 = l1 + l2 /\
               equal (u1@|u2) (coerce (v1@|v2) (l1 + l2)) /\
               (l1 == m1 \/ l2 == m2)))
    (ensures (l1 = m1 /\
              l2 = m2 /\
              equal u1 v1 /\
              equal u2 v2))
  = FStar.Seq.lemma_append_inj (reveal u1) (reveal u2) (reveal v1) (reveal v2)

(*| Returns the first element of a nonempty raw vector. *)
let head (#a:Type) (#l:len_t{l <> 0ul}) (v:raw a l)
  : Tot a
  = v.[0ul]

(*| Returns a nonempty raw vector without its first element.

    Defined as `sub v 1ul l`; see `FStar.Vector.Base.sub`. *)
let tail (#a:Type) (#l:len_t{l <> 0ul}) (v:raw a l)
  : Tot (raw a U32.(l - 1ul))
  = sub v 1ul l

(*| The first element of `v1 @| v2` is the first element of `v1`, when `v1`
    is nonempty. *)
let head_append
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 <> 0ul})
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma
    (ensures (head (v1@|v2) == head v1))
  = ()

(*| The tail of `v1 @| v2` is the tail of `v1` followed by `v2`, when `v1` is
    nonempty.

    Proved from `FStar.Seq.Properties.lemma_tail_append`. *)
let tail_append
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 <> 0ul})
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma
    (ensures (tail (v1@|v2) == tail v1@|v2))
  = Seq.lemma_tail_append (reveal v1) (reveal v2)

/// and so on ...
