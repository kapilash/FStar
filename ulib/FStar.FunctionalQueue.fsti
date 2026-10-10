(*
   Copyright 2008-2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Megan Frisella
*)
module FStar.FunctionalQueue

open FStar.Seq

(*| Abstract type of purely functional FIFO queues.

    A queue is specified by the sequence of its elements, front first, given
    by `FStar.FunctionalQueue.queue_to_seq`; the lemmas of this module relate
    each operation to `FStar.Seq` operations on that sequence
    (`FStar.Seq.Properties.snoc`, `FStar.Seq.Properties.head`,
    `FStar.Seq.Properties.tail`). The
    representation is hidden and not canonical: two queues with the same
    elements are `FStar.FunctionalQueue.equal` but not necessarily `==`.

    ```fstar
    let peek_after_enqueue (x: int)
      : Lemma (FStar.FunctionalQueue.peek (FStar.FunctionalQueue.enqueue x FStar.FunctionalQueue.empty) == x)
      = ()
    ``` *)
val queue (a:Type u#a) : Type u#a

(*| The empty queue, whose sequence of elements is `FStar.Seq.Base.empty`.

    See `FStar.FunctionalQueue.lemma_empty_ok`. *)
val empty (#a:Type) : queue a

(*| The sequence of elements of a queue, front (next to be dequeued) first.

    This is the specification of a queue; all lemmas are stated in terms of it. *)
val queue_to_seq (#a:Type) (q:queue a) : seq a

(*| Builds a queue whose elements are those of a sequence, front first.

    `queue_to_seq (queue_of_seq s) == s` (see
    `FStar.FunctionalQueue.lemma_seq_queue_bij`). *)
val queue_of_seq (#a:Type) (s:seq a) : queue a

(*| Equality of queues by their sequence of elements.

    Unlike `==`, it ignores the hidden representation. Introduced by
    `FStar.FunctionalQueue.lemma_eq_intro` and eliminated by
    `FStar.FunctionalQueue.lemma_eq_elim`. *)
val equal (#a:Type) (q1 q2:queue a) : prop

(*| Holds when a queue has at least one element.

    Defined on `queue_to_seq q`: it is not `FStar.Seq.Base.equal` to the empty sequence and has
    positive length. It is the precondition of `FStar.FunctionalQueue.dequeue`
    and `FStar.FunctionalQueue.peek`. *)
let not_empty (#a:Type) (q:queue a) : prop
  = let s = queue_to_seq q in
    ~(Seq.equal s Seq.empty) /\ length s > 0

(*| Queues whose element sequences are `FStar.Seq.Base.equal` are `FStar.FunctionalQueue.equal`.

    Triggered automatically on `equal q1 q2`. *)
val lemma_eq_intro: #a:Type -> q1:queue a -> q2:queue a -> Lemma
  (requires Seq.equal (queue_to_seq q1) (queue_to_seq q2))
  (ensures (equal q1 q2))
  [SMTPat (equal q1 q2)]

(*| `FStar.FunctionalQueue.equal` queues have the same element sequence: `queue_to_seq q1 == queue_to_seq q2`.

    It does not give `q1 == q2`. Triggered automatically on `equal q1 q2`. *)
val lemma_eq_elim: #a:Type -> q1:queue a -> q2:queue a -> Lemma
  (requires (equal q1 q2))
  (ensures queue_to_seq q1 == queue_to_seq q2)
  [SMTPat (equal q1 q2)]

(*| Converting a sequence to a queue and back gives the same sequence: `queue_to_seq (queue_of_seq s) == s`.

    Triggered automatically on `queue_of_seq s`. *)
val lemma_seq_queue_bij: #a:Type -> s:seq a -> Lemma
  (queue_to_seq (queue_of_seq s) == s)
  [SMTPat (queue_of_seq s)]

(*| Converting a queue to a sequence and back gives an `FStar.FunctionalQueue.equal` queue.

    States `equal (queue_of_seq (queue_to_seq q)) q`, not `==`. Triggered
    automatically on `queue_to_seq q`. *)
val lemma_queue_seq_bij: #a:Type -> q:queue a -> Lemma
  (equal (queue_of_seq (queue_to_seq q)) q)
  [SMTPat (queue_to_seq q)]

(*| Adds an element at the back of a queue.

    `queue_to_seq (enqueue x q) == Seq.snoc (queue_to_seq q) x` (see
    `FStar.FunctionalQueue.lemma_enqueue_ok`). *)
val enqueue (#a:Type) (x:a) (q:queue a) : queue a

(*| Removes the front element of a nonempty queue, returning it with the rest of the queue.

    Requires `FStar.FunctionalQueue.not_empty q`. The element is the head of
    `queue_to_seq q` and the remaining queue is `FStar.FunctionalQueue.equal`
    to one with its tail (see `FStar.FunctionalQueue.lemma_dequeue_ok`). *)
val dequeue (#a:Type) (q:queue a{not_empty q}) : a & queue a

(*| Returns the front element of a nonempty queue without removing it.

    Requires `FStar.FunctionalQueue.not_empty q`. The result is the head of
    `queue_to_seq q` (see `FStar.FunctionalQueue.lemma_peek_ok`). *)
val peek (#a:Type) (q:queue a{not_empty q}) : a

(*| The empty queue has no elements: `queue_to_seq empty == Seq.empty`.

    Triggered automatically on `empty`. *)
val lemma_empty_ok: #a:Type -> Lemma
  (queue_to_seq #a empty == Seq.empty)
  [SMTPat (empty #a)]

(*| Enqueuing appends at the back: `queue_to_seq (enqueue x q) == Seq.snoc (queue_to_seq q) x`.

    Triggered automatically on `enqueue x q`. *)
val lemma_enqueue_ok: #a:Type -> x:a -> q:queue a -> Lemma
  (queue_to_seq (enqueue x q) == Seq.snoc (queue_to_seq q) x)
  [SMTPat (enqueue x q)]

(*| Dequeuing returns the head of the element sequence and a queue holding its tail.

    For `let hd, tl = dequeue q`, `hd == Seq.head (queue_to_seq q)` and
    `equal tl (queue_of_seq (Seq.tail (queue_to_seq q)))`. Triggered
    automatically on `dequeue q`. *)
val lemma_dequeue_ok: #a:Type -> q:queue a{not_empty q} -> Lemma
  (let hd, tl = dequeue q in
   hd == Seq.head (queue_to_seq q) /\
   equal tl (queue_of_seq (Seq.tail (queue_to_seq q))))
  [SMTPat (dequeue q)]

(*| Peeking returns the head of the element sequence: `peek q == Seq.head (queue_to_seq q)`.

    Triggered automatically on `peek q`. *)
val lemma_peek_ok: #a:Type -> q:queue a{not_empty q} -> Lemma
  (peek q == Seq.head (queue_to_seq q))
  [SMTPat (peek q)]
