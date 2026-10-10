(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.OrdSet

(*| `total_order a f` holds when the boolean relation `f` is a non-strict
    total order on `a`: antisymmetric, transitive and total (hence also
    reflexive), like `<=` on integers. *)
type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
   (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2)  (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)   (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                 (* totality      *)

(*| The type of comparison functions usable to order the elements of
    `FStar.OrdSet.ordset`: boolean relations that satisfy
    `FStar.OrdSet.total_order`, such as `fun x y -> x <= y` on `int`. *)
type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

(*| Tests whether a list is strictly increasing with respect to `f`: every
    element is related by `f` to, and different from, the next one.

    The representation invariant of `FStar.OrdSet.ordset`; sorted lists have
    no duplicates. *)
let rec sorted (#a:eqtype) (f:cmp a) (l:list a) : Tot bool =
  match l with
  | []       -> true
  | x::[]    -> true
  | x::y::tl -> f x y && x <> y && sorted f (y::tl)

(*| The type of finite sets of elements of an `eqtype`, kept in increasing
    order with respect to the comparison function `f`.

    A set is represented by a list that is `FStar.OrdSet.sorted` by `f`, so
    each set has a single representation: `ordset a f` has decidable equality
    (see `FStar.OrdSet.hasEq_ordset`) and `=` on sets coincides with having the
    same members (see `FStar.OrdSet.equal` and `FStar.OrdSet.eq_lemma`).
    Membership, size, and the order-aware operations `FStar.OrdSet.head` and
    `FStar.OrdSet.last` are all computable.

    ```fstar
    let int_le : FStar.OrdSet.cmp int = fun x y -> x <= y
    let s12 : FStar.OrdSet.ordset int int_le =
      FStar.OrdSet.union (FStar.OrdSet.singleton 1) (FStar.OrdSet.singleton 2)
    let _ = assert (FStar.OrdSet.mem 2 s12 /\ not (FStar.OrdSet.mem 3 s12))
    ```

    For possibly infinite sets with no order, see `FStar.Set`. *)
val ordset (a:eqtype) (f:cmp a) : Type0

(*| `FStar.OrdSet.ordset` supports decidable equality.

    Triggered automatically on `hasEq (ordset a f)`. *)
val hasEq_ordset: a:eqtype -> f:cmp a
  -> Lemma (requires (True)) (ensures (hasEq (ordset a f)))
    [SMTPat (hasEq (ordset a f))]

(*| The set with no members (see `FStar.OrdSet.mem_empty`). *)
val empty        : #a:eqtype -> #f:cmp a -> Tot (ordset a f)

(*| Returns the non-empty set `s` without its least element
    `FStar.OrdSet.head s`.

    `FStar.OrdSet.size_of_tail` and `FStar.OrdSet.count_of_tail` relate it to
    `s`. *)
val tail (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty}) : ordset a f
(*| Returns the least element, with respect to `f`, of the non-empty set `s`. *)
val head (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty}) : a 

(*| Tests whether `x` is a member of `s`. *)
val mem          : #a:eqtype -> #f:cmp a -> a -> s:ordset a f -> Tot bool

(*| `mem_of s x` is `mem x s`, with the set first so that `mem_of s` can be
    used as a `FStar.OrdSet.condition`. *)
unfold let mem_of #a #f (s:ordset a f) x = mem x s

(*| Returns the greatest element, with respect to `f`, of the non-empty set
    `s`. *)
val last (#a:eqtype) (#f:cmp a) (s: ordset a f{s <> empty}) 
  : Tot (x:a{(forall (z:a{mem z s}). f z x) /\ mem x s})

(*| Returns the non-empty set `s` without its greatest element
    `FStar.OrdSet.last s`: the counterpart of `FStar.OrdSet.tail` at the other
    end ("liat" is "tail" reversed).

    If `s` has at least two elements, the result is non-empty and has the same
    `FStar.OrdSet.head` as `s`. It is the first component of
    `FStar.OrdSet.unsnoc s`. *)
val liat (#a:eqtype) (#f:cmp a) (s: ordset a f{s <> empty}) : Tot (l:ordset a f{
    (forall x. mem x l = (mem x s && (x <> last s))) /\
    (if tail s <> empty then (l <> empty) && (head s = head l) else true)
  })

(*| Splits a non-empty set into the pair of `FStar.OrdSet.liat s` and
    `FStar.OrdSet.last s`. *)
val unsnoc (#a:eqtype) (#f:cmp a) (s: ordset a f{s <> empty}) : Tot (p:(ordset a f & a){
    p = (liat s, last s) 
  }) 

(*| Returns the elements of `s` as a list in increasing order with respect to
    `f`, without duplicates. *)
val as_list (#a:eqtype) (#f:cmp a) (s:ordset a f) : Tot (l:list a{
  sorted f l /\
  (forall x. (List.Tot.mem x l = mem x s))   
})

(*| Returns the set of the elements of the list `l`: duplicates are removed and
    the order of `l` is irrelevant.

    `FStar.OrdSet.distinct_is_idempotent` states that it inverts
    `FStar.OrdSet.as_list`. *)
val distinct (#a:eqtype) (f:cmp a) (l: list a) : Pure (ordset a f) 
  (requires True) (ensures fun z -> forall x. (mem x z = List.Tot.Base.mem x l))

(*| The set of elements that are members of either argument (see
    `FStar.OrdSet.mem_union`). *)
val union        : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)
(*| The set of elements that are members of both arguments (see
    `FStar.OrdSet.mem_intersect`). *)
val intersect    : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)

(*| Returns some member of `s`, or `None` if `s` is empty.

    The interface specifies only `FStar.OrdSet.choose_empty` and
    `FStar.OrdSet.choose_s`, not which member is chosen. *)
val choose       : #a:eqtype -> #f:cmp a -> s:ordset a f -> Tot (option a)
(*| Returns `s` without the element `x` (see `FStar.OrdSet.mem_remove`); the
    set is unchanged if `x` is not a member. *)
val remove       : #a:eqtype -> #f:cmp a -> a -> ordset a f -> Tot (ordset a f)

(*| Returns the number of elements of `s`. *)
val size         : #a:eqtype -> #f:cmp a -> ordset a f -> Tot nat

(*| Tests whether every member of the first set is a member of the second (see
    `FStar.OrdSet.mem_subset`). *)
val subset       : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot bool
(*| `superset s1 s2` is `subset s2 s1`. *)
let superset #a #f (s1 s2: ordset a f) : Tot bool = subset s2 s1

(*| The set whose only member is the argument (see
    `FStar.OrdSet.mem_singleton`). *)
val singleton    : #a:eqtype -> #f:cmp a -> a -> Tot (ordset a f)

(*| Set difference: the members of the first set that are not members of the
    second (see `FStar.OrdSet.lemma_minus_mem`). *)
val minus        : #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot (ordset a f)

(*| Tests whether the first set is a subset of the second and different from
    it.

    See `FStar.OrdSet.lemma_strict_subset_size` and
    `FStar.OrdSet.lemma_strict_subset_exists_diff`. *)
val strict_subset: #a:eqtype -> #f:cmp a -> ordset a f -> ordset a f -> Tot bool
(*| `strict_superset s1 s2` is `strict_subset s2 s1`. *)
let strict_superset #a #f (s1 s2: ordset a f) : Tot bool = strict_subset s2 s1

(*| Tests whether two sets have no common member, that is, whether their
    intersection is `FStar.OrdSet.empty`. *)
let disjoint #a #f (s1 s2 : ordset a f) : Tot bool = intersect s1 s2 = empty

(*| Extensional equality: `equal s1 s2` holds when `s1` and `s2` have the same
    members.

    `FStar.OrdSet.eq_lemma`, triggered automatically on `equal s1 s2`, turns it
    into `s1 = s2`. *)
let equal (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) : Tot prop =
  forall x. mem #_ #f x s1 = mem #_ #f x s2

(*| Sets with the same members are equal: `equal s1 s2` implies `s1 = s2`.

    Triggered automatically on `equal s1 s2`. *)
val eq_lemma: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
              -> Lemma (requires (equal s1 s2))
                       (ensures (s1 = s2))
                 [SMTPat (equal s1 s2)]

(*| No element is a member of `FStar.OrdSet.empty`.

    Triggered automatically on `mem x empty`. *)
val mem_empty: #a:eqtype -> #f:cmp a -> x:a
               -> Lemma (requires True) (ensures (not (mem #a #f x (empty #a #f))))
                  [SMTPat (mem #a #f x (empty #a #f))]

(*| `y` is a member of `singleton x` exactly when `x = y`.

    Triggered automatically on `mem y (singleton x)`. *)
val mem_singleton: #a:eqtype -> #f:cmp a -> x:a -> y:a
                   -> Lemma (requires True)
                            (ensures (mem #a #f y (singleton #a #f x)) = (x = y))
                      [SMTPat (mem #a #f y (singleton #a #f x))]
 
(*| `x` is a member of `union s1 s2` exactly when it is a member of `s1` or of
    `s2`.

    Triggered automatically on `mem x (union s1 s2)`. *)
val mem_union: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f -> x:a
               -> Lemma (requires True)
                        (ensures (mem #a #f x (union #a #f s1 s2) =
                                  (mem #a #f x s1 || mem #a #f x s2)))
                  [SMTPat (mem #a #f x (union #a #f s1 s2))]

(*| `x` is a member of `intersect s1 s2` exactly when it is a member of both
    `s1` and `s2`.

    Triggered automatically on `mem x (intersect s1 s2)`. *)
val mem_intersect: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f -> x:a
                   -> Lemma (requires True)
                            (ensures (mem #a #f x (intersect s1 s2) =
                                      (mem #a #f x s1 && mem #a #f x s2)))
                      [SMTPat (mem #a #f x (intersect #a #f s1 s2))]

(*| `subset s1 s2` is `true` exactly when every member of `s1` is a member of
    `s2`.

    Triggered automatically on `subset s1 s2`. *)
val mem_subset: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires True)
                         (ensures  (subset #a #f s1 s2 <==>
                                    (forall x. mem #a #f x s1 ==> mem #a #f x s2)))
                   [SMTPat (subset #a #f s1 s2)]

(*| `choose empty` is `None`.

    Triggered automatically on `choose empty`. *)
val choose_empty: #a:eqtype -> #f:cmp a
                  -> Lemma (requires True) (ensures (None? (choose #a #f (empty #a #f))))
                     [SMTPat (choose #a #f (empty #a #f))]

(* TODO: FIXME: Pattern does not contain all quantified vars *)
(*| On a non-empty set, `choose s` returns `Some x` for a member `x`, and `s`
    is the union of `singleton x` and `remove x s`.

    Triggered automatically on `choose s`. *)
val choose_s: #a:eqtype -> #f:cmp a -> s:ordset a f
              -> Lemma (requires (not (s = (empty #a #f))))
                       (ensures (Some? (choose #a #f s) /\
                                 s = union #a #f (singleton #a #f (Some?.v (choose #a #f s)))
                                                 (remove #a #f (Some?.v (choose #a #f s)) s)))
                 [SMTPat (choose #a #f s)]

(*| `x` is a member of `remove y s` exactly when it is a member of `s` and
    differs from `y`.

    Triggered automatically on `mem x (remove y s)`. *)
val mem_remove: #a:eqtype -> #f:cmp a -> x:a -> y:a -> s:ordset a f
                -> Lemma (requires True)
                         (ensures (mem #a #f x (remove #a #f y s) =
                                   (mem #a #f x s && not (x = y))))
                   [SMTPat (mem #a #f x (remove #a #f y s))]

(*| Removing a non-member leaves the set unchanged.

    Triggered automatically on `remove x s`. *)
val eq_remove: #a:eqtype -> #f:cmp a -> x:a -> s:ordset a f
               -> Lemma (requires (not (mem #a #f x s)))
                        (ensures (s = remove #a #f x s))
                  [SMTPat (remove #a #f x s)]

(*| A set has size 0 exactly when it is `FStar.OrdSet.empty`.

    Triggered automatically on `size s`. *)
val size_empty: #a:eqtype -> #f:cmp a -> s:ordset a f
                -> Lemma (requires True) (ensures ((size #a #f s = 0) = (s = empty #a #f)))
                  [SMTPat (size #a #f s)]

(*| Removing a member decreases the size by one.

    Triggered automatically on `size (remove y s)`. *)
val size_remove: #a:eqtype -> #f:cmp a -> y:a -> s:ordset a f
                 -> Lemma (requires (mem #a #f y s))
                          (ensures (size #a #f s = size #a #f (remove #a #f y s) + 1))
                    [SMTPat (size #a #f (remove #a #f y s))]

(*| A singleton set has size 1.

    Triggered automatically on `size (singleton x)`. *)
val size_singleton: #a:eqtype -> #f:cmp a -> x:a
                    -> Lemma (requires True) (ensures (size #a #f (singleton #a #f x) = 1))
                       [SMTPat (size #a #f (singleton #a #f x))]

(*| A subset is no larger than the set containing it.

    Triggered automatically on `subset x y`. *)
val subset_size: #a:eqtype -> #f:cmp a -> x:ordset a f -> y:ordset a f
                 -> Lemma (requires (subset #a #f x y))
 	                  (ensures (size #a #f x <= size #a #f y))
	           [SMTPat (subset #a #f x y)]

(**********)

(*| A union is at least as large as each of its arguments.

    Triggered automatically on `size (union s1 s2)`. For the exact size see
    `FStar.OrdSet.size_of_union`. *)
val size_union: #a:eqtype -> #f:cmp a -> s1:ordset a f -> s2:ordset a f
                -> Lemma (requires True)
                         (ensures ((size #a #f (union #a #f s1 s2) >= size #a #f s1) &&
                                   (size #a #f (union #a #f s1 s2) >= size #a #f s2)))
                         [SMTPat (size #a #f (union #a #f s1 s2))]

(**********)

(*| Folds `g` over the elements of `s`, starting from `init`.

    The interface provides no lemma about the result. *)
val fold (#a:eqtype) (#acc:Type) (#f:cmp a) (g:acc -> a -> acc) (init:acc) (s:ordset a f)
  : Tot acc

(*| Returns the image of `sa` under `g`.

    The caller must prove that `g` is monotone (it maps `fa`-ordered pairs to
    `fb`-ordered pairs) and injective. The elements of the result, in order,
    are those of `sa` with `g` applied, so its size is at most that of `sa`. *)
val map (#a #b:eqtype) (#fa:cmp a) (#fb:cmp b) (g:a -> b) (sa:ordset a fa)
  : Pure (ordset b fb)
    (requires (forall x y. (x `fa` y ==> g x `fb` g y) /\ (x = y <==> g x = g y)))
    (ensures (fun sb -> (size sb <= size sa) /\  
                     (as_list sb == FStar.List.Tot.map g (as_list sa)) /\
                     (let sa = as_list sa in
                      let sb = as_list sb in
                      Cons? sb ==> Cons? sa /\ Cons?.hd sb == g (Cons?.hd sa))))

(*| A strict subset is a subset and is strictly smaller.

    Triggered automatically on `strict_subset s1 s2`. *)
val lemma_strict_subset_size (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (requires (strict_subset s1 s2))
          (ensures  (subset s1 s2 /\ size s1 < size s2))
    [SMTPat (strict_subset s1 s2)]

(*| `x` is a member of `minus s1 s2` exactly when it is a member of `s1` and
    not of `s2`.

    Triggered automatically on `mem x (minus s1 s2)`. *)
val lemma_minus_mem (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (x:a)
  : Lemma (requires True) (ensures (mem x (minus s1 s2) = (mem x s1 && not (mem x s2))))
    [SMTPat (mem x (minus s1 s2))]

(*| For `s1` a subset of `s2`, `s1` is a strict subset exactly when some member
    of `s2` is not a member of `s1`.

    This lemma has no SMT pattern: call it explicitly. *)
val lemma_strict_subset_exists_diff (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) 
  : Lemma (requires subset s1 s2)
          (ensures (strict_subset s1 s2) <==> (exists x. (mem x s2 /\ not (mem x s1)))) 

(*| The type of boolean predicates on `a`, used to select elements in
    `FStar.OrdSet.count`, `FStar.OrdSet.where`, `FStar.OrdSet.any` and related
    functions. *)
type condition a = a -> bool

(*| The negation of a condition: `inv c x` is `not (c x)`. *)
let inv #a (c: condition a) : (z:condition a{forall x. c x = not (z x)}) = fun x -> not (c x)

(*| Returns the number of elements of `s` that satisfy `c`.

    It equals `size (where s c)` (see `FStar.OrdSet.count_is_size_of_where`). *)
val count (#a:eqtype) (#f: cmp a) (s: ordset a f) (c: condition a) : nat

(*| No element of an empty set satisfies any condition: `count s c = 0`. *)
val count_of_empty (#a:eqtype) (#f: cmp a) (s: ordset a f{size s = 0}) (c: condition a)
  : Lemma (count s c = 0)

(*| No element satisfies a condition that is always `false`: `count s c = 0`. *)
val count_of_impossible (#a:eqtype) (#f: cmp a) (s: ordset a f) (c: condition a{forall p. not (c p)})
  : Lemma (count s c = 0)

(*| Every element satisfies a condition that is always `true`: `count s c` is
    `size s`. *)
val count_all (#a:eqtype) (#f: cmp a) (s: ordset a f) (c: condition a{forall p. c p})
  : Lemma (count s c = size s)

(*| Unfolds `count` on a non-empty set: the count on `tail s`, plus one if
    `head s` satisfies `c`.

    The same statement as `FStar.OrdSet.count_of_tail`. *)
val count_of_cons (#a:eqtype) (#f: cmp a) (s: ordset a f{size s > 0}) (c: condition a)
  : Lemma (count s c = (count (tail s) c + (if (c (head s)) then 1 else 0)))

(*| Tests whether every element of `s` satisfies `c`. *)
val all (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) : Tot bool

(*| Tests whether some element of `s` satisfies `c`. *)
val any (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) : Tot bool

(*| If a member `x` of `s` satisfies `c`, then `any s c`. *)
val mem_if_any (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) (x:a{mem x s && c x})
  : Lemma (any s c) 
  
(*| `all s c` holds exactly when no element of `s` satisfies `inv c`. *)
val all_means_not_any_not (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) 
  : Lemma (all s c = not (any s (inv c))) 

(*| Returns the least element of `s` that satisfies `c`, or `None` if there is
    none.

    See `FStar.OrdSet.find_first_is_some_iff_any` and
    `FStar.OrdSet.find_first_precedes_any_other`. *)
val find_first (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) : option a  

(*| `find_first s c` is `Some` exactly when `any s c`. *)
val find_first_is_some_iff_any (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) 
  : Lemma (Some? (find_first s c) = any s c)  

(*| `find_first s c` finds an element that precedes (by `f`) every member of
    `s` satisfying `c`. *)
val find_first_precedes_any_other (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) (x:a{mem x s && c x})
  : Lemma (Some? (find_first s c) && f (Some?.v (find_first s c)) x) 

(*| `liat s` has one element fewer than `s`. *)
val liat_size (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty})
  : Lemma (size (liat s) = ((size s)-1))

(*| The members of `s` are the members of `liat s` together with `last s`. *)
val mem_liat (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty}) (x:a)
  : Lemma (mem x s = (mem x (liat s) || x = last s))

(*| Some element of `s` satisfies `c` exactly when some element of `liat s`
    does or `last s` does. *)
val any_liat (#a:eqtype) (#f:cmp a) (s:ordset a f{s<>empty}) (c:condition a)
  : Lemma (any s c = (any (liat s) c || c (last s)))

(*| Returns the greatest element of `s` that satisfies `c`, or `None` if there
    is none.

    The result type states both facts; see also
    `FStar.OrdSet.find_last_is_some_iff_any` and
    `FStar.OrdSet.find_last_follows_any_other`. *)
val find_last (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a) : (z:option a{ match z with
  | None -> not (any s c)
  | Some v -> (any s c /\ (forall (x:a{mem x s && c x}). f x v))
})

(*| `find_last s c` is `Some` exactly when `any s c`. *)
val find_last_is_some_iff_any (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) 
  : Lemma (Some? (find_last s c) = any s c)  

(*| `find_last s c` finds an element that follows (by `f`) every member of `s`
    satisfying `c`. *)
val find_last_follows_any_other (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) (x:a{mem x s && c x})
  : Lemma (Some? (find_last s c) && f x (Some?.v (find_last s c))) 

(*| `tail s` has one element fewer than the non-empty set `s`. *)
val size_of_tail (#a:eqtype) (#f:cmp a) (s:ordset a f{size s > 0})
  : Lemma (size s = 1 + (size (tail s)))

(*| Unfolds `count` on a non-empty set: the count on `tail s`, plus one if
    `head s` satisfies `c`.

    The same statement as `FStar.OrdSet.count_of_cons`. *)
val count_of_tail (#a:eqtype) (#f:cmp a) (s:ordset a f{size s > 0}) (c: condition a)
  : Lemma (count s c = (count (tail s) c + (if c (head s) then 1 else 0))) 

(*| Returns the set of elements of `s` that satisfy `c`.

    Its list of elements is `FStar.List.Tot.Base.filter c (as_list s)`. *)
val where (#a:eqtype) (#f:cmp a) (s:ordset a f) (c: condition a) 
  : Pure (ordset a f) 
         (requires True)
         (ensures fun (z:ordset a f) -> 
               (as_list #a  z == FStar.List.Tot.Base.filter c (as_list s)) /\
               (forall x. mem x z = (mem x s && c x)) /\
               (if size z > 0 && size s > 0 then f (head s) (head z) else true))

(*| `intersect s1 s2` is the set of elements of `s1` that are members of `s2`,
    `where s1 (mem_of s2)`. *)
val intersect_eq_where (#a:eqtype) (#f:cmp a) (s1 s2:ordset a f)  
  : Lemma (intersect s1 s2 = where s1 (mem_of s2))

(*| `minus s1 s2` is the set of elements of `s1` that are not members of `s2`,
    `where s1 (inv (mem_of s2))`. *)
val minus_eq_where (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f)
  : Lemma (minus s1 s2 = where s1 (inv (mem_of s2))) 
 
(*| `count s c` is the size of `where s c`. *)
val count_is_size_of_where (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a)
  : Lemma (count s c = size (where s c)) 

(*| The size of `intersect s1 s2` is the number of elements of either set that
    are members of the other. *)
val size_of_intersect (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f) 
  : Lemma (ensures size (intersect s1 s2) = count s1 (mem_of s2) /\
                   size (intersect s1 s2) = count s2 (mem_of s1))

(*| The size of a union is the sum of the sizes minus the size of the
    intersection. *)
val size_of_union (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f)
  : Lemma (size (union s1 s2) = (size s1 + size s2 - size (intersect s1 s2)))

(*| Every element of `s` satisfies exactly one of `c` and `inv c`, so the two
    counts add up to `size s`. *)
val count_dichotomy (#a:eqtype) (#f:cmp a) (s: ordset a f) (c: condition a)
  : Lemma (size s = count s c + count s (inv c))  

(*| The size of `minus s1 s2` is the size of `s1` minus the size of
    `intersect s1 s2`. *)
val size_of_minus (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f)
  : Lemma (size (minus s1 s2) = size s1 - size (intersect s1 s2))

(*| If `s1` is a subset of `s2`, then `intersect s1 s2 = s1`. *)
val intersect_with_subset (#a:eqtype) (#f:cmp a) (s1 s2: ordset a f)
  : Lemma (requires subset s1 s2) 
          (ensures intersect s1 s2 = s1)
  
(*| If `s1` is a strict subset of `s2` and both are subsets of `s`, removing
    the larger set from `s` leaves fewer elements: `minus s s2` is smaller than
    `minus s s1`.

    Triggered automatically when `strict_subset s1 s2`, `subset s1 s` and
    `subset s2 s` all appear. *)
val lemma_strict_subset_minus_size (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s:ordset a f)
  : Lemma (requires (strict_subset s1 s2 /\ subset s1 s /\ subset s2 s))
          (ensures  (size (minus s s2) < size (minus s s1)))
    [SMTPat (strict_subset s1 s2); SMTPat (subset s1 s); SMTPat (subset s2 s)]

(*| Each of two non-empty disjoint sets is a strict subset of their union.

    Triggered automatically on `strict_subset s1 (union s1 s2)` or
    `strict_subset s2 (union s1 s2)`. *)
val lemma_disjoint_union_subset (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (requires (~ (s1 == empty) /\ ~ (s2 == empty) /\ intersect s1 s2 == empty))
          (ensures  (strict_subset s1 (union s1 s2) /\ strict_subset s2 (union s1 s2)))
    [SMTPatOr [[SMTPat (strict_subset s1 (union s1 s2))]; [SMTPat (strict_subset s2 (union s1 s2))]]]

(*| The union of two subsets of `s` is a subset of `s`.

    Triggered automatically on `subset (union s1 s2) s`. *)
val lemma_subset_union (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s:ordset a f)
  : Lemma (requires (subset s1 s /\ subset s2 s))
          (ensures  (subset (union s1 s2) s))
    [SMTPat (subset (union s1 s2) s)]

(*| `strict_subset` is transitive.

    Triggered automatically when both `strict_subset s1 s2` and
    `strict_subset s2 s3` appear. *)
val lemma_strict_subset_transitive (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s3:ordset a f)
  : Lemma (requires (strict_subset s1 s2 /\ strict_subset s2 s3))
          (ensures  (strict_subset s1 s3))
    [SMTPat (strict_subset s1 s2); SMTPat (strict_subset s2 s3)]

(*| `intersect` is commutative.

    Triggered automatically on `intersect s1 s2` or `intersect s2 s1`. *)
val lemma_intersect_symmetric (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (requires True) (ensures (intersect s1 s2 == intersect s2 s1))
    [SMTPatOr [[SMTPat (intersect s1 s2)]; [SMTPat (intersect s2 s1)]]]

(*| A union is disjoint from `s3` exactly when each of its two arguments is.

    Triggered automatically on `intersect (union s1 s2) s3`. *)
val lemma_intersect_union_empty (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f) (s3:ordset a f)
  : Lemma ((intersect (union s1 s2) s3 = empty) = (intersect s1 s3 = empty && intersect s2 s3 = empty))
    [SMTPat (intersect (union s1 s2) s3)]
 
(*| `union` is commutative.

    Triggered automatically on `union s1 s2`. *)
val lemma_union_symmetric (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (union s1 s2 == union s2 s1)
    [SMTPat (union s1 s2)]

(*| For disjoint `s1` and `s2`, removing `s1` from their union gives back
    `s2`.

    Triggered automatically when both `union s1 s2` and `disjoint s1 s2`
    appear. *)
val union_of_disjoint (#a:eqtype) (#f:cmp a) (s1:ordset a f) (s2:ordset a f)
  : Lemma (requires (disjoint s1 s2))
        (ensures (minus (union s1 s2) s1 == s2))
    [SMTPat (union s1 s2); SMTPat (disjoint s1 s2)]

(*| Converting a set to a list with `FStar.OrdSet.as_list` and back with
    `FStar.OrdSet.distinct` gives the same set. *)
val distinct_is_idempotent (#a:eqtype) (#f: cmp a) (s: ordset a f)
  : Lemma (distinct f (as_list s) = s)

(* Conversion from OrdSet to Set *)

module S = FStar.Set

(*| Converts an ordered set to a `FStar.Set.set` with the same members (see
    `FStar.OrdSet.lemma_as_set_mem`). *)
val as_set : #a:eqtype -> #f:cmp a -> ordset a f -> Tot (S.set a)

(*| `x` is a member of `s` exactly when it is a member of `as_set s`.

    Triggered automatically when both `mem x s` and
    `FStar.Set.mem x (as_set s)` appear. *)
val lemma_as_set_mem (#a:eqtype) (#f:cmp a) (s:ordset a f) (x:a)
  : Lemma (mem x s <==> S.mem x (as_set s))
          [SMTPat (mem x s);
           SMTPat (S.mem x (as_set s))]

(*| Two ordered sets have an empty intersection exactly when their conversions
    by `FStar.OrdSet.as_set` are `FStar.Set.disjoint`.

    Triggered automatically on `FStar.Set.disjoint (as_set s1) (as_set s2)`. *)
val lemma_as_set_disjoint (#a:eqtype) (#f:cmp a) (s1 s2:ordset a f)
  : Lemma (intersect s1 s2 = empty <==> S.disjoint (as_set s1) (as_set s2))
          [SMTPat (S.disjoint (as_set s1) (as_set s2))]
