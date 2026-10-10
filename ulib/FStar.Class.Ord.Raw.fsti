module FStar.Class.Ord.Raw

open FStar.Order
open FStar.Class
open FStar.Class.Eq.Raw { deq }

// raw
(*| Typeclass of comparison functions on `a`, with no laws ("raw").

    Fields:

    - `super`: a `FStar.Class.Eq.Raw.deq` instance for `a`, the superclass.
    - `cmp`: a three-way comparison returning a `FStar.Order.order` (`Lt`, `Eq` or `Gt`).

    Nothing requires `cmp` to be a total order or to agree with `super`; the derived operations assume it does. The comparison operators `<?`, `<=?`, `>?` and `>=?` and the list utilities `sort`, `dedup`, `sort_dedup` and `ord_list_diff` are built on it. *)
class ord (a:Type) = {
  super : deq a;
  cmp : a -> a -> order;
}

(*| Superclass projection: the `FStar.Class.Eq.Raw.deq` instance stored in an `ord` instance. *)
instance val ord_eq (a:Type) (d : ord a) : Tot (deq a)

(*| Strict less-than: true when `cmp x y` is `Lt`. *)
val (<?)  : #a:Type -> {| ord a |} -> a -> a -> bool
(*| Strict greater-than: true when `cmp x y` is `Gt`. *)
val (>?)  : #a:Type -> {| ord a |} -> a -> a -> bool
(*| Less-than-or-equal: true when `cmp x y` is not `Gt`. *)
val (<=?) : #a:Type -> {| ord a |} -> a -> a -> bool
(*| Greater-than-or-equal: true when `cmp x y` is not `Lt`. *)
val (>=?) : #a:Type -> {| ord a |} -> a -> a -> bool

(*| The smaller of two values according to `cmp`; the first argument when they compare equal. *)
val min : #a:Type -> {| ord a |} -> a -> a -> a
(*| The larger of two values according to `cmp`; the first argument when they compare equal. *)
val max : #a:Type -> {| ord a |} -> a -> a -> a

(*| Sorts a list in ascending order according to `cmp`, keeping elements that compare equal in their original order. *)
val sort
  (#a:Type) {| ord a |}
  (xs : list a)
  : list a

(*| Sorts a list in ascending order according to the comparison `f`, without needing an `ord` instance.

    Same behaviour as `FStar.Class.Ord.Raw.sort` with `f` as `cmp`. *)
val sort_by
  (#a:Type) (f : a -> a -> order)
  (xs : list a)
  : list a

(*| Removes duplicates from a list, keeping the first occurrence of each element and the original order.

    For example, deduplicating `[a; b; c; a; f; e; c]` gives `[a; b; c; f; e]`. Duplicates are detected with the `deq` superclass, not with `cmp`. *)
val dedup
  (#a:Type) {| ord a |}
  (xs : list a)
  : list a

(*| Sorts a list in ascending order according to `cmp` and removes elements that compare `Eq` to another, in one pass. *)
val sort_dedup
  (#a:Type) {| ord a |}
  (xs : list a)
  : list a

(*| Computes the difference of two lists, ignoring order and duplicates.

    Returns a pair: the elements present only in `xs`, and those present only in `ys`. Both lists are first sorted and deduplicated with `FStar.Class.Ord.Raw.sort_dedup`, and each result is sorted in ascending order. *)
val ord_list_diff (#a:Type0) {| ord a |} (xs ys : list a) : list a & list a

(*| Ordering on `int`, the usual numeric order. *)
instance val ord_int    : ord int
// instance val ord_bool   : ord bool
(*| Ordering on `unit`: the single value compares `Eq` to itself. *)
instance val ord_unit   : ord unit
(*| Ordering on `string`, following `FStar.String.compare`. *)
instance val ord_string : ord string

(*| Ordering on options: `None` is below every `Some x`, and `Some` values compare by their contents. *)
instance val ord_option
   (_ : ord 'a)
: Tot (ord (option 'a))

(*| Lexicographic ordering on lists, using `FStar.Order.compare_list`. *)
instance val ord_list
   (_ : ord 'a)
: Tot (ord (list 'a))

(*| Ordering on `either`: every `Inl` value is below every `Inr` value, and values with the same constructor compare by their payloads. *)
instance val ord_either
   (_ : ord 'a)
   (_ : ord 'b)
: Tot (ord (either 'a 'b))

(*| Lexicographic ordering on pairs: by first component, then by second. *)
instance val ord_tuple2
   (_ : ord 'a)
   (_ : ord 'b)
: Tot (ord ('a & 'b))

// instance val ord_tuple3
//    (_ : ord 'a)
//    (_ : ord 'b)
//    (_ : ord 'c)
// : Tot (ord ('a & 'b & 'c))

// instance val ord_tuple4
//    (_ : ord 'a)
//    (_ : ord 'b)
//    (_ : ord 'c)
//    (_ : ord 'd)
// : Tot (ord ('a & 'b & 'c & 'd))

// instance val ord_tuple5
//    (_ : ord 'a)
//    (_ : ord 'b)
//    (_ : ord 'c)
//    (_ : ord 'd)
//    (_ : ord 'e)
// : Tot (ord ('a & 'b & 'c & 'd & 'e))

// instance val ord_tuple6
//    (_ : ord 'a)
//    (_ : ord 'b)
//    (_ : ord 'c)
//    (_ : ord 'd)
//    (_ : ord 'e)
//    (_ : ord 'f)
// : Tot (ord ('a & 'b & 'c & 'd & 'e & 'f))
