Proves a universal property one point at a time.

```fstar
let all_nat (f:int -> nat) : Lemma (forall x. f x >= 0) =
  FStar.Classical.forall_intro (fun x -> ())
```
