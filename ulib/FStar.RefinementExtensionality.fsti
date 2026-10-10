module FStar.RefinementExtensionality

(*| Refinement types with equivalent refinements are equal: `x:t{r1 x}` equals
    `x:t{r2 x}` whenever `r1 x <==> r2 x` for every `x`. *)
val refext (t:Type) (r1 : t -> prop) (r2 : t -> prop) :
  Lemma (requires (forall x. r1 x <==> r2 x))
        (ensures (x:t{r1 x} == x:t{r2 x}))
