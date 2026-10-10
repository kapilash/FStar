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

module FStar.IndefiniteDescription

/// Indefinite description is an axiom that allows picking a witness
/// for existentially quantified predicate.
///
/// For some background on the axiom, see:
///
/// https://github.com/coq/coq/wiki/CoqAndAxioms#indefinite-description--hilberts-epsilon-operator
/// https://en.wikipedia.org/wiki/Theory_of_descriptions#Indefinite_descriptions

(*| Picks a witness of the satisfiable predicate `p`, in ghost code.

    The indefinite description axiom, also known as Hilbert's epsilon operator.
    The witness is ghost, so it cannot be used in computationally relevant
    code; see `FStar.IndefiniteDescription.indefinite_description_tot` for an
    erased witness in total code. *)
val indefinite_description_ghost (a: Type) (p: (a -> prop) { exists x. p x })
  : GTot (x: a { p x })

(*| Picks an erased witness of the satisfiable predicate `p`.

    Like `FStar.IndefiniteDescription.indefinite_description_ghost`, but the
    witness is wrapped in `FStar.Ghost.erased`, so total code can use it. *)
val indefinite_description_tot (a:Type) (p:(a -> prop) { exists x. p x })
  : Tot (w:Ghost.erased a{ p w })
    
(*| Decides any proposition `p`, in ghost code: returns `true` exactly when `p`
    holds.

    A consequence of indefinite description. *)
val strong_excluded_middle (p: prop) : GTot (b: bool{b = true <==> p})

(*| Returns a natural number satisfying the boolean predicate `p`, given that
    `p` does not fail for every natural number. *)
val stronger_markovs_principle (p: (nat -> GTot bool))
    : Ghost nat (requires (~(forall (n: nat). ~(p n)))) (ensures (fun n -> p n))

(*| Returns a natural number satisfying the predicate `p`, given that `p` does
    not fail for every natural number.

    The `prop`-valued variant of
    `FStar.IndefiniteDescription.stronger_markovs_principle`. *)
val stronger_markovs_principle_prop (p: (nat -> GTot prop))
    : Ghost nat (requires (~(forall (n: nat). ~(p n)))) (ensures (fun n -> p n))