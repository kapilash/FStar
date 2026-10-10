(*
   Copyright 2008-2021 John Li, Jay Lorch, Rustan Leino, Alex Summers,
   Dan Rosen, Nikhil Swamy, Microsoft Research, and contributors to
   the Dafny Project

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Includes material from the Dafny project
   (https://github.com/dafny-lang/dafny) which carries this license
   information:

     Created 9 February 2008 by Rustan Leino.
     Converted to Boogie 2 on 28 June 2008.
     Edited sequence axioms 20 October 2009 by Alex Summers.
     Modified 2014 by Dan Rosen.
     Copyright (c) 2008-2014, Microsoft.
     Copyright by the contributors to the Dafny Project
     SPDX-License-Identifier: MIT
*)

(**
This module brings properties about finite sets ambiently into the
context.  The properties are modeled after those in the Dafny sequence
axioms, with patterns for quantifiers chosen as in those axioms.

@summary Puts properties of finite sets into the ambient context
*)
module FStar.FiniteSet.Ambient

open FStar.FiniteSet.Base

(*| Makes every fact of `FStar.FiniteSet.Base.all_finite_set_facts` hold in
    the SMT context of every module that depends on
    `FStar.FiniteSet.Ambient`.

    It is a top-level proof of `squash all_finite_set_facts`, obtained from
    `FStar.FiniteSet.Base.all_finite_set_facts_lemma`. The SMT encoding of a
    top-level definition records its type, so the facts are assumed in every
    later query; nothing needs to be called.

    ```fstar
    open FStar.FiniteSet.Ambient
    let singleton_has_its_element (x: int)
      : Lemma (FStar.FiniteSet.Base.mem x (FStar.FiniteSet.Base.singleton x))
      = ()
    ```

    To use the facts only in a few proofs, call
    `FStar.FiniteSet.Base.all_finite_set_facts_lemma` instead. *)
let all_finite_set_facts_ambient : (squash all_finite_set_facts) =
  all_finite_set_facts_lemma ()

