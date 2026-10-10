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

module FStar.Exn

(*| Raises the exception `e`.

    An assumed primitive in the `Exn` effect, implemented natively as the
    target's raise. Its postcondition is `False`, so it does not return normally
    and the result type is arbitrary. See also `FStar.All.failwith` and
    `FStar.All.try_with`. *)
assume
val raise (e: exn) : Exn 'a (ensures fun _ -> False)

