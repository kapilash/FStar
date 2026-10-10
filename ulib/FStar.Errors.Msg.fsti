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
module FStar.Errors.Msg

(* Allows constructing structured pretty-printed error messages. *)

open FStar.Pprint

(*| A structured error message: a list of `FStar.Pprint.document`s rendered in order, one item per entry.

    The header (error number and source range) is added by the error reporter.
    For example, a message with three documents is printed as:

    ```text
    * Error 19 at tests/error-messages/Bug1997.fst(92,19-92,49):
      - Assertion failed
      - The SMT solver could not prove the query. Use --query_stats for more details.
      - Also see: Prims.fst(96,32-96,42)
    ```

    Empty documents (`FStar.Pprint.empty`) in the list are skipped. *)
type error_message = list document

(*| Turns a string of prose into a document, splitting it into words and formatting them as a paragraph.

    Any formatting in the string is lost. To include a pretty-printed term use
    `FStar.Stubs.Tactics.V2.Builtins.term_to_doc` or another document builder,
    or as a last resort `FStar.Pprint.doc_of_string`. An assumed primitive. *)
val text : string -> document

(*| Makes a single-document error message from a string, keeping its spacing and line breaks.

    `mkmsg s` is `[FStar.Pprint.doc_of_string s]`. For long prose use
    `FStar.Errors.Msg.text` instead; for structured content it is better to
    build a document directly than to lift a string. An assumed primitive. *)
val mkmsg : string -> error_message
