module FStar.Issue
open FStar.Range

module Pprint = FStar.Pprint

(*| The abstract type of diagnostics (errors, warnings and information messages) reported by the compiler.

    Build one with `FStar.Issue.mk_issue` or `FStar.Issue.mk_issue_doc` and
    inspect it with accessors such as `FStar.Issue.message_of_issue`. It is
    realized by the compiler's own issue type, so tactics can create, collect
    and inspect diagnostics. *)
new
val issue : Type0

(*| The severity of an issue, as one of the strings `"Info"`, `"Warning"`, `"Error"` or `"Feature not yet implemented: "`. *)
let issue_level_string = s:string {
  s == "Info" \/
  s == "Warning" \/
  s == "Error" \/
  s == "Feature not yet implemented: "
}

(*| Returns the message of an issue, as a list of documents. An assumed primitive. *)
val message_of_issue (i:issue) : Tot (list Pprint.document)

(*| Returns the severity of an issue. An assumed primitive. *)
val level_of_issue (i:issue) : Tot issue_level_string

(*| Returns the error number of an issue, or `None` if it has none. An assumed primitive. *)
val number_of_issue (i:issue) : Tot (option int)

(*| Returns the source range of an issue, or `None` if it has none. An assumed primitive. *)
val range_of_issue (i:issue) : Tot (option range)

(*| Returns the context lines of an issue, which describe where it was raised. An assumed primitive. *)
val context_of_issue (i:issue) : Tot (list string)

(*| Formats an issue, with its header and message, as a document. An assumed primitive. *)
val issue_to_doc (i:issue) : Tot Pprint.document

(*| Formats an issue, with its header and message, as a string. An assumed primitive. *)
val render_issue (i:issue) : Tot string

(* NOTE: the only way to build a document that actually reduces
in interpreted mode (like in tactics when not using plugins)
is using arbitrary_string, as below. *)
(*| Builds an issue from a severity, a message given as documents, an optional range, an optional error number and a list of context lines.

    An assumed primitive; nothing relates the result to the accessors such as
    `FStar.Issue.message_of_issue`. See `FStar.Issue.mk_issue` for a string
    message. *)
val mk_issue_doc (i:issue_level_string)
             (msg:list Pprint.document)
             (range:option range)
             (number:option int)
             (ctx:list string)
  : Tot issue

(* These qualifiers here to make sure that karamel (while building
krmllib) does not attempt to extract this definition, as that would fail
since it does not have an implementation of arbitrary_string. We could
also not extract this module altogether. *)
(*| Builds an issue from a severity, a message string, an optional range, an optional error number and a list of context lines.

    It is `FStar.Issue.mk_issue_doc` with the message wrapped by
    `FStar.Pprint.arbitrary_string`, which also reduces in interpreted mode (for
    example in tactics run without plugins). It is `noextract`. *)
noextract
inline_for_extraction
let mk_issue (i:issue_level_string)
             (msg:string)
             (range:option range)
             (number:option int)
             (ctx:list string)
  = mk_issue_doc i [Pprint.arbitrary_string msg] range number ctx
