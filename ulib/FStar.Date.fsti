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

module FStar.Date

/// A module providing primitives for dates and times
(*| An abstract type of points in time. A primitive with no equality and no specification. *)
new
val dateTime:Type0
(*| An abstract type of durations. A primitive with no equality and no specification. *)
new
val timeSpan:Type0

(*| Returns the current date and time.

    `EXT` effect, which marks an external system call: impure, with no
    observable effect on the state. Nothing is specified about the result. *)
val now: unit -> EXT dateTime
(*| Returns the current time as a number of seconds since a fixed origin.

    `EXT` effect, which marks an external system call. Only the bound
    `n < pow2 32` is specified; the origin is left to the realization. *)
val secondsFromDawn: unit -> EXT (n: nat{n < pow2 32})
(*| Builds a duration from four integer components.

    The interface does not name the components; by analogy with .NET's
    `TimeSpan(days, hours, minutes, seconds)` they are presumably days, hours,
    minutes and seconds. An assumed primitive with no specification. *)
val newTimeSpan: int -> int -> int -> int -> Tot timeSpan
(*| Adds a duration to a point in time. An assumed primitive with no specification. *)
val addTimeSpan: dateTime -> timeSpan -> Tot dateTime
(*| Tests whether the first point in time is strictly later than the second. An assumed primitive with no specification. *)
val greaterDateTime: dateTime -> dateTime -> Tot bool

