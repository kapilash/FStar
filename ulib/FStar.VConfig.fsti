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
module FStar.VConfig

(*| The verification-relevant options used to check a particular definition.

    Each field holds the value of the corresponding command-line option, such
    as `initial_fuel`, `max_ifuel`, `z3rlimit`, `z3seed` or `no_smt`. Tactics
    can read the configuration of a definition with
    `FStar.Stubs.Reflection.V2.Builtins.sigelt_opts`, and the
    `FStar.VConfig.check_with` attribute checks a definition with a given
    configuration. Equality is decidable. *)
type vconfig = {
  initial_fuel                              : int;
  max_fuel                                  : int;
  initial_ifuel                             : int;
  max_ifuel                                 : int;
  no_smt                                    : bool;
  quake_lo                                  : int;
  quake_hi                                  : int;
  quake_keep                                : bool;
  retry                                     : bool;
  smtencoding_elim_box                      : bool;
  smtencoding_nl_arith_repr                 : string;
  smtencoding_l_arith_repr                  : string;
  tcnorm                                    : bool;
  no_plugins                                : bool;
  no_tactics                                : bool;
  z3cliopt                                  : list string;
  z3smtopt                                  : list string;  
  z3refresh                                 : bool;
  z3rlimit                                  : int;
  z3rlimit_factor                           : int;
  z3seed                                    : int;
  z3version                                 : string;
  trivial_pre_for_unannotated_effectful_fns : bool;
}

(*| An attribute that checks the annotated definition with the given `FStar.VConfig.vconfig`.

    It is usually produced by tactics, for example with
    `FStar.Reflection.V2.Derived.add_check_with`. The function itself does
    nothing and is `irreducible`. *)
irreducible
let check_with (vcfg : vconfig) : unit = ()
