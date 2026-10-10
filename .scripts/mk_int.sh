#!/usr/bin/env bash

set -eu

D=$(dirname $0)
ULIB=$D/../ulib

function err () {
	echo "Generating the int files failed."
	echo "Please note this must be run in the ulib/ directory"
}

trap err ERR

## Write FStar.Int<N>.fsti

for i in 8 16 32 64 128; do
  f=$ULIB/FStar.Int$i.fsti
  cat > $f <<EOF
(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.Int$i

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

(*| The bit width of \`t\`.

    Values of \`t\` are two's complement integers ranging from \`FStar.Int.min_int n\` to \`FStar.Int.max_int n\`. *)
unfold let n = $i

EOF
  cat $D/FStar.IntN.fstip >> $f
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

(*| Full product of two signed 64-bit integers as a signed 128-bit integer: \`v (mul_wide a b) == FStar.Int64.v a * FStar.Int64.v b\`.

    No precondition: the product of two signed 64-bit values always fits in 128 bits. The implementation assumes this bound rather than proving it. *)
val mul_wide: a:Int64.t -> b:Int64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = Int64.v a * Int64.v b))
EOF
  fi
done


##Write FStar.Int<N>.fst

for i in 8 16 32 64 128; do
  f=$ULIB/FStar.Int$i.fst
  cat > $f <<EOF
(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.Int$i

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

EOF
  cat $D/FStar.IntN.fstp >> $f
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

let mul_wide a b = 
  assume (size (Int64.v a * Int64.v b) n);
  Mk ((Int64.v a) * (Int64.v b))
EOF
  fi
done

##Write FStar.UInt<N>.fsti

for i in 8 16 32 64; do
  f=$ULIB/FStar.UInt$i.fsti
  cat > $f <<EOF
(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.UInt$i

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

(*| The bit width of \`t\`.

    Values of \`t\` range from \`0\` to \`pow2 n - 1\`. *)
unfold let n = $i

EOF
  cat $D/FStar.UIntN.fstip >> $f
  if [ $i -eq 8 ]; then
    echo >> $f
    echo '(*| An abbreviation for `t`, the unsigned 8-bit machine integer type, conventionally used for bytes. *)' >> $f
    echo "unfold inline_for_extraction type byte = t" >> $f
  fi
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

val mul_wide: a:UInt64.t -> b:UInt64.t -> Pure t
  (requires True)
  (ensures (fun c -> v c = UInt64.v a * UInt64.v b))
EOF
  fi
done


##Write FStar.UInt<N>.fst

for i in 8 16 32 64; do
  f=$ULIB/FStar.UInt$i.fst
  cat > $f <<EOF
(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.UInt$i

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

EOF
  cat $D/FStar.UIntN.fstp >> $f
  if [ $i -eq 128 ]; then
      cat >> $f <<EOF

let mul_wide a b = 
  assume (size (UInt64.v a * UInt64.v b) n);
  Mk ((UInt64.v a) * (UInt64.v b))
EOF
  fi
done

# Remove self-references.
sed -i 's/UInt32.//g' $ULIB/FStar.UInt32.fsti
sed -i 's/UInt32.//g' $ULIB/FStar.UInt32.fst
