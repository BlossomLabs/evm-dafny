/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
include "../util/int.dfy"
include "../util/arrays.dfy"
include "../../../libs/DafnyCrypto/src/dafny/util/option.dfy"

// Backend values are explicit environmental inputs, with no crypto postulates.
module Precompiled {
  import opened Int
  import opened Optional
  import opened Arrays
  type CallFn = (u160,Array<u8>) -> Option<(Array<u8>,nat)>
  type Sha3Fn = Array<u8> -> u256
  datatype T = Dispatcher(call: CallFn, sha3: Sha3Fn) {
    opaque function Call(address: u160, data: Array<u8>): Option<(Array<u8>,nat)> { call(address,data) }
    opaque function Sha3(data: Array<u8>): u256 { sha3(data) }
  }
  // Only a subset-type witness. Executable constructors require a backend.
  const WITNESS: T := Dispatcher((address,data) => None, data => 0)
}
