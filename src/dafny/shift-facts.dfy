// SPDX-License-Identifier: Apache-2.0
include "util/int.dfy"

module ShiftFacts {
  import opened Int
  import U256
  import EvmArithmetic
  const Power224: int := 26959946667150639794667015087019630673637144422540572481103610249216

  lemma {:fuel EvmArithmetic.Pow, 12} Power()
    ensures EvmArithmetic.Pow(2,224) == Power224
  {}

  lemma HighFourBytes(word: u256, selector: u32, rest: nat)
    requires rest < Power224
    requires word as int == selector as int * Power224 + rest
    ensures U256.Shr(word,224) == selector as u256
  {
    Power(); reveal U256.Shr();
    assert (selector as int * Power224 + rest) / Power224 == selector as int;
  }
}
