// SPDX-License-Identifier: Apache-2.0
include "core/code.dfy"

module InstructionBoundaries {
  import Code

  function Next(c: Code.T, pc: nat): nat
    requires pc < |c.contents|
  {
    var op := c.contents[pc];
    pc + 1 + (if 0x60 <= op <= 0x7f then (op as nat) - 0x5f else 0)
  }

  lemma Extend(c: Code.T, cursor: nat, boundary: nat)
    requires Code.IsInstructionStart(c, cursor, boundary)
    requires boundary < |c.contents|
    requires Next(c, boundary) < |c.contents|
    ensures Code.IsInstructionStart(c, cursor, Next(c, boundary))
    decreases boundary - cursor
  {
    reveal Code.IsInstructionStart();
    if cursor < boundary {
      Extend(c, Next(c, cursor), boundary);
    }
  }

  predicate Certificate(c: Code.T, pcs: seq<nat>)
  {
    |pcs| > 0 && pcs[0] == 0 &&
    (forall i | 0 <= i < |pcs| :: pcs[i] < |c.contents|) &&
    (forall i | 0 <= i < |pcs|-1 :: Next(c, pcs[i]) == pcs[i+1])
  }

  lemma Sound(c: Code.T, pcs: seq<nat>, index: nat)
    requires Certificate(c, pcs)
    requires index < |pcs|
    ensures Code.IsInstructionStart(c, 0, pcs[index])
    decreases index
  {
    reveal Code.IsInstructionStart();
    if index > 0 {
      Sound(c, pcs, index-1);
      assert Next(c, pcs[index-1]) == pcs[index];
      Extend(c, 0, pcs[index-1]);
    }
  }
}
