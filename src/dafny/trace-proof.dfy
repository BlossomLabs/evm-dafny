// SPDX-License-Identifier: Apache-2.0
include "execution.dfy"

module ExecutionTraceProof {
  import opened EvmState
  import EVM
  import Execution

  ghost predicate Valid(states: seq<State>)
  {
    |states| >= 1 &&
    (forall i | 0 <= i < |states|-1 ::
       states[i].EXECUTING? && EVM.Execute(states[i]) == states[i+1])
  }

  lemma Replay(states: seq<State>, fuel: nat, pcs: seq<nat> := [])
    requires Valid(states)
    requires !states[|states|-1].EXECUTING?
    requires fuel >= |states|-1
    ensures Execution.Run(states[0],fuel,pcs).state == states[|states|-1]
    decreases |states|
  {
    reveal Execution.Run();
    if |states| > 1 {
      assert states[1..][|states|-2] == states[|states|-1];
      assert Valid(states[1..]);
      assert EVM.Execute(states[0]) == states[1];
      Replay(states[1..],fuel-1,pcs+[states[0].PC()]);
    }
  }
}
