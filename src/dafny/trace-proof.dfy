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

  lemma Append(states: seq<State>, next: State)
    requires Valid(states)
    requires states[|states|-1].EXECUTING?
    requires EVM.Execute(states[|states|-1]) == next
    ensures Valid(states+[next])
  {
    forall i | 0 <= i < |states|
      ensures (states+[next])[i].EXECUTING? &&
              EVM.Execute((states+[next])[i]) == (states+[next])[i+1]
    {
      if i < |states|-1 {
        assert states[i].EXECUTING? && EVM.Execute(states[i]) == states[i+1];
      } else {
        assert i == |states|-1;
      }
    }
  }

  lemma Join(left: seq<State>, right: seq<State>)
    requires Valid(left) && Valid(right)
    requires left[|left|-1] == right[0]
    ensures Valid(left+right[1..])
  {
    forall i | 0 <= i < |left|+|right|-2
      ensures (left+right[1..])[i].EXECUTING? &&
              EVM.Execute((left+right[1..])[i]) == (left+right[1..])[i+1]
    {
      if i < |left|-1 {
        assert left[i].EXECUTING? && EVM.Execute(left[i]) == left[i+1];
      } else {
        var j := i-(|left|-1);
        assert 0 <= j < |right|-1;
        assert (left+right[1..])[i] == right[j];
        assert (left+right[1..])[i+1] == right[j+1];
        assert right[j].EXECUTING? && EVM.Execute(right[j]) == right[j+1];
      }
    }
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
