// SPDX-License-Identifier: Apache-2.0
include "evm.dfy"

// A bounded driver usable by any contract. EXECUTING at the fuel boundary is
// exhaustion of this driver, never a successful EVM outcome.
module Execution {
  import opened EvmState
  import EVM

  datatype Result = Result(state: State, pcs: seq<nat>)

  function {:tailrecursion true} Run(st: State, fuel: nat, pcs: seq<nat> := []): Result
    decreases fuel
  {
    if fuel == 0 || !st.EXECUTING? then Result(st,pcs)
    else Run(EVM.Execute(st),fuel-1,pcs+[st.PC()])
  }

  lemma Bound(st: State, fuel: nat, pcs: seq<nat>)
    ensures |pcs| <= |Run(st,fuel,pcs).pcs| <= |pcs|+fuel
    ensures Run(st,fuel,pcs).pcs[..|pcs|] == pcs
    ensures Run(st,fuel,pcs).state.EXECUTING? ==> |Run(st,fuel,pcs).pcs| == |pcs|+fuel
    decreases fuel
  {
    reveal Run();
    if fuel > 0 && st.EXECUTING? {
      Bound(EVM.Execute(st),fuel-1,pcs+[st.PC()]);
      assert (pcs+[st.PC()])[..|pcs|] == pcs;
    }
  }

  lemma Halted(st: State, fuel: nat, pcs: seq<nat>)
    requires !st.EXECUTING?
    ensures Run(st,fuel,pcs) == Result(st,pcs)
  { reveal Run(); }

  lemma ExecuteNCorrespondence(st: ExecutingState, fuel: nat, pcs: seq<nat>)
    requires fuel > 0
    ensures Run(st,fuel,pcs).state == EVM.ExecuteN(st,fuel)
    decreases fuel
  {
    reveal Run();
    reveal EVM.ExecuteN();
    var next := EVM.Execute(st);
    if fuel > 1 && next.EXECUTING? {
      ExecuteNCorrespondence(next,fuel-1,pcs+[st.PC()]);
    } else {
      if !next.EXECUTING? { Halted(next,fuel-1,pcs+[st.PC()]); }
    }
  }
}
