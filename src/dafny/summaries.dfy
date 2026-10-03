include "evm.dfy"
module InstructionSteps {
  import opened EvmState
  import EVM
  import Opcode
  import Bytecode
  import Stack
  import U256
  import opened Int
  lemma JumpDestStep(st:ExecutingState)
    requires st.PC() < |st.evm.code.contents|
    requires st.evm.code.contents[st.PC()] == Opcode.JUMPDEST
    requires Opcode.JUMPDEST in st.evm.fork.bytecodes
    requires st.Gas() >= 1
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-1))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); }
  lemma AddStep(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents|
    requires st.evm.code.contents[st.PC()] == Opcode.ADD && Opcode.ADD in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,stack:=Stack.Make([U256.Add(st.Peek(0),st.Peek(1))]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Add(); }

  lemma PopStep(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents|
    requires st.evm.code.contents[st.PC()] == Opcode.POP && Opcode.POP in st.evm.fork.bytecodes
    requires st.Gas() >= 2 && st.Operands() >= 1
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-2,stack:=Stack.Make(st.evm.stack.contents[1..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Pop(); }

  lemma SwapStep(st: ExecutingState, k: nat)
    requires 1 <= k <= 16 && st.Operands() > k && st.Gas() >= 3
    requires st.PC() < |st.evm.code.contents|
    requires st.evm.code.contents[st.PC()] == (0x8f+k) as u8 && (0x8f+k) as u8 in st.evm.fork.bytecodes
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,stack:=Stack.Make(st.evm.stack.contents[0:=st.Peek(k)][k:=st.Peek(0)])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Swap(); }

  lemma JumpIfStep(st: ExecutingState)
    requires st.Operands() >= 2 && st.Gas() >= 10
    requires st.PC() < |st.evm.code.contents|
    requires st.evm.code.contents[st.PC()] == Opcode.JUMPI && Opcode.JUMPI in st.evm.fork.bytecodes
    requires st.Peek(1) == 0 || st.IsJumpDest(st.Peek(0))
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=(if st.Peek(1) == 0 then st.PC()+1 else st.Peek(0) as nat),gas:=st.Gas()-10,stack:=Stack.Make(st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.JumpI(); }

  lemma JumpStep(st: ExecutingState)
    requires st.Operands() >= 1 && st.Gas() >= 8
    requires st.PC() < |st.evm.code.contents|
    requires st.evm.code.contents[st.PC()] == Opcode.JUMP && Opcode.JUMP in st.evm.fork.bytecodes
    requires st.IsJumpDest(st.Peek(0))
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.Peek(0) as nat,gas:=st.Gas()-8,stack:=Stack.Make(st.evm.stack.contents[1..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Jump(); }

}
module ForkFacts {
  import EvmFork
  import Opcode
  lemma CancunMembership()
    ensures {Opcode.JUMPDEST,Opcode.PUSH0,Opcode.PUSH1,Opcode.PUSH2,Opcode.PUSH4,Opcode.SHL,Opcode.SUB,Opcode.MSTORE,Opcode.REVERT,Opcode.DUP1,Opcode.DUP2,Opcode.DUP3,Opcode.DUP4,Opcode.SWAP1,Opcode.SWAP2,Opcode.MLOAD,Opcode.LT,Opcode.ISZERO,Opcode.SHR,Opcode.JUMPI,Opcode.POP,Opcode.ADD,Opcode.JUMP} <= EvmFork.CANCUN.bytecodes
  { reveal EvmFork.CANCUN; reveal EvmFork.CANCUN_BYTECODES; reveal EvmFork.GENISIS_BYTECODES; EvmFork.EipSet(EvmFork.CANCUN_EIPS,EvmFork.GENISIS_BYTECODES); }
}

module JumpBoundaryRegression {
  import Code
  lemma RejectPushImmediate()
    ensures !Code.IsInstructionStart(Code.Create([0x60,0x5b,0x56,0x00]),0,1)
  { reveal Code.IsInstructionStart(); }
  lemma AcceptFollowingInstruction()
    ensures Code.IsInstructionStart(Code.Create([0x60,0x5b,0x5b]),0,2)
  { reveal Code.IsInstructionStart(); }
  lemma PushZeroDoesNotSkip()
    ensures Code.IsInstructionStart(Code.Create([0x5f,0x5b]),0,1)
  { reveal Code.IsInstructionStart(); }
  lemma TruncatedPushDoesNotCreateBoundary()
    ensures !Code.IsInstructionStart(Code.Create([0x7f,0x5b]),0,1)
  { reveal Code.IsInstructionStart(); }
}

module PushSummaries {
  import opened EvmState
  import opened Int
  import EVM
  import Bytecode
  import ByteUtils
  import Code
  import Arrays
  import Stack
  lemma PushOne(st:ExecutingState, value:u8)
    requires st.PC()+1 < |st.evm.code.contents|
    requires st.evm.code.contents[st.PC()] == 0x60
    requires st.evm.code.contents[st.PC()+1] == value
    requires 0x60 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Capacity() >= 1
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+2,gas:=st.Gas()-3,stack:=Stack.Make([value as u256]+st.evm.stack.contents)))
  {
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
    reveal Bytecode.Push(); reveal Code.Slice(); reveal Arrays.SliceAndPad();
    reveal ByteUtils.ConvertBytesTo256();
    assert Code.Slice(st.evm.code,st.PC()+1,1) == [value];
  }
  lemma PushTwo(st:ExecutingState, hi:u8, lo:u8)
    requires st.PC()+2 < |st.evm.code.contents|
    requires st.evm.code.contents[st.PC()] == 0x61
    requires st.evm.code.contents[st.PC()+1] == hi && st.evm.code.contents[st.PC()+2] == lo
    requires 0x61 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Capacity() >= 1
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+3,gas:=st.Gas()-3,stack:=Stack.Make([(hi as u256)*256+(lo as u256)]+st.evm.stack.contents)))
  {
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
    reveal Bytecode.Push(); reveal Code.Slice(); reveal Arrays.SliceAndPad();
    reveal ByteUtils.ConvertBytesTo256(); reveal ByteUtils.ReadUint16();
    assert Code.Slice(st.evm.code,st.PC()+1,2) == [hi,lo];
  }
}

module ShiftSummaries {
  import opened EvmState
  import EVM
  import Bytecode
  import Stack
  import opened Int
  import MathUtils = EvmArithmetic
  import U256
  lemma Power160()
    ensures MathUtils.Pow(2,160) == 0x10000000000000000000000000000000000000000
  {
    assert MathUtils.Pow(2,1) == 2;
    assert MathUtils.Pow(2,2) == 4;
    assert MathUtils.Pow(2,5) == 32;
    assert MathUtils.Pow(2,10) == 1024;
    assert MathUtils.Pow(2,20) == 1048576;
    assert MathUtils.Pow(2,40) == 1099511627776;
    assert MathUtils.Pow(2,80) == 1208925819614629174706176;
    assert MathUtils.Pow(2,160) == 1461501637330902918203684832716283019655932542976;
  }
  lemma Below160(word:u256)
    requires word < 0x10000000000000000000000000000000000000000
    ensures U256.Shr(word,160) == 0
  { Power160(); reveal U256.Shr(); }
  lemma ExecuteBelow160(st:ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0x1c
    requires 0x1c in st.evm.fork.bytecodes
    requires st.Operands() >= 2 && st.Gas() >= 3
    requires st.Peek(0) == 160 && st.Peek(1) < 0x10000000000000000000000000000000000000000
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,stack:=Stack.Make([0 as u256]+st.evm.stack.contents[2..])))
  {
    Below160(st.Peek(1));
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
    reveal Bytecode.Shr();
  }

}

module LoadSummaries {
  import opened EvmState
  import EVM
  import Bytecode
  import Memory
  import Stack
  import Gas
  lemma Fits(st:ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0x51
    requires 0x51 in st.evm.fork.bytecodes
    requires st.Operands() >= 1 && st.Gas() >= 3
    requires (st.Peek(0) as nat)+32 <= |st.evm.memory.contents|
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,stack:=Stack.Make([st.Read(st.Peek(0) as nat)]+st.evm.stack.contents[1..])))
  {
    reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode();
    reveal Bytecode.MLoad(); reveal Memory.ExpandMem(); reveal Memory.Expand();
    reveal Gas.CostExpandBytes(); reveal Gas.ExpansionSize();
  }
}
