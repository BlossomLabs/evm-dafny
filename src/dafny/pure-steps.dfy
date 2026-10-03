// SPDX-License-Identifier: Apache-2.0
include "summaries.dfy"
module PureSteps {
  import opened EvmState
  import opened Int
  import EVM
  import Bytecode
  import Stack
  import U256
  import Word
  import Code
  import ByteUtils
  import Gas
  import Memory
  lemma Sub(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 3
    requires 3 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([(((st.Peek(0) as int) - (st.Peek(1) as int)) % TWO_256) as u256]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Sub(); }
  lemma Lt(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 16
    requires 16 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([(if st.Peek(0) < st.Peek(1) then 1 else 0)]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Lt(); }
  lemma Gt(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 17
    requires 17 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([(if st.Peek(0) > st.Peek(1) then 1 else 0)]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Gt(); }
  lemma SLt(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 18
    requires 18 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([(if Word.asI256(st.Peek(0)) < Word.asI256(st.Peek(1)) then 1 else 0)]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.SLt(); }
  lemma Eq(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 20
    requires 20 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([(if st.Peek(0) == st.Peek(1) then 1 else 0)]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Eq(); }
  lemma IsZero(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 21
    requires 21 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 1
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([(if st.Peek(0) == 0 then 1 else 0)]+st.evm.stack.contents[1..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.IsZero(); }
  lemma BooleanAnd(a: u256, b: u256)
    requires a <= 1 && b <= 1
    ensures U256.And((a as bv256) as u256, (b as bv256) as u256) == (if a == 1 && b == 1 then 1 else 0)
  {
    reveal U256.And();
    if a == 0 {
      assert a as bv256 == 0;
      if b == 0 { assert b as bv256 == 0; assert U256.And(0,0) == 0; }
      else { assert b == 1; assert b as bv256 == 1; assert U256.And(0,1) == 0; }
    } else {
      assert a == 1; assert a as bv256 == 1;
      if b == 0 { assert b as bv256 == 0; assert U256.And(1,0) == 0; }
      else { assert b == 1; assert b as bv256 == 1; assert U256.And(1,1) == 1; }
    }
  }
  lemma And(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 22
    requires 22 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    requires st.Peek(0) <= 1 && st.Peek(1) <= 1
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([(if st.Peek(0) == 1 && st.Peek(1) == 1 then 1 else 0)]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.And(); BooleanAnd(st.Peek(0),st.Peek(1));
    if st.Peek(0) == 0 {} else { assert st.Peek(0) == 1; }
    if st.Peek(1) == 0 {} else { assert st.Peek(1) == 1; }
  }
  lemma BooleanOr(a: u256, b: u256)
    requires a <= 1 && b <= 1
    ensures U256.Or((a as bv256) as u256, (b as bv256) as u256) == (if a == 1 || b == 1 then 1 else 0)
  {
    reveal U256.Or();
    if a == 0 {
      assert a as bv256 == 0;
      if b == 0 { assert b as bv256 == 0; assert U256.Or(0,0) == 0; }
      else { assert b == 1; assert b as bv256 == 1; assert U256.Or(0,1) == 1; }
    } else {
      assert a == 1; assert a as bv256 == 1;
      if b == 0 { assert b as bv256 == 0; assert U256.Or(1,0) == 1; }
      else { assert b == 1; assert b as bv256 == 1; assert U256.Or(1,1) == 1; }
    }
  }
  lemma Or(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 23
    requires 23 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    requires st.Peek(0) <= 1 && st.Peek(1) <= 1
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([(if st.Peek(0) == 1 || st.Peek(1) == 1 then 1 else 0)]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Or(); BooleanOr(st.Peek(0),st.Peek(1));
    if st.Peek(0) == 0 {} else { assert st.Peek(0) == 1; }
    if st.Peek(1) == 0 {} else { assert st.Peek(1) == 1; }
  }
  lemma Shl(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 27
    requires 27 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([U256.Shl(st.Peek(1),st.Peek(0))]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Shl(); }
  lemma Shr(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 28
    requires 28 in st.evm.fork.bytecodes
    requires st.Gas() >= 3 && st.Operands() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1, gas:=st.Gas()-3,
                                         stack:=Stack.Make([U256.Shr(st.Peek(1),st.Peek(0))]+st.evm.stack.contents[2..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Shr(); }

  lemma Dup(st: ExecutingState, k: nat)
    requires 1 <= k <= 16 && st.Operands() >= k && st.Capacity() >= 1 && st.Gas() >= 3
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == (0x7f+k) as u8
    requires (0x7f+k) as u8 in st.evm.fork.bytecodes
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,
                                         stack:=Stack.Make([st.Peek(k-1)]+st.evm.stack.contents)))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Dup(); }

  lemma PushZero(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0x5f
    requires 0x5f in st.evm.fork.bytecodes && st.Capacity() >= 1 && st.Gas() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-2,
                                         stack:=Stack.Make([0]+st.evm.stack.contents)))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Push0(); }

  lemma Push(st: ExecutingState, n: nat)
    requires 1 <= n <= 32 && st.Capacity() >= 1 && st.Gas() >= 3
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == (0x5f+n) as u8
    requires (0x5f+n) as u8 in st.evm.fork.bytecodes
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+n+1,gas:=st.Gas()-3,
                                         stack:=Stack.Make([ByteUtils.ConvertBytesTo256(Code.Slice(st.evm.code,st.PC()+1,n))]+st.evm.stack.contents)))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Push(); }

  lemma CallValue(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0x34
    requires 0x34 in st.evm.fork.bytecodes && st.Capacity() >= 1 && st.Gas() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-2,
                                         stack:=Stack.Make([st.evm.context.callValue]+st.evm.stack.contents)))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.CallValue(); }

  lemma CallDataSize(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0x36
    requires 0x36 in st.evm.fork.bytecodes && st.Capacity() >= 1 && st.Gas() >= 2
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-2,
                                         stack:=Stack.Make([st.evm.context.CallDataSize()]+st.evm.stack.contents)))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.CallDataSize(); }

  lemma CallDataLoad(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0x35
    requires 0x35 in st.evm.fork.bytecodes && st.Operands() >= 1 && st.Gas() >= 3
    ensures EVM.Execute(st) == EXECUTING(st.evm.(pc:=st.PC()+1,gas:=st.Gas()-3,
                                         stack:=Stack.Make([if st.Peek(0) >= st.evm.context.CallDataSize() then 0
                                                                              else st.evm.context.CallDataRead(st.Peek(0))]+st.evm.stack.contents[1..])))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.CallDataLoad(); }

  lemma Store(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0x52
    requires 0x52 in st.evm.fork.bytecodes && st.Operands() >= 2
    requires st.Gas() >= 3+Gas.CostExpandBytes(st,2,0,32)
    ensures EVM.Execute(st) == st.UseGas(3+Gas.CostExpandBytes(st,2,0,32)).Expand(st.Peek(0) as nat,32).Pop(2).Write(st.Peek(0) as nat,st.Peek(1)).Next()
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.MStore(); }

  lemma Return(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0xf3
    requires 0xf3 in st.evm.fork.bytecodes && st.Operands() >= 2
    requires st.Gas() >= Gas.CostExpandRange(st,2,0,1)
    ensures EVM.Execute(st) == RETURNS(st.Gas()-Gas.CostExpandRange(st,2,0,1),
                                       Memory.Slice(st.evm.memory,st.Peek(0) as nat,st.Peek(1) as nat),st.evm.world,st.evm.transient,st.evm.substate)
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Return(); }

  lemma Revert(st: ExecutingState)
    requires st.PC() < |st.evm.code.contents| && st.evm.code.contents[st.PC()] == 0xfd
    requires 0xfd in st.evm.fork.bytecodes && st.Operands() >= 2
    requires st.Gas() >= Gas.CostExpandRange(st,2,0,1)
    ensures EVM.Execute(st) == ERROR(REVERTS,st.Gas()-Gas.CostExpandRange(st,2,0,1),
                                     Memory.Slice(st.evm.memory,st.Peek(0) as nat,st.Peek(1) as nat))
  { reveal EVM.Execute(); reveal EVM.DeductGas(); reveal EVM.ExecuteBytecode(); reveal Bytecode.Revert(); }
}
