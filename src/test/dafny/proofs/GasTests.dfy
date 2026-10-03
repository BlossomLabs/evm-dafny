include "../../../dafny/core/precompiled-crypto.dfy"
// Some tests related to gas.
include "../../../dafny/evm.dfy"

module GasTests {
    import opened Int
    import EVM
    import EvmFork
    import Bytecode
    import opened Opcode
    import Gas

     /** The gas loaded in the EVM before executing a program. */
    const INITGAS := 0xFFFF

    method test_01() {
        // Assuption required because Z3 cannot figure this out!
        assume {:axiom} {GAS} <= EvmFork.BERLIN_BYTECODES;
        // Simple contract containing only one instruction.
        var vm := EVM.Init(gas := INITGAS, code := [GAS], precompiled:=PrecompiledCrypto.Backend((data,v,r,s)=>data,data=>data,data=>data,data=>data,data=>0));
        vm := EVM.Execute(vm);
        // Sanity check output!
        assert vm.Peek(0) == ((INITGAS - Gas.G_BASE) as u256);
    }
}
