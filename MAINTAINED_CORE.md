# Maintained interpreter core

The clean execution closure takes explicit hash and precompile callbacks. It
places no correctness postconditions on these callbacks. Concrete cryptography
is an optional adapter in `src/dafny/core/precompiled-crypto.dfy`; that adapter,
`t8n.dfy`, and legacy example proof debt are outside clean-core acceptance.
Java and optional-adapter compatibility remain separate gates.

`src/dafny/summaries.dfy` and `pure-steps.dfy` summarize actual `EVM.Execute`
steps, including gas deduction. `execution.dfy` provides bounded execution and
its equality with `EVM.ExecuteN`. `trace-proof.dfy` composes verified steps.
`boundaries.dfy` checks instruction-boundary certificates against the actual
PUSH-aware decoder. `checked-add.dfy` proves modular arithmetic and the unsigned
and signed overflow tests used by checked addition.

Selectors, contract offsets, compiler bindings, ABI specifications and public
claim evidence belong to consumers, including Assertions.

Run `python3 tools/bootstrap.py`, then
`python3 tools/verify_core.py --dafny .tools/dafny/dafny --output evidence/core`.
Evidence directories must be fresh. Verification checks the complete imported
closure with Dafny 4.11.0, Z3 4.12.1, two cores, isolated assertions and a
30-second limit per obligation; audit and formatting are separate required gates.
Generated evidence and installed tools are not committed.
