# stainless-evm

Formally verified EVM implementation targeting the [Osaka](https://eips.ethereum.org/EIPS/eip-7607) execution layer spec, written in Scala 3 with [Stainless](https://epfl-lara.github.io/stainless/).

## Requirements

- JDK 17+
- sbt 1.7+
- z3 or cvc5 for SMT solving: `brew install z3`

## Setup

The stainless compiler plugin jar (87 MB) is not committed. Download `sbt-stainless.zip` from the [stainless releases page](https://github.com/epfl-lara/stainless/releases) and extract it at the project root:

```
unzip sbt-stainless.zip
```

This populates `project/lib/sbt-stainless.jar` and `stainless/` (the local Maven repo). The zip itself can be deleted after extraction.

## Build and verify

```
sbt compile         # verify and compile the whole tree
sbt test            # run the unit tests
```

To verify only a subset of functions during iteration, use Stainless function filtering, for example:

```
sbt "set every stainlessExtraOptions ++= Seq(\"--functions=evm.value._\")" compile
```

Stainless verification runs automatically on every compile. Each function annotated with `require`/`ensuring` produces verification conditions that are discharged by the SMT solver. The summary at the end of compilation shows valid/invalid/unknown counts.

To skip verification temporarily:

```
sbt "set every stainlessEnabled := false" compile
```

## Running bytecode (CLI)

The `cli` project is an unverified shell over the verified core (it depends on the
core as compiled bytecode, so Stainless never sees it). It executes raw bytecode
through the verified `Interpreter.run` and prints the outcome.

```
sbt "cli/run run <hex> [--gas N] [--calldata HEX] [--value N]"
```

For example, bytecode that stores 42 in memory and returns it:

```
sbt "cli/run run 602a60005260206000f3"
```
```
status:    Halted
gas used:  18
return:    0x000000000000000000000000000000000000000000000000000000000000002a
logs:      0
```

`--gas` sets the gas limit (default 1,000,000), `--calldata` supplies input bytes
(hex), and `--value` sets the call value in wei.

The `tx` command runs a full transaction through `Transaction.run`: it deploys the
given code at the recipient, funds the sender, and applies the whole intrinsic gas,
EIP-1559 fee, nonce, value-transfer, and settlement path. It prints the settlement
and the before/after balances and nonces.

```
sbt "cli/run tx 00 --value 100 --maxfee 10 --priorityfee 2 --basefee 5 --gas 30000"
```
```
status:       Halted
gas used:     21000
gas refunded: 0
return:       0x (empty)
logs:         0

sender    0x0000000000000000000000000000000000000001  balance 1000000000000000000 -> 999999999999852900  nonce 0 -> 1
recipient 0x0000000000000000000000000000000000001000  balance 0 -> 100
coinbase  0x0000000000000000000000000000000000002000  balance 0 -> 42000
```

Here the sender pays `21000 * 7 + 100` (gas at the effective price of 7 plus the
value), the recipient receives the value, and the coinbase receives the priority
tip of `21000 * 2`. Flags: `--from`/`--to`/`--coinbase` (hex addresses),
`--balance` (sender funds, default 1e18), and `--maxfee`/`--priorityfee`/`--basefee`
/`--nonce`. With the fee flags left at their zero defaults, gas is free.

The `disasm` command prints bytecode as opcodes with their offsets and immediates:

```
sbt "cli/run disasm 602a60005260206000f3"
```
```
0x0000  PUSH1         0x2a
0x0002  PUSH1         0x00
0x0004  MSTORE
0x0005  PUSH1         0x20
0x0007  PUSH1         0x00
0x0009  RETURN
```

The `repl` command starts an interactive session against a single contract whose
storage persists across lines, so state written by one snippet is visible to the
next:

```
sbt "cli/run repl"
```
```
evm> 602a600055                        # SSTORE slot 0 = 0x2a
  status Halted   gas used 22106   return 0x (empty)   logs 0
evm> 60005460005260206000f3            # SLOAD slot 0, MSTORE, RETURN
  status Halted   gas used 2118   return 0x000000000000000000000000000000000000000000000000000000000000002a
evm> :q
```

Inside the REPL, `:disasm <hex>`, `:gas N`, `:reset`, `:help`, and `:q` are
available.

`sbt "cli/run help"` prints usage. Running the CLI recompiles the core dependency,
so Stainless re-verifies it (cached).

## Project structure

The verified core is a single sbt project (one verification unit, one target).
Since every verified type cross-references the others (Word256 uses EvmMath, the
interpreter uses everything), Stainless requires them in one compilation unit
anyway, so the code is organized by package rather than by sbt module. The only
separate project is the `cli` shell, which is deliberately unverified and depends
on the core as compiled bytecode.

```
src/main/scala/evm/
  math/    the pure-math and proof layer (no EVM-type references)
    EvmMath.scala              Number theory: modulus, exponentiation, byte length, signed interpretation, bounds, and their lemmas (including the division/modulo scaffold for the digit law)
    Bitwise.scala              Bitwise and/or/xor as trusted @extern functions with assumed algebraic axioms; not is verified
    Collections.scala          Generic List/Map lemmas (for example updated preserves other indices)
    Bytes.scala                Byte-array packing over Map: readBytes/writeBytes/copyBytes plus framing and round-trip lemmas
    ByteList.scala             Big-endian reads over a byte list (the calldata model), with the readWord per-byte digit law proven
    Gas.scala                  Pure gas pricing formulas (memory expansion, copy, keccak, exp, log, access, sstore) with non-negativity lemmas
  value/   primitive value types
    Word256.scala              The 256-bit EVM word with verified arithmetic, bitwise, shift, signed, and comparison operations
    Keccak256.scala            Keccak-256 as a trusted @extern primitive (a real executable implementation, treated as a black box by the verifier)
  state/   the mutable machine state
    Stack.scala                The 1024-item EVM stack (push, pop, peek, dup, swap), verified to respect the depth bound
    Memory.scala               Byte-addressable EVM memory (load, store, store8, mcopy, msize, expand), with proven write/read round-trips
    Storage.scala              Persistent/transient key-value store (load, store) for SLOAD/SSTORE and TLOAD/TSTORE
  code/    the bytecode layer
    Opcode.scala               Opcode enum (all ~150 opcodes with hex and descriptions), hex/decode and per-opcode base gas
    Code.scala                 Bytecode wrapper: byte/opcode access, verified JUMPDEST analysis, and PUSH immediate reading into a Word256
  env/     the execution environment (kept in its own package to avoid the Address/ADDRESS case collision)
    Address.scala              The 160-bit account address type
    CreateAddress.scala        Trusted @extern derivation of CREATE (RLP) and CREATE2 addresses, keccak-hashed like the primitive it wraps
    Context.scala              Block (with block hashes), transaction (with blob hashes), and message context records
    WorldState.scala           Accounts (balance, code, storage, nonce) keyed by address, with default-zero lookups, value transfer, and balance/storage/nonce updates proven to preserve the other fields
    Log.scala                  An emitted log record: address, topics, and data bytes
  exec/    the machine
    ExecState.scala            Execution state: stack, memory, storage, transient, pc, gas, depth, static flag, status, return data, block/tx/message/world context, accessed sets, the created-this-tx set (EIP-6780), logs and the refund counter
    Transaction.scala          The transaction layer: intrinsic gas + EIP-7623 calldata floor, EIP-1559 fees (effective gas price from base fee and priority tip, upfront debit, unused-gas refund to the sender, tip to the coinbase), EIP-2930 access lists (pre-warming), the EIP-7825 gas cap, creation transactions (53000 intrinsic + EIP-3860 initcode cost, deploy at the derived address), nonce check and increment, top-level entry (run), and settlement with the EIP-3529 capped refund
    Interpreter.scala          The step/run dispatch loop (with recursive call frames CALL/CALLCODE/DELEGATECALL/STATICCALL, CREATE/CREATE2 initcode frames, value transfer, and SELFDESTRUCT, proven-terminating): arithmetic, comparison, bitwise, shift, PUSH/DUP/SWAP/POP, memory (MLOAD/MSTORE/MSTORE8/MSIZE/MCOPY) with expansion and EXP dynamic gas, the read-only environment ops (ADDRESS, CALLER, CALLVALUE, ORIGIN, block/tx fields, SELFBALANCE, CODESIZE, PC, GAS), world reads with account cold/warm (BALANCE, EXTCODESIZE, EXTCODEHASH, EXTCODECOPY), BLOCKHASH/BLOBHASH, storage (SLOAD/SSTORE with cold/warm and the EIP-2200 charge, TLOAD/TSTORE), control flow (JUMP/JUMPI against verified JUMPDEST analysis, RETURN, REVERT), the calldata/code copy ops (CALLDATALOAD, CALLDATACOPY, CODECOPY, RETURNDATASIZE, RETURNDATACOPY), KECCAK256 (via the trusted keccak primitive, with per-word gas), and LOG0-4 (emitting to a log accumulator); proven-terminating run
src/test/scala/evm/            munit unit tests, one suite per type (Word256, Stack, Memory, Storage, Gas, Opcode, Code, ExecState, Interpreter, Context)
cli/src/main/scala/evm/cli/    unverified CLI shell (Main.scala) over the verified core; a second sbt project with no Stainless plugin
build.sbt                      Two projects: the verified core (Stainless runs on every compile) and the cli shell that depends on it via bytecode
.github/workflows/verify.yml   CI: one job that verifies the whole tree and runs the unit tests
```

## Verification approach: lemmas and axioms

Each function carries its specification inline as `require` (preconditions) and `ensuring` (postconditions). Stainless turns these into verification conditions handled by the SMT solver. The solver knows nothing about a function beyond its literal definition and will not discover non-trivial facts on its own, so when it gets stuck (`unknown`) we give it the missing fact in one of two forms, both live in the `evm.math` package and are invoked from the EVM code as needed.

### Lemmas: proven facts

A lemma is an ordinary recursive `Boolean` function whose recursion is an
inductive proof. Stainless verifies it and checks it terminates so it cannot be wrong. Example: the SMT
solver cannot show `pow(2, n) > 0` for all `n` (that needs induction), so we
prove it once and reuse it.

```scala
@ghost
def powTwoPos(n: BigInt): Boolean = {
  require(n >= 0)
  decreases(n)                       // proves the proof terminates
  pow(BigInt(2), n) > 0 because {
    if (n == 0) trivial              // base case
    else powTwoPos(n - 1)            // inductive step
  }
}.holds
```

`@ghost` means it is erased from the compiled bytecode (zero runtime cost).
`Word256.>>` calls `powTwoPos(shift)` so the solver knows the divisor is nonzero.

### Axioms: trusted facts

Some facts cannot be proven at all because they fall outside Stainless's logic. Bitwise `&`, `|`, `^` on `BigInt` have no theory, so `Bitwise.and`/`or`/`xor` are `@extern`. As a workaround solution we state their true properties as **axioms**: an `@extern` function whose `ensuring` is assumed rather than proven. We use this instead of the built-in `assume(...)` construct because it allows assumption naming, reusabilitiy and centralizes them in one place. Example, "OR of two 256-bit values is still a 256-bit value":

```scala
@extern
def orBound(a: BigInt, b: BigInt): Unit = {
  require(a >= 0 && a < MODULO && b >= 0 && b < MODULO)
  ()                                 
}.ensuring(_ => or(a, b) >= 0 && or(a, b) < MODULO && or(a, b) >= a && or(a, b) >= b)
```

On an `@extern` function `ensuring` goes from "must prove" to "may assume", which is what turns a postcondition into an axiom. `Word256.|` calls `orBound` to add these assumptions.

These axioms are the project's **trusted base**: if one is false, the whole proof becomes unsound. They are kept to a minimum, used only where Stainless genuinely cannot reason (like bitwise ops), and every one is true of 256-bit two's-complement integers. They are all collected in `Bitwise` so the trusted surface is auditable in one place. Where a "bitwise" op is actually plain arithmetic (`not(a) == MAX_VALUE - a`) it is a real verified function, not an axiom.

## Scala and Stainless references

- [Stainless documentation](https://epfl-lara.github.io/stainless/)
- [Pure Scala subset supported by Stainless](https://epfl-lara.github.io/stainless/purescala.html)
- [Specifications (require/ensuring/assert)](https://epfl-lara.github.io/stainless/specification.html)
- [Scala 3 documentation](https://docs.scala-lang.org/scala3/)
- [sbt documentation](https://www.scala-sbt.org/1.x/docs/)

## EVM reference

- [Ethereum Yellow Paper](https://ethereum.github.io/yellowpaper/paper.pdf)
- [EVM opcodes reference](https://www.evm.codes/)
- [Osaka/Fusaka EIPs (EIP-7607)](https://eips.ethereum.org/EIPS/eip-7607)
- [EVM From Scratch](https://www.evm-from-scratch.app/)
