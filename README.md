# stainless-evm

Formally verified EVM implementation targeting the Osaka execution layer spec, written in Scala 3 with [Stainless](https://epfl-lara.github.io/stainless/).

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
sbt core/compile    # verify and compile core 
sbt evm/compile     # verify and compile evm 
sbt compile         # both
```

Stainless verification runs automatically on every compile. Each function annotated with `require`/`ensuring` produces verification conditions that are discharged by the SMT solver. The summary at the end of compilation shows valid/invalid/unknown counts.

To skip verification temporarily:

```
sbt "set every stainlessEnabled := false" compile
```

## Project structure

```
proofs/src/main/scala/evm/proofs/   Pure helper functions and all @ghost lemmas, by subject (no EVM-type references)
  EvmMath.scala                Number theory: modulus, exponentiation, signed interpretation, bounds, and their lemmas
  Bitwise.scala                Bitwise and/or/xor as trusted @extern functions with assumed algebraic axioms; not is verified
  Collections.scala            Generic List/Map lemmas (for example updated preserves other indices)
  Bytes.scala                  Byte-array packing over Map: readBytes/writeBytes/copyBytes plus framing and round-trip lemmas
  Gas.scala                    Pure gas pricing formulas (memory expansion, copy, keccak, exp, log, access, sstore) with non-negativity lemmas
core/src/main/scala/evm/core/
  Word256.scala                The 256-bit EVM word with verified arithmetic, bitwise, shift, signed, and comparison operations
evm/src/main/scala/evm/
  Stack.scala                  The 1024-item EVM stack (push, pop, peek, dup, swap), verified to respect the depth bound
  Memory.scala                 Byte-addressable EVM memory (load, store, store8, mcopy, msize, expand), with proven write/read round-trips
  Storage.scala                Persistent/transient key-value store (load, store) for SLOAD/SSTORE and TLOAD/TSTORE
  Opcode.scala                 Opcode enum (all ~150 opcodes with hex and descriptions), hex/decode and per-opcode base gas
  Code.scala                   Bytecode wrapper: byte/opcode access, verified JUMPDEST analysis, and PUSH immediate reading into a Word256
  ExecState.scala              Execution state: stack, memory, storage, transient, pc, gas, depth, static flag, status, return data
  Interpreter.scala            The step/run dispatch loop (skeleton: STOP, PUSH1, POP, ADD, JUMPDEST), with a proven-terminating run
evm/src/test/scala/evm/
  core/Word256Suite.scala      munit unit tests for Word256
  StackSuite.scala             munit unit tests for Stack
  MemorySuite.scala            munit unit tests for Memory
  StorageSuite.scala           munit unit tests for Storage
  GasSuite.scala               munit unit tests for the gas formulas
  OpcodeSuite.scala            munit unit tests for opcode hex, base gas and decode
  CodeSuite.scala              munit unit tests for the bytecode wrapper
  ExecStateSuite.scala         munit unit tests for the execution state
  InterpreterSuite.scala       munit unit tests running bytecode through the interpreter
build.sbt                      Build and Stainless wiring; source roots keep each module one verification unit
.github/workflows/verify.yml   CI: one job that verifies the whole tree and runs the unit tests
```

## Verification approach: lemmas and axioms

Each function carries its specification inline as `require` (preconditions) and `ensuring` (postconditions). Stainless turns these into verification conditions handled by the SMT solver. The solver knows nothing about a function beyond its literal definition and will not discover non-trivial facts on its own, so when it gets stuck (`unknown`) we give it the missing fact in one of two forms, both live in `proofs/src` and are invoked from the EVM code as needed.

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
