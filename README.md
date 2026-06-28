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
core/   EVM primitive types
evm/    Stack, memory, opcodes and EVM execution logic
```

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
