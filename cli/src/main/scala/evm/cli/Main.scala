package evm.cli

import stainless.collection.{List => SList, Nil => SNil, Cons}
import evm.value.Word256
import evm.code.Code
import evm.env.{Address, BlockContext, TxContext, MessageContext, WorldState}
import evm.exec.{ExecState, Interpreter}

// Unverified CLI over the verified EVM core. Parses arguments and hex bytecode,
// hands them to Interpreter.run, and prints the result. None of this file is
// verified: it depends on the core as compiled bytecode.
object Main:

  def main(args: Array[String]): Unit =
    if (args.isEmpty) { usage(); return }
    args(0) match
      case "run"  => run(args.drop(1))
      case "help" | "--help" | "-h" => usage()
      case other  => Console.err.println(s"unknown command: $other"); usage()

  private def usage(): Unit =
    println(
      """stainless-evm - run EVM bytecode over the verified core
        |
        |usage:
        |  run <hex> [--gas N] [--calldata HEX] [--value N]
        |      execute bytecode and print status, gas used, and return data
        |
        |example:
        |  run 602a60005260206000f3        # MSTORE 42, RETURN it (returns 0x..2a)""".stripMargin)

  private def run(args: Array[String]): Unit =
    if (args.isEmpty) { Console.err.println("run: expected bytecode hex"); return }
    val code = Code(parseHex(args(0)))
    val gas = flag(args, "--gas").map(BigInt(_)).getOrElse(BigInt(1000000))
    val callData = flag(args, "--calldata").map(parseHex).getOrElse(SNil[BigInt]())
    val value = flag(args, "--value").map(v => Word256(BigInt(v))).getOrElse(Word256.Zero)

    val msg = MessageContext(Address.zero, Address.zero, value, callData)
    val init = ExecState.initialWith(code, gas, BlockContext.empty, TxContext.empty, msg, WorldState.empty)
    val res = Interpreter.run(init)

    println(s"status:    ${res.status}")
    println(s"gas used:  ${gas - res.gas}")
    println(s"return:    ${toHex(res.returnData)}")
    println(s"logs:      ${res.logs.size}")

  // Convert a hex string (optional 0x prefix) into a byte list for the core.
  private def parseHex(s: String): SList[BigInt] =
    val clean = if (s.startsWith("0x")) s.substring(2) else s
    clean.grouped(2).map(h => BigInt(h, 16)).toList
      .foldRight(SNil[BigInt](): SList[BigInt])((b, acc) => Cons(b, acc))

  // Render a byte list back to a hex string.
  private def toHex(l: SList[BigInt]): String =
    if (l.isEmpty) "0x (empty)"
    else
      val sb = new StringBuilder("0x")
      var cur = l
      while (!cur.isEmpty) do
        sb.append(f"${(cur.head.toInt & 0xff)}%02x")
        cur = cur.tail
      sb.toString

  // The value following `name` in the argument list, if present.
  private def flag(args: Array[String], name: String): Option[String] =
    val i = args.indexOf(name)
    if (i >= 0 && i + 1 < args.length) Some(args(i + 1)) else None
