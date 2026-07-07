package evm.cli

import stainless.collection.{List => SList, Nil => SNil, Cons}
import stainless.lang.{Map => SMap}
import evm.value.Word256
import evm.code.{Code, Opcode}
import evm.env.{Account, Address, BlockContext, TxContext, MessageContext, WorldState}
import evm.exec.{ExecState, Interpreter, Transaction}

// Unverified CLI over the verified EVM core. Parses arguments and hex bytecode,
// hands them to Interpreter.run, and prints the result. None of this file is
// verified: it depends on the core as compiled bytecode.
object Main:

  def main(args: Array[String]): Unit =
    if (args.isEmpty) { usage(); return }
    args(0) match
      case "run"    => run(args.drop(1))
      case "tx"     => tx(args.drop(1))
      case "disasm" => disasm(args.drop(1))
      case "help" | "--help" | "-h" => usage()
      case other    => Console.err.println(s"unknown command: $other"); usage()

  private def usage(): Unit =
    println(
      """stainless-evm - run EVM bytecode over the verified core
        |
        |usage:
        |  run <hex> [--gas N] [--calldata HEX] [--value N]
        |      execute bytecode as a single frame; print status, gas, and return data
        |  tx <hex> [--from A] [--to A] [--coinbase A] [--balance N] [--gas N]
        |           [--value N] [--maxfee N] [--priorityfee N] [--basefee N]
        |           [--nonce N] [--calldata HEX]
        |      run a full transaction against a world (the hex is the recipient code);
        |      print settlement and before/after account balances and nonces
        |  disasm <hex>
        |      disassemble bytecode into opcodes with their offsets and immediates
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

  // Run a full transaction: deploy the given code at the recipient, fund the
  // sender, and hand it to Transaction.run. Prints settlement plus before/after
  // balances and nonces so the fee split, value transfer, and nonce bump show.
  private def tx(args: Array[String]): Unit =
    if (args.isEmpty) { Console.err.println("tx: expected recipient bytecode hex"); return }
    val code = Code(parseHex(args(0)))
    val from = flag(args, "--from").map(parseAddr).getOrElse(Address(BigInt(1)))
    val to = flag(args, "--to").map(parseAddr).getOrElse(Address(BigInt(0x1000)))
    val coinbase = flag(args, "--coinbase").map(parseAddr).getOrElse(Address(BigInt(0x2000)))
    val gas = flag(args, "--gas").map(BigInt(_)).getOrElse(BigInt(1000000))
    val value = flag(args, "--value").map(v => Word256(BigInt(v))).getOrElse(Word256.Zero)
    val balance = flag(args, "--balance").map(BigInt(_)).getOrElse(BigInt("1000000000000000000"))
    val maxFee = flag(args, "--maxfee").map(v => Word256(BigInt(v))).getOrElse(Word256.Zero)
    val prioFee = flag(args, "--priorityfee").map(v => Word256(BigInt(v))).getOrElse(Word256.Zero)
    val baseFee = flag(args, "--basefee").map(v => Word256(BigInt(v))).getOrElse(Word256.Zero)
    val nonce = flag(args, "--nonce").map(BigInt(_)).getOrElse(BigInt(0))
    val callData = flag(args, "--calldata").map(parseHex).getOrElse(SNil[BigInt]())

    val world = WorldState(SMap(
      from -> Account(Word256(balance), Code.empty),
      to -> Account(Word256.Zero, code)))
    val block = BlockContext(coinbase, Word256.Zero, Word256.Zero, Word256.Zero,
      Word256.Zero, Word256.Zero, baseFee, Word256.Zero, SMap.empty[Word256, Word256])
    val transaction = Transaction(from, to, value, gas, maxFee, prioFee, nonce, callData)
    val res = Transaction.run(transaction, block, world)

    println(s"status:       ${res.status}")
    println(s"gas used:     ${res.gasUsed}")
    println(s"gas refunded: ${res.gasRefunded}")
    println(s"return:       ${toHex(res.returnData)}")
    println(s"logs:         ${res.logs.size}")
    println()
    printAccount("sender   ", from, world, res.world)
    printAccount("recipient", to, world, res.world)
    printAccount("coinbase ", coinbase, world, res.world)

  // Print an account's balance and nonce, showing before -> after when they moved.
  private def printAccount(label: String, a: Address, before: WorldState, after: WorldState): Unit =
    val b0 = before.balanceOf(a).value
    val b1 = after.balanceOf(a).value
    val n0 = before.nonceOf(a)
    val n1 = after.nonceOf(a)
    val bal = if (b0 == b1) s"balance $b1" else s"balance $b0 -> $b1"
    val non = if (n0 == n1) "" else s"  nonce $n0 -> $n1"
    println(s"$label ${hexAddr(a)}  $bal$non")

  // Disassemble bytecode: walk it opcode by opcode, printing each offset, mnemonic,
  // and (for PUSHn) its immediate. Skipping over immediates is what keeps push data
  // from being mis-read as opcodes.
  private def disasm(args: Array[String]): Unit =
    if (args.isEmpty) { Console.err.println("disasm: expected bytecode hex"); return }
    val bytes = toBytes(parseHex(args(0)))
    var pc = 0
    while (pc < bytes.length) do
      val b = bytes(pc)
      // Opcode.decode returns a stainless Option, so we branch on isDefined/get
      // rather than Scala's Some/None.
      val decoded = Opcode.decode(BigInt(b))
      if (decoded.isDefined)
        val op = decoded.get
        val w = Opcode.pushWidth(op).toInt
        if (w > 0)
          val imm = (pc + 1 until math.min(pc + 1 + w, bytes.length)).map(i => f"${bytes(i)}%02x").mkString
          println(f"0x$pc%04x  ${op.toString}%-13s 0x$imm")
        else
          println(f"0x$pc%04x  ${op.toString}")
        pc += 1 + w
      else
        println(f"0x$pc%04x  ${"?"}%-13s 0x$b%02x  (undefined)")
        pc += 1

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

  // Turn a byte list into an indexable Scala vector
  private def toBytes(l: SList[BigInt]): Vector[Int] =
    val buf = scala.collection.mutable.ArrayBuffer[Int]()
    var cur = l
    while (!cur.isEmpty) do
      buf += (cur.head.toInt & 0xff)
      cur = cur.tail
    buf.toVector

  // Parse a hex (optionally 0x-prefixed) address.
  private def parseAddr(s: String): Address =
    val clean = if (s.startsWith("0x")) s.substring(2) else s
    Address(BigInt(clean, 16))

  // Format a 160-bit address as a zero-padded hex string.
  private def hexAddr(a: Address): String =
    val h = a.value.toString(16)
    "0x" + "0" * (40 - h.length) + h

  // The value following `name` in the argument list, if present.
  private def flag(args: Array[String], name: String): Option[String] =
    val i = args.indexOf(name)
    if (i >= 0 && i + 1 < args.length) Some(args(i + 1)) else None
