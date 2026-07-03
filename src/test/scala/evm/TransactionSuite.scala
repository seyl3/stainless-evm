package evm

import stainless.collection.*
import stainless.lang.Map
import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*

class TransactionSuite extends munit.FunSuite {

  def code(bytes: Int*): Code =
    Code(bytes.foldRight(Nil[BigInt](): List[BigInt])((b, acc) => Cons(BigInt(b), acc)))

  val to: Address = Address(BigInt(0x1000))

  def worldWith(c: Code): WorldState =
    WorldState(Map(to -> Account(Word256.Zero, c)))

  def tx(gasLimit: BigInt, data: List[BigInt] = Nil()): Transaction =
    Transaction(Address(BigInt(1)), to, Word256.Zero, gasLimit, Word256.Zero, data)

  test("a simple transaction runs the recipient code and bills intrinsic plus execution gas") {
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(code(0x60, 0x01, 0x00)))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasUsed, BigInt(21003))
  }

  test("a transaction with gas below the intrinsic cost fails and consumes its whole limit") {
    val res = Transaction.run(tx(20000), BlockContext.empty, worldWith(code(0x60, 0x01, 0x00)))
    assertEquals(res.status, Status.Failed)
    assertEquals(res.gasUsed, BigInt(20000))
  }

  test("clearing a dirty slot back to its original grants a refund capped at gasUsed/5") {
    val program = code(0x60, 0x05, 0x60, 0x01, 0x55, 0x60, 0x00, 0x60, 0x01, 0x55, 0x00)
    val res = Transaction.run(tx(100000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasRefunded, BigInt(8642))
    assertEquals(res.gasUsed, BigInt(34570))
  }

  test("a reverting transaction reports Reverted, grants no refund and commits no storage") {
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(code(0x60, 0x00, 0x60, 0x00, 0xFD)))
    assertEquals(res.status, Status.Reverted)
    assertEquals(res.gasRefunded, BigInt(0))
    assertEquals(res.world.storageOf(to).load(Word256(BigInt(1))).value, BigInt(0))
  }

  test("RETURN sets the transaction output to the returned memory region") {
    // MSTORE8 0xAB at offset 0, then RETURN offset 0 length 1
    val program = code(0x60, 0xAB, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xF3)
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.returnData.size, BigInt(1))
    assertEquals(res.returnData.head, BigInt(0xAB))
  }

  test("REVERT returns its data at the transaction boundary") {
    val program = code(0x60, 0xAB, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xFD)
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Reverted)
    assertEquals(res.returnData.size, BigInt(1))
    assertEquals(res.returnData.head, BigInt(0xAB))
  }

  test("the recipient account is pre-warmed so BALANCE on self is warm") {
    // PUSH2 0x1000 (== to), BALANCE, STOP: warm access costs 100, not cold 2600
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(code(0x61, 0x10, 0x00, 0x31, 0x00)))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasUsed, BigInt(21103))
  }

  test("intrinsic gas charges 16 per nonzero and 4 per zero calldata byte") {
    val data: List[BigInt] = Cons(BigInt(0x00), Cons(BigInt(0xFF), Nil()))
    assertEquals(Transaction.intrinsicGas(data), BigInt(21000 + 4 + 16))
  }

  test("storage persists across transactions through the world state") {
    // contract increments slot 0: PUSH0key SLOAD PUSH1 ADD PUSH0key SSTORE STOP
    val counter = code(0x60, 0x00, 0x54, 0x60, 0x01, 0x01, 0x60, 0x00, 0x55, 0x00)
    val w0 = worldWith(counter)
    val r1 = Transaction.run(tx(100000), BlockContext.empty, w0)
    assertEquals(r1.status, Status.Halted)
    assertEquals(r1.world.storageOf(to).load(Word256.Zero).value, BigInt(1))
    // second tx runs against the world produced by the first
    val r2 = Transaction.run(tx(100000), BlockContext.empty, r1.world)
    assertEquals(r2.world.storageOf(to).load(Word256.Zero).value, BigInt(2))
  }

  test("a reverting transaction does not persist its storage writes") {
    // SSTORE slot 0 = 7, then REVERT
    val program = code(0x60, 0x07, 0x60, 0x00, 0x55, 0x60, 0x00, 0x60, 0x00, 0xFD)
    val res = Transaction.run(tx(100000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Reverted)
    assertEquals(res.world.storageOf(to).load(Word256.Zero).value, BigInt(0))
  }

  test("EIP-7623: a calldata-heavy low-execution tx is charged the token floor") {
    val data: List[BigInt] = Cons(BigInt(0xFF), Cons(BigInt(0xFF), Nil()))
    // tokens = 8; floor = 21000 + 80 = 21080; standard intrinsic = 21000 + 32 = 21032; STOP adds 0
    val res = Transaction.run(
      Transaction(Address(BigInt(1)), to, Word256.Zero, 30000, Word256.Zero, data),
      BlockContext.empty, worldWith(code(0x00)))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasUsed, BigInt(21080))
  }
}
