package evm

import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*
import evm.math.*

import stainless.collection.*
import evm.value.Word256

class InterpreterSuite extends munit.FunSuite {

  val MAX: BigInt = evm.math.EvmMath.MAX_VALUE

  def code(bytes: Int*): Code =
    Code(bytes.foldRight(Nil[BigInt](): List[BigInt])((b, acc) => Cons(BigInt(b), acc)))

  def run(gas: BigInt, bytes: Int*): ExecState =
    Interpreter.run(ExecState.initial(code(bytes*), gas))

  test("empty code halts immediately") {
    val s = run(1000)
    assertEquals(s.status, Status.Halted)
  }

  test("PUSH1 then STOP leaves the value on the stack and halts") {
    val s = run(1000, 0x60, 0x2A, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.data.size, BigInt(1))
    assertEquals(s.stack.peek(0).value, BigInt(0x2A))
  }

  test("PUSH1 5 PUSH1 3 ADD computes 8") {
    val s = run(1000, 0x60, 0x05, 0x60, 0x03, 0x01, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.data.size, BigInt(1))
    assertEquals(s.stack.peek(0).value, BigInt(8))
  }

  test("POP removes the top item") {
    val s = run(1000, 0x60, 0x01, 0x50, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.data.size, BigInt(0))
  }

  test("ADD on an empty stack fails") {
    val s = run(1000, 0x01)
    assertEquals(s.status, Status.Failed)
  }

  test("running out of gas fails") {
    val s = run(2, 0x60, 0x01, 0x60, 0x02, 0x01, 0x00)
    assertEquals(s.status, Status.Failed)
  }

  test("MUL and SUB compute correctly") {
    val mul = run(1000, 0x60, 0x06, 0x60, 0x07, 0x02, 0x00)
    assertEquals(mul.stack.peek(0).value, BigInt(42))
    val sub = run(1000, 0x60, 0x03, 0x60, 0x0A, 0x03, 0x00)
    assertEquals(sub.stack.peek(0).value, BigInt(7))
  }

  test("LT pushes 1 or 0") {
    val t = run(1000, 0x60, 0x05, 0x60, 0x02, 0x10, 0x00)
    assertEquals(t.stack.peek(0).value, BigInt(1))
    val f = run(1000, 0x60, 0x02, 0x60, 0x05, 0x10, 0x00)
    assertEquals(f.stack.peek(0).value, BigInt(0))
  }

  test("ISZERO and NOT") {
    val z = run(1000, 0x60, 0x00, 0x15, 0x00)
    assertEquals(z.stack.peek(0).value, BigInt(1))
    val n = run(1000, 0x60, 0x00, 0x19, 0x00)
    assertEquals(n.stack.peek(0).value, MAX)
  }

  test("AND of 0xF0 and 0x0F is 0") {
    val s = run(1000, 0x60, 0xF0, 0x60, 0x0F, 0x16, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(0))
  }

  test("SHL shifts the value by the shift amount") {
    val s = run(1000, 0x60, 0x01, 0x60, 0x04, 0x1B, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(16))
  }

  test("PUSH2 reads a two-byte immediate") {
    val s = run(1000, 0x61, 0x12, 0x34, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(0x1234))
  }

  test("DUP1 duplicates the top and SWAP1 swaps the top two") {
    val d = run(1000, 0x60, 0x07, 0x80, 0x00)
    assertEquals(d.stack.data.size, BigInt(2))
    assertEquals(d.stack.peek(0).value, BigInt(7))
    assertEquals(d.stack.peek(1).value, BigInt(7))
    val w = run(1000, 0x60, 0x01, 0x60, 0x02, 0x90, 0x00)
    assertEquals(w.stack.peek(0).value, BigInt(1))
    assertEquals(w.stack.peek(1).value, BigInt(2))
  }

  test("ADDMOD uses the true sum before the modulus") {
    val s = run(1000, 0x60, 0x08, 0x60, 0x0A, 0x60, 0x0A, 0x08, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(4))
  }

  test("MSTORE then MLOAD round-trips a word through memory") {
    val s = run(10000, 0x60, 0x2A, 0x60, 0x00, 0x52, 0x60, 0x00, 0x51, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(0x2A))
  }

  test("MSTORE grows memory and MSIZE reports it") {
    val s = run(10000, 0x60, 0x01, 0x60, 0x00, 0x52, 0x59, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(32))
  }

  test("MLOAD of an unwritten slot reads zero") {
    val s = run(10000, 0x60, 0x40, 0x51, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(0))
  }

  test("MSTORE8 writes a single byte") {
    val s = run(10000, 0x60, 0xFF, 0x60, 0x00, 0x53, 0x59, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(32))
  }

  test("memory expansion at a high offset runs out of gas") {
    val s = run(50, 0x60, 0x00, 0x61, 0xFF, 0xFF, 0x52, 0x00)
    assertEquals(s.status, Status.Failed)
  }

  test("EXP with a large exponent costs more gas than the base") {
    val ok = run(1000, 0x61, 0x01, 0x00, 0x60, 0x02, 0x0A, 0x00)
    assertEquals(ok.status, Status.Halted)
    val oog = run(30, 0x61, 0x01, 0x00, 0x60, 0x02, 0x0A, 0x00)
    assertEquals(oog.status, Status.Failed)
  }

  def runWith(gas: BigInt, block: BlockContext, tx: TxContext, msg: MessageContext,
              world: WorldState, bytes: Int*): ExecState =
    Interpreter.run(ExecState.initialWith(code(bytes*), gas, block, tx, msg, world))

  test("CALLER, CALLVALUE and ORIGIN read the message and tx context") {
    val msg = MessageContext(Address(BigInt(9)), Address(BigInt(0xABCD)), Word256(BigInt(77)), Nil())
    val tx = TxContext(Address(BigInt(0x1234)), Word256(BigInt(5)))
    val caller = runWith(1000, BlockContext.empty, tx, msg, WorldState.empty, 0x33, 0x00)
    assertEquals(caller.stack.peek(0).value, BigInt(0xABCD))
    val value = runWith(1000, BlockContext.empty, tx, msg, WorldState.empty, 0x34, 0x00)
    assertEquals(value.stack.peek(0).value, BigInt(77))
    val origin = runWith(1000, BlockContext.empty, tx, msg, WorldState.empty, 0x32, 0x00)
    assertEquals(origin.stack.peek(0).value, BigInt(0x1234))
  }

  test("NUMBER and CHAINID read the block context") {
    val block = BlockContext.empty.copy(number = Word256(BigInt(19000000)), chainId = Word256(BigInt(1)))
    val num = runWith(1000, block, TxContext.empty, MessageContext.empty, WorldState.empty, 0x43, 0x00)
    assertEquals(num.stack.peek(0).value, BigInt(19000000))
    val chain = runWith(1000, block, TxContext.empty, MessageContext.empty, WorldState.empty, 0x46, 0x00)
    assertEquals(chain.stack.peek(0).value, BigInt(1))
  }

  test("SELFBALANCE reads the executing account's balance from the world") {
    val self = Address(BigInt(42))
    val msg = MessageContext(self, Address.zero, Word256.Zero, Nil())
    val world = WorldState(stainless.lang.Map(self -> Account(Word256(BigInt(999)), Code.empty)))
    val s = runWith(1000, BlockContext.empty, TxContext.empty, msg, world, 0x47, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(999))
  }

  test("CODESIZE and PC report machine state") {
    val sz = run(1000, 0x38, 0x00)
    assertEquals(sz.stack.peek(0).value, BigInt(2))
    val pc = run(1000, 0x5B, 0x58, 0x00)
    assertEquals(pc.stack.peek(0).value, BigInt(1))
  }

  test("BALANCE reads an account's balance from the world by address") {
    val target = Address(BigInt(0x77))
    val world = WorldState(stainless.lang.Map(target -> Account(Word256(BigInt(555)), Code.empty)))
    val s = runWith(5000, BlockContext.empty, TxContext.empty, MessageContext.empty, world, 0x60, 0x77, 0x31, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(555))
  }

  test("a cold BALANCE costs 2600 and a repeat warm access costs 100") {
    val cold = run(2603, 0x60, 0x77, 0x31, 0x00)
    assertEquals(cold.status, Status.Halted)
    val coldOog = run(2602, 0x60, 0x77, 0x31, 0x00)
    assertEquals(coldOog.status, Status.Failed)
    val warmSecond = run(2900, 0x60, 0x77, 0x31, 0x50, 0x60, 0x77, 0x31, 0x00)
    assertEquals(warmSecond.status, Status.Halted)
  }

  test("EXTCODESIZE reads an account's code length") {
    val target = Address(BigInt(0x88))
    val world = WorldState(stainless.lang.Map(target -> Account(Word256.Zero, code(0x60, 0x00, 0x00))))
    val s = runWith(5000, BlockContext.empty, TxContext.empty, MessageContext.empty, world,
      0x60, 0x88, 0x3B, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(3))
  }

  test("an unsupported opcode fails") {
    val s = run(1000, 0xF3)
    assertEquals(s.status, Status.Failed)
  }
}
