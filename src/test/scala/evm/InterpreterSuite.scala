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

  test("SSTORE then SLOAD round-trips a value through storage") {
    val s = run(30000, 0x60, 0x2A, 0x60, 0x01, 0x55, 0x60, 0x01, 0x54, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(0x2A))
  }

  test("a fresh SSTORE costs 22100 and out-of-gas one below") {
    val ok = run(22106, 0x60, 0x2A, 0x60, 0x01, 0x55, 0x00)
    assertEquals(ok.status, Status.Halted)
    val oog = run(22105, 0x60, 0x2A, 0x60, 0x01, 0x55, 0x00)
    assertEquals(oog.status, Status.Failed)
  }

  test("a cold SLOAD costs 2100 and a repeat warm access costs 100") {
    val cold = run(2103, 0x60, 0x01, 0x54, 0x00)
    assertEquals(cold.status, Status.Halted)
    val coldOog = run(2102, 0x60, 0x01, 0x54, 0x00)
    assertEquals(coldOog.status, Status.Failed)
    val warmSecond = run(2300, 0x60, 0x01, 0x54, 0x50, 0x60, 0x01, 0x54, 0x00)
    assertEquals(warmSecond.status, Status.Halted)
  }

  test("TSTORE then TLOAD round-trips through transient storage") {
    val s = run(1000, 0x60, 0x63, 0x60, 0x05, 0x5D, 0x60, 0x05, 0x5C, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(0x63))
  }

  test("transient storage is separate from persistent storage") {
    val s = run(5000, 0x60, 0x63, 0x60, 0x05, 0x5D, 0x60, 0x05, 0x54, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(0))
  }

  test("JUMP to a valid JUMPDEST continues there") {
    val s = run(1000, 0x60, 0x04, 0x56, 0x00, 0x5B, 0x60, 0x2A, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(0x2A))
  }

  test("JUMP to a non-JUMPDEST fails") {
    val s = run(1000, 0x60, 0x01, 0x56, 0x00)
    assertEquals(s.status, Status.Failed)
  }

  test("JUMPI branches when the condition is nonzero") {
    val s = run(1000, 0x60, 0x01, 0x60, 0x06, 0x57, 0x00, 0x5B, 0x60, 0x2A, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(0x2A))
  }

  test("JUMPI falls through when the condition is zero") {
    val s = run(1000, 0x60, 0x00, 0x60, 0x06, 0x57, 0x60, 0x63, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(0x63))
  }

  test("RETURN halts and REVERT reverts") {
    val ret = run(1000, 0x60, 0x00, 0x60, 0x00, 0xF3)
    assertEquals(ret.status, Status.Halted)
    val rev = run(1000, 0x60, 0x00, 0x60, 0x00, 0xFD)
    assertEquals(rev.status, Status.Reverted)
  }

  test("REVERT keeps remaining gas while an exceptional halt consumes it all") {
    val rev = run(1000, 0x60, 0x00, 0x60, 0x00, 0xFD)
    assert(rev.gas > BigInt(0))
    val bad = run(1000, 0xF1)
    assertEquals(bad.gas, BigInt(0))
  }

  test("a backward JUMP loop terminates by running out of gas") {
    val s = run(100, 0x5B, 0x60, 0x00, 0x56)
    assertEquals(s.status, Status.Failed)
  }

  test("DIV and MOD are unsigned with the top operand as dividend") {
    assertEquals(run(1000, 0x60, 0x03, 0x60, 0x14, 0x04, 0x00).stack.peek(0).value, BigInt(6))
    assertEquals(run(1000, 0x60, 0x03, 0x60, 0x14, 0x06, 0x00).stack.peek(0).value, BigInt(2))
  }

  test("SDIV divides signed: -6 / 2 == -3") {
    val s = run(1000, 0x60, 0x02, 0x60, 0x06, 0x60, 0x00, 0x03, 0x05, 0x00)
    assertEquals(s.stack.peek(0).value, MAX - 2)
  }

  test("SMOD takes the sign of the dividend: -6 % 4 == -2") {
    val s = run(1000, 0x60, 0x04, 0x60, 0x06, 0x60, 0x00, 0x03, 0x07, 0x00)
    assertEquals(s.stack.peek(0).value, MAX - 1)
  }

  test("SIGNEXTEND extends the sign bit of the given byte") {
    val s = run(1000, 0x60, 0xFF, 0x60, 0x00, 0x0B, 0x00)
    assertEquals(s.stack.peek(0).value, MAX)
  }

  test("MULMOD uses the true product before the modulus") {
    val s = run(1000, 0x60, 0x08, 0x60, 0x0A, 0x60, 0x0A, 0x09, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(4))
  }

  test("GT and EQ") {
    assertEquals(run(1000, 0x60, 0x02, 0x60, 0x05, 0x11, 0x00).stack.peek(0).value, BigInt(1))
    assertEquals(run(1000, 0x60, 0x07, 0x60, 0x07, 0x14, 0x00).stack.peek(0).value, BigInt(1))
  }

  test("SLT and SGT compare signed: -1 < 1 and 1 > -1") {
    val slt = run(1000, 0x60, 0x01, 0x60, 0x00, 0x19, 0x12, 0x00)
    assertEquals(slt.stack.peek(0).value, BigInt(1))
    val sgt = run(1000, 0x60, 0x00, 0x19, 0x60, 0x01, 0x13, 0x00)
    assertEquals(sgt.stack.peek(0).value, BigInt(1))
  }

  test("OR and XOR") {
    assertEquals(run(1000, 0x60, 0xF0, 0x60, 0x0F, 0x17, 0x00).stack.peek(0).value, BigInt(0xFF))
    assertEquals(run(1000, 0x60, 0xFF, 0x60, 0x0F, 0x18, 0x00).stack.peek(0).value, BigInt(0xF0))
  }

  test("BYTE extracts the indexed byte (0 = most significant)") {
    val s = run(1000, 0x61, 0x12, 0x34, 0x60, 0x1F, 0x1A, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(0x34))
  }

  test("SHR is logical and SAR is arithmetic") {
    assertEquals(run(1000, 0x60, 0xFF, 0x60, 0x04, 0x1C, 0x00).stack.peek(0).value, BigInt(0x0F))
    val sar = run(1000, 0x60, 0x00, 0x19, 0x60, 0x01, 0x1D, 0x00)
    assertEquals(sar.stack.peek(0).value, MAX)
  }

  test("CLZ counts leading zero bits") {
    assertEquals(run(1000, 0x60, 0x01, 0x1E, 0x00).stack.peek(0).value, BigInt(255))
    assertEquals(run(1000, 0x60, 0x00, 0x1E, 0x00).stack.peek(0).value, BigInt(256))
  }

  test("MCOPY copies a word between memory regions") {
    val s = run(30000, 0x60, 0x2A, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0x60, 0x20, 0x5E, 0x60, 0x20, 0x51, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value, BigInt(0x2A))
  }

  test("DUP2 and SWAP2 reach the second and third items") {
    val dup = run(1000, 0x60, 0x01, 0x60, 0x02, 0x81, 0x00)
    assertEquals(dup.stack.data.size, BigInt(3))
    assertEquals(dup.stack.peek(0).value, BigInt(1))
    val swap = run(1000, 0x60, 0x01, 0x60, 0x02, 0x60, 0x03, 0x91, 0x00)
    assertEquals(swap.stack.peek(0).value, BigInt(1))
    assertEquals(swap.stack.peek(2).value, BigInt(3))
  }

  test("CALLDATALOAD reads a 32-byte word from calldata, zero-padded") {
    val cd: List[BigInt] = Cons(BigInt(0x11), Cons(BigInt(0x22), Nil()))
    val msg = MessageContext(Address.zero, Address.zero, Word256.Zero, cd)
    val s = runWith(1000, BlockContext.empty, TxContext.empty, msg, WorldState.empty, 0x60, 0x00, 0x35, 0x00)
    assertEquals(s.stack.peek(0).value, BigInt(0x1122) * BigInt(2).pow(240))
  }

  test("CODECOPY copies code into memory and MLOAD reads it back") {
    val s = run(30000, 0x60, 0x04, 0x60, 0x00, 0x60, 0x00, 0x39, 0x60, 0x00, 0x51, 0x00)
    assertEquals(s.status, Status.Halted)
    val top = s.stack.peek(0).value
    assertEquals(top / BigInt(2).pow(248), BigInt(0x60))
  }

  test("CALLDATACOPY copies calldata into memory") {
    val cd: List[BigInt] = Cons(BigInt(0xAB), Nil())
    val msg = MessageContext(Address.zero, Address.zero, Word256.Zero, cd)
    val s = runWith(30000, BlockContext.empty, TxContext.empty, msg, WorldState.empty,
      0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x37, 0x60, 0x00, 0x51, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.stack.peek(0).value / BigInt(2).pow(248), BigInt(0xAB))
  }

  test("RETURNDATASIZE is zero and RETURNDATACOPY out of range fails") {
    assertEquals(run(1000, 0x3D, 0x00).stack.peek(0).value, BigInt(0))
    val oor = run(30000, 0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x3E, 0x00)
    assertEquals(oor.status, Status.Failed)
  }

  test("LOG1 emits a log with the executing address, one topic and the data") {
    val self = Address(BigInt(0x99))
    val msg = MessageContext(self, Address.zero, Word256.Zero, Nil())
    val s = runWith(30000, BlockContext.empty, TxContext.empty, msg, WorldState.empty,
      0x60, 0x2A, 0x60, 0x00, 0x52,
      0x60, 0xAA, 0x60, 0x20, 0x60, 0x00, 0xA1, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.logs.size, BigInt(1))
    assertEquals(s.logs.head.address.value, BigInt(0x99))
    assertEquals(s.logs.head.topics.size, BigInt(1))
    assertEquals(s.logs.head.topics.head.value, BigInt(0xAA))
    assertEquals(s.logs.head.data.size, BigInt(32))
  }

  test("LOG0 emits a log with no topics and consumes offset and length") {
    val s = run(30000, 0x60, 0x00, 0x60, 0x00, 0xA0, 0x00)
    assertEquals(s.status, Status.Halted)
    assertEquals(s.logs.size, BigInt(1))
    assertEquals(s.logs.head.topics.size, BigInt(0))
    assertEquals(s.stack.data.size, BigInt(0))
  }

  test("LOG in a static context fails") {
    val base = ExecState.initialWith(code(0x60, 0x00, 0x60, 0x00, 0xA0, 0x00), 30000,
      BlockContext.empty, TxContext.empty, MessageContext.empty, WorldState.empty)
    val s = Interpreter.run(base.copy(static = true))
    assertEquals(s.status, Status.Failed)
  }

  test("an unsupported opcode fails") {
    val s = run(1000, 0xF1)
    assertEquals(s.status, Status.Failed)
  }
}
