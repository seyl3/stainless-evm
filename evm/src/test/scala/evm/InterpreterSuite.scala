package evm

import stainless.collection.*
import evm.core.Word256

class InterpreterSuite extends munit.FunSuite {

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

  test("an unsupported opcode fails") {
    val s = run(1000, 0x02)
    assertEquals(s.status, Status.Failed)
  }
}
