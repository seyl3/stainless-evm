package evm

import stainless.collection.*
import stainless.lang.{Some, None}

class CodeSuite extends munit.FunSuite {

  def code(bytes: Int*): Code =
    Code(bytes.foldRight(Nil[Int](): List[Int])((b, acc) => Cons(b, acc)))

  test("empty code has size zero") {
    assertEquals(Code.empty.size, BigInt(0))
  }

  test("byteAt reads the raw byte at a position") {
    val c = code(0x60, 0x01, 0x00)
    assertEquals(c.size, BigInt(3))
    assertEquals(c.byteAt(0), 0x60)
    assertEquals(c.byteAt(2), 0x00)
  }

  test("opcodeAt decodes the byte at a position") {
    val c = code(0x60, 0x01, 0x00)
    assertEquals(c.opcodeAt(0), Some(Opcode.PUSH1))
    assertEquals(c.opcodeAt(1), Some(Opcode.ADD))
    assertEquals(c.opcodeAt(2), Some(Opcode.STOP))
  }

  test("opcodeAt is None on an undefined byte") {
    val c = code(0x0C)
    assertEquals(c.opcodeAt(0), None())
  }

  test("a real JUMPDEST is a valid jump destination") {
    val c = code(0x5B)
    assert(c.isValidJumpDest(0))
  }

  test("a 0x5B inside PUSH data is not a valid jump destination") {
    val c = code(0x60, 0x5B)
    assert(!c.isValidJumpDest(0))
    assert(!c.isValidJumpDest(1))
  }

  test("analysis skips push immediates to find the real JUMPDEST") {
    val c = code(0x60, 0x5B, 0x5B)
    assert(!c.isValidJumpDest(1))
    assert(c.isValidJumpDest(2))
  }

  test("no valid jump destinations in empty or plain code") {
    assert(!Code.empty.isValidJumpDest(0))
    assert(!code(0x01, 0x02).isValidJumpDest(0))
  }
}
