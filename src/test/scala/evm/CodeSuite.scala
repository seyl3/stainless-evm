package evm

import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*
import evm.math.*

import stainless.collection.*
import stainless.lang.{Some, None}

class CodeSuite extends munit.FunSuite {

  def code(bytes: Int*): Code =
    Code(bytes.foldRight(Nil[BigInt](): List[BigInt])((b, acc) => Cons(BigInt(b), acc)))

  test("empty code has size zero") {
    assertEquals(Code.empty.size, BigInt(0))
  }

  test("byteAt reads the raw byte at a position") {
    val c = code(0x60, 0x01, 0x00)
    assertEquals(c.size, BigInt(3))
    assertEquals(c.byteAt(0), BigInt(0x60))
    assertEquals(c.byteAt(2), BigInt(0x00))
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

  test("pushValue reads a big-endian immediate after the opcode") {
    val c = code(0x60, 0x11, 0x61, 0x12, 0x34)
    assertEquals(c.pushValue(1, 1).value, BigInt(0x11))
    assertEquals(c.pushValue(3, 2).value, BigInt(0x1234))
  }

  test("pushValue of width 0 is zero") {
    assertEquals(code(0x5F).pushValue(1, 0).value, BigInt(0))
  }

  test("pushValue past the end of code pads with zero bytes") {
    val c = code(0x61, 0xAB)
    assertEquals(c.pushValue(1, 2).value, BigInt(0xAB00))
  }
}
