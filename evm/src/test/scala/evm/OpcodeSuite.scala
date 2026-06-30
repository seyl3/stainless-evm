package evm

import stainless.lang.{Some, None}

class OpcodeSuite extends munit.FunSuite {

  test("hex returns the opcode byte") {
    assertEquals(Opcode.hex(Opcode.STOP), 0x00)
    assertEquals(Opcode.hex(Opcode.ADD), 0x01)
    assertEquals(Opcode.hex(Opcode.CLZ), 0x1E)
    assertEquals(Opcode.hex(Opcode.PUSH1), 0x60)
    assertEquals(Opcode.hex(Opcode.PUSH32), 0x7F)
    assertEquals(Opcode.hex(Opcode.SELFDESTRUCT), 0xFF)
  }

  test("baseGas returns the static cost per opcode") {
    assertEquals(Opcode.baseGas(Opcode.STOP), BigInt(0))
    assertEquals(Opcode.baseGas(Opcode.ADD), BigInt(3))
    assertEquals(Opcode.baseGas(Opcode.MUL), BigInt(5))
    assertEquals(Opcode.baseGas(Opcode.ADDMOD), BigInt(8))
    assertEquals(Opcode.baseGas(Opcode.EXP), BigInt(10))
    assertEquals(Opcode.baseGas(Opcode.JUMPDEST), BigInt(1))
    assertEquals(Opcode.baseGas(Opcode.SLOAD), BigInt(100))
    assertEquals(Opcode.baseGas(Opcode.LOG2), BigInt(1125))
    assertEquals(Opcode.baseGas(Opcode.CREATE), BigInt(32000))
    assertEquals(Opcode.baseGas(Opcode.SELFDESTRUCT), BigInt(5000))
  }

  test("decode maps a byte to its opcode, None for undefined bytes") {
    assertEquals(Opcode.decode(0x00), Some(Opcode.STOP))
    assertEquals(Opcode.decode(0x01), Some(Opcode.ADD))
    assertEquals(Opcode.decode(0x60), Some(Opcode.PUSH1))
    assertEquals(Opcode.decode(0xFF), Some(Opcode.SELFDESTRUCT))
    assertEquals(Opcode.decode(0x0C), None())
    assertEquals(Opcode.decode(0x21), None())
    assertEquals(Opcode.decode(0xF6), None())
  }

  test("decode is the inverse of hex") {
    for op <- List(Opcode.STOP, Opcode.ADD, Opcode.PUSH32, Opcode.MCOPY, Opcode.CLZ, Opcode.SELFDESTRUCT) do
      assertEquals(Opcode.decode(Opcode.hex(op)), Some(op))
  }
}
