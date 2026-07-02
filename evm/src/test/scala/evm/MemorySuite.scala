package evm

import stainless.lang.Map
import evm.core.Word256
import evm.proofs.Bytes

class MemorySuite extends munit.FunSuite {

  val MAX: BigInt = evm.proofs.EvmMath.MAX_VALUE

  def w(n: BigInt): Word256 = Word256(n)

  test("empty memory is zero everywhere and has size zero") {
    val m = Memory.empty
    assertEquals(m.msize, BigInt(0))
    assertEquals(m.getByte(0), BigInt(0))
    assertEquals(m.getByte(1000), BigInt(0))
  }

  test("store then load round-trips a word") {
    val m = Memory.empty.store(0, w(0x1122334455L))
    assertEquals(m.load(0).value, BigInt(0x1122334455L))
  }

  test("store then load round-trips the maximum word") {
    val m = Memory.empty.store(64, w(MAX))
    assertEquals(m.load(64).value, MAX)
  }

  test("store expands memory to a multiple of 32 covering the word") {
    val m = Memory.empty.store(0, w(1))
    assertEquals(m.msize, BigInt(32))
    val m2 = Memory.empty.store(40, w(1))
    assertEquals(m2.msize, BigInt(96))
  }

  test("loading an unwritten region reads as zero") {
    val m = Memory.empty.store(0, w(0xFF))
    assertEquals(m.load(64).value, BigInt(0))
  }

  test("store8 writes a single byte as the least significant byte") {
    val m = Memory.empty.store8(5, w(0x12AB))
    assertEquals(m.getByte(5), BigInt(0xAB))
    assertEquals(m.getByte(4), BigInt(0))
    assertEquals(m.getByte(6), BigInt(0))
  }

  test("store8 places the byte as the high byte of a word load at that offset") {
    val m = Memory.empty.store8(0, w(0xAB))
    assertEquals(m.load(0).value, BigInt(0xAB) * BigInt(2).pow(248))
  }

  test("a word is stored big-endian (most significant byte first)") {
    val m = Memory.empty.store(0, w(0xAABB))
    assertEquals(m.getByte(30), BigInt(0xAA))
    assertEquals(m.getByte(31), BigInt(0xBB))
    assertEquals(m.getByte(0), BigInt(0))
  }

  test("mcopy duplicates a region") {
    val m = Memory.empty.store(0, w(0xDEAD)).mcopy(32, 0, 32)
    assertEquals(m.load(32).value, BigInt(0xDEAD))
    assertEquals(m.msize, BigInt(64))
  }

  test("mcopy handles overlapping forward copy via source snapshot") {
    val m0 = Memory.empty.store8(0, w(0x11)).store8(1, w(0x22)).store8(2, w(0x33))
    val m1 = m0.mcopy(1, 0, 2)
    assertEquals(m1.getByte(1), BigInt(0x11))
    assertEquals(m1.getByte(2), BigInt(0x22))
  }

  test("mcopy of zero length is a no-op and never expands memory") {
    val base = Memory.empty.store8(0, w(0x77))
    val m = base.mcopy(1000, 0, 0)
    assertEquals(m.getByte(0), BigInt(0x77))
    assertEquals(m.getByte(1000), BigInt(0))
    assertEquals(m.msize, base.msize)
  }

  test("store8 normalizes a value larger than a byte") {
    val m = Memory.empty.store8(0, w(0x1234))
    assertEquals(m.getByte(0), BigInt(0x34))
  }

  test("expand grows size to cover an access without changing contents") {
    val m = Memory.empty.store8(0, w(0x55)).expand(100)
    assertEquals(m.msize, BigInt(128))
    assertEquals(m.getByte(0), BigInt(0x55))
    val same = Memory.empty.store(0, w(1)).expand(10)
    assertEquals(same.msize, BigInt(32))
  }

  test("expandedTo rounds up to a multiple of 32 and never shrinks") {
    val m = Memory.empty
    assertEquals(m.expandedTo(0), BigInt(0))
    assertEquals(m.expandedTo(1), BigInt(32))
    assertEquals(m.expandedTo(32), BigInt(32))
    assertEquals(m.expandedTo(33), BigInt(64))
    val big = Memory.empty.store(0, w(1)).store(64, w(1))
    assertEquals(big.msize, BigInt(96))
    assertEquals(big.expandedTo(10), BigInt(96))
  }

  test("Bytes.emod256 canonicalizes any integer to a byte") {
    assertEquals(Bytes.emod256(0x1234), BigInt(0x34))
    assertEquals(Bytes.emod256(255), BigInt(255))
    assertEquals(Bytes.emod256(256), BigInt(0))
    assertEquals(Bytes.emod256(-1), BigInt(255))
  }

  test("Bytes.getByteOf defaults absent addresses to zero") {
    val d = Bytes.setByteOf(Map.empty[BigInt, BigInt], 5, 0xAB)
    assertEquals(Bytes.getByteOf(d, 5), BigInt(0xAB))
    assertEquals(Bytes.getByteOf(d, 6), BigInt(0))
  }

  test("Bytes.readBytes and writeBytes round-trip at a small width") {
    val d = Bytes.writeBytes(Map.empty[BigInt, BigInt], 0, 3, 0x010203)
    assertEquals(Bytes.readBytes(d, 0, 3), BigInt(0x010203))
    assertEquals(Bytes.getByteOf(d, 0), BigInt(0x01))
    assertEquals(Bytes.getByteOf(d, 2), BigInt(0x03))
  }
}
