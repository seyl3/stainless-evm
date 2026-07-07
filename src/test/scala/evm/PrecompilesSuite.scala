package evm

import stainless.collection.{List => SList, Cons, Nil => SNil}
import evm.value.*

class PrecompilesSuite extends munit.FunSuite {

  def bytes(xs: Int*): SList[BigInt] =
    xs.foldRight(SNil[BigInt](): SList[BigInt])((x, acc) => Cons(BigInt(x), acc))

  def toBig(l: SList[BigInt]): BigInt =
    l.foldLeft(BigInt(0))((acc, b) => (acc << 8) | b)

  test("identity (0x04) returns its input unchanged") {
    val in = bytes(1, 2, 3, 0xFF, 0x00, 0x42)
    assertEquals(Precompiles.identity(in), in)
  }

  test("SHA-256 (0x02) of the empty input") {
    assertEquals(Precompiles.sha256(SNil()).size, BigInt(32))
    assertEquals(toBig(Precompiles.sha256(SNil())),
      BigInt("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 16))
  }

  test("SHA-256 (0x02) of 'abc'") {
    assertEquals(toBig(Precompiles.sha256(bytes(0x61, 0x62, 0x63))),
      BigInt("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad", 16))
  }

  test("RIPEMD-160 (0x03) of the empty input, left-padded to 32 bytes") {
    val out = Precompiles.ripemd160(SNil())
    assertEquals(out.size, BigInt(32))
    assertEquals(toBig(out), BigInt("9c1185a5c5e9fc54612808977ee8f548b2258d31", 16))
  }

  test("RIPEMD-160 (0x03) of 'abc'") {
    assertEquals(toBig(Precompiles.ripemd160(bytes(0x61, 0x62, 0x63))),
      BigInt("8eb208f7e05d987a9b044a8e98c6b087f15a0bfc", 16))
  }

  test("RIPEMD-160 (0x03) of 'message digest'") {
    // "message digest" -> 5d0689ef49d2fae572b881b123a85ffa21595f36
    val md = bytes(0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x20, 0x64, 0x69, 0x67, 0x65, 0x73, 0x74)
    assertEquals(toBig(Precompiles.ripemd160(md)),
      BigInt("5d0689ef49d2fae572b881b123a85ffa21595f36", 16))
  }

  test("precompile gas costs") {
    assertEquals(Precompiles.identityGas(0), BigInt(15))
    assertEquals(Precompiles.identityGas(32), BigInt(18))
    assertEquals(Precompiles.identityGas(33), BigInt(21))
    assertEquals(Precompiles.sha256Gas(0), BigInt(60))
    assertEquals(Precompiles.sha256Gas(32), BigInt(72))
    assertEquals(Precompiles.ripemd160Gas(0), BigInt(600))
    assertEquals(Precompiles.ripemd160Gas(32), BigInt(720))
  }
}
