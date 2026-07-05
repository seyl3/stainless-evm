package evm

import stainless.collection.*
import evm.value.*

class Keccak256Suite extends munit.FunSuite {

  test("keccak256 of the empty input") {
    assertEquals(Keccak256.hash(Nil()).value,
      BigInt("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470", 16))
  }

  test("keccak256 of a single zero byte") {
    assertEquals(Keccak256.hash(Cons(BigInt(0), Nil())).value,
      BigInt("bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a", 16))
  }

  test("keccak256 of the three bytes 'abc'") {
    val abc: List[BigInt] = Cons(BigInt(0x61), Cons(BigInt(0x62), Cons(BigInt(0x63), Nil())))
    assertEquals(Keccak256.hash(abc).value,
      BigInt("4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45", 16))
  }

  def pattern(n: Int): List[BigInt] =
    (0 until n).foldRight(Nil[BigInt](): List[BigInt])((i, acc) => Cons(BigInt(i % 256), acc))

  test("keccak256 one byte below the 136-byte rate boundary") {
    assertEquals(Keccak256.hash(pattern(135)).value,
      BigInt("cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62", 16))
  }

  test("keccak256 of exactly one 136-byte block") {
    assertEquals(Keccak256.hash(pattern(136)).value,
      BigInt("7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e", 16))
  }

  test("keccak256 one byte past the rate boundary") {
    assertEquals(Keccak256.hash(pattern(137)).value,
      BigInt("ac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db", 16))
  }

  test("keccak256 of a three-block 300-byte input") {
    assertEquals(Keccak256.hash(pattern(300)).value,
      BigInt("a679e749a6af300c36e7ff2255d220864eab27b382f9cfdc5aa4d13563ba36ff", 16))
  }
}
