package evm.core

class Word256Suite extends munit.FunSuite {

  val MOD: BigInt = BigInt(2).pow(256)
  val MAX: BigInt = MOD - 1
  val MIN: BigInt = BigInt(2).pow(255)

  def w(n: BigInt): Word256 = Word256(n)
  def sw(n: BigInt): Word256 = Word256(((n % MOD) + MOD) % MOD)

  test("construction and constants") {
    assertEquals(w(5).value, BigInt(5))
    assertEquals(Word256.Zero.value, BigInt(0))
    assertEquals(Word256.One.value, BigInt(1))
  }

  test("add wraps mod 2^256") {
    assertEquals((w(1) + w(1)).value, BigInt(2))
    assertEquals((w(MAX) + w(1)).value, BigInt(0))
    assertEquals((w(MAX) + w(2)).value, BigInt(1))
  }

  test("sub wraps mod 2^256") {
    assertEquals((w(5) - w(3)).value, BigInt(2))
    assertEquals((w(0) - w(1)).value, MAX)
  }

  test("mul wraps mod 2^256") {
    assertEquals((w(3) * w(4)).value, BigInt(12))
    assertEquals((w(MAX) * w(2)).value, MOD - 2)
  }

  test("div and mod, zero divisor gives zero") {
    assertEquals((w(10) / w(3)).value, BigInt(3))
    assertEquals((w(5) / w(0)).value, BigInt(0))
    assertEquals((w(10) % w(3)).value, BigInt(1))
    assertEquals((w(5) % w(0)).value, BigInt(0))
  }

  test("sdiv signed division with truncation and overflow") {
    assertEquals(w(MAX).sdiv(Word256.One).value, MAX)
    assertEquals(sw(-6).sdiv(w(2)).value, MOD - 3)
    assertEquals(w(10).sdiv(w(0)).value, BigInt(0))
    assertEquals(w(MIN).sdiv(w(MAX)).value, MIN)
  }

  test("smod signed modulo follows dividend sign") {
    assertEquals(sw(-6).smod(w(4)).value, MOD - 2)
    assertEquals(w(7).smod(w(3)).value, BigInt(1))
    assertEquals(w(7).smod(w(0)).value, BigInt(0))
  }

  test("bitwise and/or/xor/not") {
    assertEquals((w(0xF0) & w(0x0F)).value, BigInt(0))
    assertEquals((w(0xF0) | w(0x0F)).value, BigInt(0xFF))
    assertEquals((w(0xFF) ^ w(0x0F)).value, BigInt(0xF0))
    assertEquals((~w(0)).value, MAX)
    assertEquals((~w(MAX)).value, BigInt(0))
  }

  test("shl logical left shift") {
    assertEquals(w(1).shl(w(4)).value, BigInt(16))
    assertEquals(w(1).shl(w(256)).value, BigInt(0))
    assertEquals(w(MAX).shl(w(1)).value, MOD - 2)
  }

  test("shr logical right shift") {
    assertEquals(w(16).shr(w(4)).value, BigInt(1))
    assertEquals(w(0xFF).shr(w(4)).value, BigInt(0x0F))
    assertEquals(w(1).shr(w(256)).value, BigInt(0))
  }

  test("sar arithmetic right shift preserves sign") {
    assertEquals(sw(-2).sar(w(1)).value, MAX)
    assertEquals(w(8).sar(w(1)).value, BigInt(4))
    assertEquals(sw(-1).sar(w(256)).value, MAX)
    assertEquals(w(4).sar(w(256)).value, BigInt(0))
  }

  test("exp modular exponentiation") {
    assertEquals((w(2) ** w(10)).value, BigInt(1024))
    assertEquals((w(2) ** w(256)).value, BigInt(0))
    assertEquals((w(5) ** w(0)).value, BigInt(1))
  }

  test("addmod and mulmod use the true result") {
    assertEquals(Word256.addmod(w(10), w(10), w(8)).value, BigInt(4))
    assertEquals(Word256.addmod(w(MAX), w(2), w(5)).value, BigInt(2))
    assertEquals(Word256.addmod(w(1), w(1), w(0)).value, BigInt(0))
    assertEquals(Word256.mulmod(w(3), w(4), w(5)).value, BigInt(2))
    assertEquals(Word256.mulmod(w(MAX), w(MAX), w(5)).value, BigInt(0))
    assertEquals(Word256.mulmod(w(1), w(1), w(0)).value, BigInt(0))
  }

  test("byte extracts the i-th byte") {
    assertEquals(w(0xAB).byte(w(31)).value, BigInt(0xAB))
    assertEquals(w(0xAB).byte(w(0)).value, BigInt(0))
    assertEquals(w(0x1122).byte(w(30)).value, BigInt(0x11))
    assertEquals(w(0x1122).byte(w(31)).value, BigInt(0x22))
    assertEquals(w(0xAB).byte(w(32)).value, BigInt(0))
  }

  test("signextend sign-extends from byte b") {
    assertEquals(w(0xFF).signextend(w(0)).value, MAX)
    assertEquals(w(0x7F).signextend(w(0)).value, BigInt(0x7F))
    assertEquals(w(0x80).signextend(w(0)).value, MOD - 128)
    assertEquals(w(0xFFFF).signextend(w(1)).value, MAX)
    assertEquals(w(0x1234).signextend(w(31)).value, BigInt(0x1234))
  }

  test("clz counts leading zero bits") {
    assertEquals(w(0).clz.value, BigInt(256))
    assertEquals(w(1).clz.value, BigInt(255))
    assertEquals(w(MAX).clz.value, BigInt(0))
    assertEquals(w(MIN).clz.value, BigInt(0))
  }

  test("comparison predicates, unsigned and signed differ") {
    assert(w(0).isZero)
    assert(!w(1).isZero)
    assert(w(1).lt(w(2)))
    assert(w(2).gt(w(1)))
    assertEquals(w(5), w(5))
    assert(!w(MAX).lt(Word256.One))
    assert(w(MAX).slt(Word256.One))
    assert(Word256.One.sgt(w(MAX)))
  }
}
