package evm

import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*
import evm.math.*

import evm.value.Word256

class StorageSuite extends munit.FunSuite {

  def w(n: BigInt): Word256 = Word256(n)

  test("empty storage reads zero for any key") {
    assertEquals(Storage.empty.load(w(0)).value, BigInt(0))
    assertEquals(Storage.empty.load(w(12345)).value, BigInt(0))
  }

  test("store then load round-trips a value") {
    val s = Storage.empty.store(w(1), w(42))
    assertEquals(s.load(w(1)).value, BigInt(42))
  }

  test("store leaves other keys unchanged") {
    val s = Storage.empty.store(w(1), w(42)).store(w(2), w(99))
    assertEquals(s.load(w(1)).value, BigInt(42))
    assertEquals(s.load(w(2)).value, BigInt(99))
    assertEquals(s.load(w(3)).value, BigInt(0))
  }

  test("storing a key again overwrites it") {
    val s = Storage.empty.store(w(1), w(42)).store(w(1), w(7))
    assertEquals(s.load(w(1)).value, BigInt(7))
  }

  test("storing zero is observable as zero") {
    val s = Storage.empty.store(w(1), w(0))
    assertEquals(s.load(w(1)).value, BigInt(0))
  }
}
