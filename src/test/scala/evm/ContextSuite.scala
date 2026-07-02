package evm

import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*
import evm.math.*

import stainless.lang.Map
import evm.value.Word256
import evm.env.*

class ContextSuite extends munit.FunSuite {

  def w(n: BigInt): Word256 = Word256(n)

  test("an address holds a 160-bit value") {
    assertEquals(Address(BigInt(0x1234)).value, BigInt(0x1234))
    assertEquals(Address.zero.value, BigInt(0))
  }

  test("empty world state defaults balance to zero and code to empty") {
    val ws = WorldState.empty
    assertEquals(ws.balanceOf(Address(BigInt(1))).value, BigInt(0))
    assertEquals(ws.codeOf(Address(BigInt(1))).size, BigInt(0))
  }

  test("world state returns a stored account's balance and code") {
    val a = Address(BigInt(42))
    val ws = WorldState(Map(a -> Account(w(1000), Code.empty)))
    assertEquals(ws.balanceOf(a).value, BigInt(1000))
    assertEquals(ws.balanceOf(Address(BigInt(43))).value, BigInt(0))
  }
}
