package evm

import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*
import evm.math.*

import stainless.collection.*

class ExecStateSuite extends munit.FunSuite {

  def st(gas: BigInt): ExecState = ExecState.initial(Code.empty, gas)

  test("initial state starts running at pc 0 with the given gas") {
    val s = st(1000)
    assertEquals(s.pc, BigInt(0))
    assertEquals(s.gas, BigInt(1000))
    assertEquals(s.depth, BigInt(0))
    assertEquals(s.static, false)
    assert(s.isRunning)
    assertEquals(s.stack.data.size, BigInt(0))
    assertEquals(s.memory.msize, BigInt(0))
  }

  test("chargeGas subtracts from remaining gas") {
    val s = st(1000).chargeGas(30)
    assertEquals(s.gas, BigInt(970))
  }

  test("outOfGas is true exactly when cost exceeds remaining gas") {
    val s = st(100)
    assert(!s.outOfGas(100))
    assert(s.outOfGas(101))
  }

  test("advancePc moves the program counter") {
    assertEquals(st(10).advancePc(3).pc, BigInt(3))
  }

  test("halt and revert stop execution without touching gas") {
    val s = st(500)
    val h = s.halt
    assert(!h.isRunning)
    assertEquals(h.status, Status.Halted)
    assertEquals(h.gas, BigInt(500))
    val r = s.revert
    assert(!r.isRunning)
    assertEquals(r.status, Status.Reverted)
  }

  test("initial fills empty block, tx, message and world contexts") {
    val s = st(1000)
    assertEquals(s.block.number.value, BigInt(0))
    assertEquals(s.tx.origin.value, BigInt(0))
    assertEquals(s.msg.caller.value, BigInt(0))
    assertEquals(s.msg.callData.size, BigInt(0))
    assertEquals(s.world.balanceOf(Address.zero).value, BigInt(0))
  }

  test("initialWith threads a supplied context into the state") {
    val block = BlockContext.empty.copy(number = Word256(BigInt(42)))
    val tx = TxContext(Address(BigInt(7)), Word256(BigInt(3)))
    val msg = MessageContext(Address(BigInt(9)), Address(BigInt(11)), Word256(BigInt(5)), Nil())
    val s = ExecState.initialWith(Code.empty, 1000, block, tx, msg, WorldState.empty)
    assertEquals(s.block.number.value, BigInt(42))
    assertEquals(s.tx.gasPrice.value, BigInt(3))
    assertEquals(s.msg.self.value, BigInt(9))
    assertEquals(s.msg.caller.value, BigInt(11))
    assertEquals(s.msg.callValue.value, BigInt(5))
  }
}
