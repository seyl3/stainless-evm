package evm

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
}
