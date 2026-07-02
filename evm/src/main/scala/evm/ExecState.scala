package evm

import stainless.collection.*
import stainless.lang.*

enum Status:
  case Running
  case Halted
  case Reverted
  case Failed

object ExecState:
  val MAX_DEPTH: BigInt = 1024

  def initial(code: Code, gas: BigInt): ExecState = {
    require(gas >= 0)
    ExecState(code, Stack.empty, Memory.empty, Storage.empty, Storage.empty,
      BigInt(0), gas, BigInt(0), false, Status.Running, Nil())
  }

case class ExecState(
  code: Code,
  stack: Stack,
  memory: Memory,
  storage: Storage,
  transient: Storage,
  pc: BigInt,
  gas: BigInt,
  depth: BigInt,
  static: Boolean,
  status: Status,
  returnData: List[Int]
):
  require(pc >= 0 && gas >= 0 && depth >= 0 && depth <= ExecState.MAX_DEPTH)

  def isRunning: Boolean = status == Status.Running

  def outOfGas(cost: BigInt): Boolean = {
    require(cost >= 0)
    cost > gas
  }

  def chargeGas(cost: BigInt): ExecState = {
    require(cost >= 0 && cost <= gas)
    copy(gas = gas - cost)
  }.ensuring(r => r.gas == gas - cost && r.gas >= 0 && r.status == status)

  def advancePc(n: BigInt): ExecState = {
    require(n >= 0)
    copy(pc = pc + n)
  }.ensuring(r => r.pc == pc + n && r.gas == gas && r.status == status)

  def halt: ExecState = {
    copy(status = Status.Halted)
  }.ensuring(r => !r.isRunning && r.gas == gas)

  def revert: ExecState = {
    copy(status = Status.Reverted)
  }.ensuring(r => !r.isRunning && r.gas == gas)

  def fail: ExecState = {
    copy(status = Status.Failed, gas = 0)
  }.ensuring(r => !r.isRunning)
