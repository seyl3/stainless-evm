package evm.exec

import stainless.collection.*
import stainless.lang.*
import evm.code.Code
import evm.value.Word256
import evm.state.{Stack, Memory, Storage}
import evm.env.{Address, BlockContext, TxContext, MessageContext, WorldState, Log}

// The outcome of a frame: still Running, or Halted (STOP/RETURN), Reverted
// (REVERT), or Failed (out of gas / invalid). Only Running frames keep stepping.
enum Status:
  case Running
  case Halted
  case Reverted
  case Failed

// The full machine state of one call frame. Everything the interpreter reads or
// writes lives here: stack/memory/storage/transient, pc/gas/depth, the static
// flag and status, return data, the block/tx/message context and world, the
// EIP-2929 accessed sets, `original` storage (start-of-tx values for SSTORE),
// emitted logs, and the refund counter.
object ExecState:
  val MAX_DEPTH: BigInt = 1024

  def initial(code: Code, gas: BigInt): ExecState = {
    require(gas >= 0)
    initialWith(code, gas, BlockContext.empty, TxContext.empty, MessageContext.empty, WorldState.empty)
  }

  def initialWith(code: Code, gas: BigInt, block: BlockContext, tx: TxContext, msg: MessageContext, world: WorldState): ExecState = {
    require(gas >= 0)
    ExecState(code, Stack.empty, Memory.empty, Storage.empty, Storage.empty,
      BigInt(0), gas, BigInt(0), false, Status.Running, Nil(), block, tx, msg, world,
      Set.empty[Address], Storage.empty, Set.empty[Word256], Nil(), BigInt(0))
  }

  // A fresh child call frame: empty stack/memory/transient at pc 0, the callee's
  // code and storage, the forwarded gas, and depth+1. Warm accounts are inherited
  // from the parent (EIP-2929 accessed set is transaction-global).
  def subFrame(code: Code, self: Address, caller: Address, value: Word256, callData: List[BigInt],
               gas: BigInt, depth: BigInt, static: Boolean, block: BlockContext, tx: TxContext,
               world: WorldState, storage: Storage, original: Storage, accessedAccounts: Set[Address]): ExecState = {
    require(gas >= 0 && depth >= 0 && depth <= MAX_DEPTH)
    ExecState(code, Stack.empty, Memory.empty, storage, Storage.empty, BigInt(0), gas, depth, static,
      Status.Running, Nil(), block, tx, MessageContext(self, caller, value, callData), world,
      accessedAccounts, original, Set.empty[Word256], Nil(), BigInt(0))
  }.ensuring(r => r.gas == gas && r.depth == depth && r.isRunning)

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
  returnData: List[BigInt],
  block: BlockContext,
  tx: TxContext,
  msg: MessageContext,
  world: WorldState,
  accessedAccounts: Set[Address],
  original: Storage,
  accessedSlots: Set[Word256],
  logs: List[Log],
  refund: BigInt
):
  require(pc >= 0 && gas >= 0 && depth >= 0 && depth <= ExecState.MAX_DEPTH)

  def isRunning: Boolean = status == Status.Running

  def outOfGas(cost: BigInt): Boolean = {
    require(cost >= 0)
    cost > gas
  }

  // The state transitions below each return `copy(...)` and expose that exact copy
  // in their postcondition. This transparency lets a caller that chains them (for
  // example chargeGas then advancePc) know precisely which single field changed,
  // which the solver needs to carry the other fields' values through.
  def chargeGas(cost: BigInt): ExecState = {
    require(cost >= 0 && cost <= gas)
    copy(gas = gas - cost)
  }.ensuring(r => r == copy(gas = gas - cost) && r.gas >= 0)

  def advancePc(n: BigInt): ExecState = {
    require(n >= 0)
    copy(pc = pc + n)
  }.ensuring(r => r == copy(pc = pc + n))

  def halt: ExecState = {
    copy(status = Status.Halted)
  }.ensuring(r => r == copy(status = Status.Halted))

  def revert: ExecState = {
    copy(status = Status.Reverted)
  }.ensuring(r => r == copy(status = Status.Reverted))

  def fail: ExecState = {
    copy(status = Status.Failed, gas = 0)
  }.ensuring(r => r == copy(status = Status.Failed, gas = 0))
