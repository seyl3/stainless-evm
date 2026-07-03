package evm.exec

import stainless.collection.*
import stainless.lang.*
import evm.value.Word256
import evm.math.Bytes
import evm.state.Storage
import evm.env.{Address, BlockContext, TxContext, MessageContext, WorldState, Log}

case class Transaction(
  origin: Address,
  to: Address,
  value: Word256,
  gasLimit: BigInt,
  gasPrice: Word256,
  data: List[BigInt]
):
  require(gasLimit >= 0)

case class TxResult(
  status: Status,
  gasUsed: BigInt,
  gasRefunded: BigInt,
  logs: List[Log],
  returnData: List[BigInt],
  storage: Storage
)

object Transaction:

  def dataGas(data: List[BigInt]): BigInt = {
    decreases(data)
    data match
      case Nil() => BigInt(0)
      case Cons(b, t) => (if (Bytes.emod256(b) == 0) BigInt(4) else BigInt(16)) + dataGas(t)
  }.ensuring(r => r >= 0)

  def intrinsicGas(data: List[BigInt]): BigInt = {
    BigInt(21000) + dataGas(data)
  }.ensuring(r => r >= 21000)

  def settle(gasLimit: BigInt, fin: ExecState): TxResult = {
    require(gasLimit >= 0)
    val gasUsed0 = if (gasLimit >= fin.gas) gasLimit - fin.gas else BigInt(0)
    val success = fin.status == Status.Halted
    val refund =
      if (success) {
        val cap = gasUsed0 / 5
        val r = if (fin.refund < 0) BigInt(0) else fin.refund
        if (r < cap) r else cap
      } else BigInt(0)
    val gasUsed = gasUsed0 - refund
    if (success) TxResult(Status.Halted, gasUsed, refund, fin.logs, fin.returnData, fin.storage)
    else if (fin.status == Status.Reverted) TxResult(Status.Reverted, gasUsed0, BigInt(0), Nil(), fin.returnData, Storage.empty)
    else TxResult(fin.status, gasUsed0, BigInt(0), Nil(), Nil(), Storage.empty)
  }.ensuring(r => r.gasUsed >= 0 && r.gasRefunded >= 0)

  def run(tx: Transaction, block: BlockContext, world: WorldState): TxResult = {
    val intrinsic = intrinsicGas(tx.data)
    if (tx.gasLimit < intrinsic)
      TxResult(Status.Failed, tx.gasLimit, BigInt(0), Nil(), Nil(), Storage.empty)
    else {
      val execGas = tx.gasLimit - intrinsic
      val txctx = TxContext(tx.origin, tx.gasPrice)
      val msg = MessageContext(tx.to, tx.origin, tx.value, tx.data)
      val init = ExecState.initialWith(world.codeOf(tx.to), execGas, block, txctx, msg, world)
      settle(tx.gasLimit, Interpreter.run(init))
    }
  }
