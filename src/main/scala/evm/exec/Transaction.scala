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
  world: WorldState
)

object Transaction:

  val precompiles: Set[Address] = Set(
    Address(BigInt(1)), Address(BigInt(2)), Address(BigInt(3)), Address(BigInt(4)),
    Address(BigInt(5)), Address(BigInt(6)), Address(BigInt(7)), Address(BigInt(8)),
    Address(BigInt(9)), Address(BigInt(10)), Address(BigInt(256)))

  // EIP-7623 calldata tokens: 1 per zero byte, 4 per nonzero byte.
  def tokens(data: List[BigInt]): BigInt = {
    decreases(data)
    data match
      case Nil() => BigInt(0)
      case Cons(b, t) => (if (Bytes.emod256(b) == 0) BigInt(1) else BigInt(4)) + tokens(t)
  }.ensuring(r => r >= 0)

  // Standard intrinsic cost: 21000 + 4 per token (= 4 per zero byte, 16 per nonzero).
  def intrinsicGas(data: List[BigInt]): BigInt = {
    BigInt(21000) + 4 * tokens(data)
  }.ensuring(r => r >= 21000)

  // EIP-7623 floor: 21000 + 10 per token; a tx must pay at least this.
  def floorGas(data: List[BigInt]): BigInt = {
    BigInt(21000) + 10 * tokens(data)
  }.ensuring(r => r >= 21000)

  def settle(gasLimit: BigInt, floor: BigInt, to: Address, world: WorldState, fin: ExecState): TxResult = {
    require(gasLimit >= 0 && 0 <= floor && floor <= gasLimit)
    val gasUsed0 = if (gasLimit >= fin.gas) gasLimit - fin.gas else BigInt(0)
    val success = fin.status == Status.Halted
    val refund =
      if (success) {
        val cap = gasUsed0 / 5
        val r = if (fin.refund < 0) BigInt(0) else fin.refund
        if (r < cap) r else cap
      } else BigInt(0)
    val afterRefund = gasUsed0 - refund
    val gasUsed = if (afterRefund < floor) floor else afterRefund
    // On success the recipient's modified storage is committed to the world; a
    // reverted or failed tx leaves the world unchanged (state rolled back).
    if (success) TxResult(Status.Halted, gasUsed, refund, fin.logs, fin.returnData, fin.world.withStorage(to, fin.storage))
    else if (fin.status == Status.Reverted) TxResult(Status.Reverted, gasUsed, BigInt(0), Nil(), fin.returnData, world)
    else TxResult(fin.status, gasUsed, BigInt(0), Nil(), Nil(), world)
  }.ensuring(r => r.gasUsed >= 0 && r.gasRefunded >= 0)

  def run(tx: Transaction, block: BlockContext, world: WorldState): TxResult = {
    val t = tokens(tx.data)
    val intrinsic = BigInt(21000) + 4 * t
    val floor = BigInt(21000) + 10 * t
    if (tx.gasLimit < floor)
      TxResult(Status.Failed, tx.gasLimit, BigInt(0), Nil(), Nil(), world)
    else {
      val execGas = tx.gasLimit - intrinsic
      val txctx = TxContext(tx.origin, tx.gasPrice)
      val msg = MessageContext(tx.to, tx.origin, tx.value, tx.data)
      val s = world.storageOf(tx.to)
      val init = ExecState.initialWith(world.codeOf(tx.to), execGas, block, txctx, msg, world)
        .copy(accessedAccounts = precompiles ++ Set(tx.origin, tx.to, block.coinbase),
              storage = s, original = s)
      settle(tx.gasLimit, floor, tx.to, world, Interpreter.run(init))
    }
  }
