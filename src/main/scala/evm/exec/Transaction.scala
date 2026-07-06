package evm.exec

import stainless.collection.*
import stainless.lang.*
import evm.value.Word256
import evm.math.Bytes
import evm.math.EvmMath
import evm.state.Storage
import evm.env.{Address, BlockContext, TxContext, MessageContext, WorldState, Log}

case class Transaction(
  origin: Address,
  to: Address,
  value: Word256,
  gasLimit: BigInt,
  maxFeePerGas: Word256,
  maxPriorityFeePerGas: Word256,
  nonce: BigInt,
  data: List[BigInt]
):
  require(gasLimit >= 0 && nonce >= 0)

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

  def tokens(data: List[BigInt]): BigInt = {
    decreases(data)
    data match
      case Nil() => BigInt(0)
      case Cons(b, t) => (if (Bytes.emod256(b) == 0) BigInt(1) else BigInt(4)) + tokens(t)
  }.ensuring(r => r >= 0)

  def intrinsicGas(data: List[BigInt]): BigInt = {
    BigInt(21000) + 4 * tokens(data)
  }.ensuring(r => r >= 21000)

  def floorGas(data: List[BigInt]): BigInt = {
    BigInt(21000) + 10 * tokens(data)
  }.ensuring(r => r >= 21000)

  def effectiveGasPrice(maxFee: Word256, maxPriority: Word256, baseFee: Word256): Word256 = {
    require(baseFee.value <= maxFee.value)
    val cap = maxFee.value - baseFee.value
    val prio = if (maxPriority.value < cap) maxPriority.value else cap
    Word256(baseFee.value + prio)
  }.ensuring(r => baseFee.value <= r.value && r.value <= maxFee.value)

  def settle(tx: Transaction, floor: BigInt, price: Word256, baseFee: Word256,
             coinbase: Address, worldOnFail: WorldState, fin: ExecState): TxResult = {
    require(0 <= floor && floor <= tx.gasLimit
      && baseFee.value <= price.value
      && tx.gasLimit * price.value <= EvmMath.MAX_VALUE)
    val gasUsed0 = if (tx.gasLimit >= fin.gas) tx.gasLimit - fin.gas else BigInt(0)
    val success = fin.status == Status.Halted
    val refund =
      if (success) {
        val cap = gasUsed0 / 5
        val r = if (fin.refund < 0) BigInt(0) else fin.refund
        if (r < cap) r else cap
      } else BigInt(0)
    val afterRefund = gasUsed0 - refund
    val gasUsed = if (afterRefund < floor) floor else afterRefund
    val unused = tx.gasLimit - gasUsed
    val prio = price.value - baseFee.value
    EvmMath.mulNonNeg(unused, price.value)
    EvmMath.mulLeMonoLeft(unused, tx.gasLimit, price.value)
    EvmMath.mulNonNeg(gasUsed, prio)
    EvmMath.mulLeMono(gasUsed, prio, price.value)
    EvmMath.mulLeMonoLeft(gasUsed, tx.gasLimit, price.value)
    val weiRefund = Word256(unused * price.value)
    val tip = Word256(gasUsed * prio)
    val committed =
      if (success) fin.world.withStorage(tx.to, fin.storage) else worldOnFail
    val w1 = committed.withBalance(tx.origin, committed.balanceOf(tx.origin) + weiRefund)
    val w2 = w1.withBalance(coinbase, w1.balanceOf(coinbase) + tip)
    if (success) TxResult(Status.Halted, gasUsed, refund, fin.logs, fin.returnData, w2)
    else if (fin.status == Status.Reverted) TxResult(Status.Reverted, gasUsed, BigInt(0), Nil(), fin.returnData, w2)
    else TxResult(fin.status, gasUsed, BigInt(0), Nil(), Nil(), w2)
  }.ensuring(r => floor <= r.gasUsed && r.gasUsed <= tx.gasLimit && r.gasRefunded >= 0)

  def execTx(tx: Transaction, block: BlockContext, world: WorldState,
             intrinsic: BigInt, floor: BigInt): TxResult = {
    require(0 <= intrinsic && intrinsic <= floor && floor <= tx.gasLimit
      && block.baseFee.value <= tx.maxFeePerGas.value
      && tx.maxPriorityFeePerGas.value <= tx.maxFeePerGas.value
      && world.balanceOf(tx.origin).value >= tx.gasLimit * tx.maxFeePerGas.value + tx.value.value)
    val senderBal = world.balanceOf(tx.origin)
    val price = effectiveGasPrice(tx.maxFeePerGas, tx.maxPriorityFeePerGas, block.baseFee)
    EvmMath.mulNonNeg(tx.gasLimit, price.value)
    EvmMath.mulLeMono(tx.gasLimit, price.value, tx.maxFeePerGas.value)
    val upfront = tx.gasLimit * price.value
    senderBal.bounded
    assert(upfront + tx.value.value <= senderBal.value)
    EvmMath.sumBound(upfront, tx.value.value, senderBal.value)
    val w1 = world.withNonce(tx.origin, tx.nonce + 1)
      .withBalance(tx.origin, Word256(senderBal.value - upfront))
    val w2 = w1.transfer(tx.origin, tx.to, tx.value)
    val execGas = tx.gasLimit - intrinsic
    val txctx = TxContext(tx.origin, price)
    val msg = MessageContext(tx.to, tx.origin, tx.value, tx.data)
    val s = w2.storageOf(tx.to)
    val init = ExecState.initialWith(w2.codeOf(tx.to), execGas, block, txctx, msg, w2)
      .copy(accessedAccounts = precompiles ++ Set(tx.origin, tx.to, block.coinbase),
            storage = s, original = s)
    settle(tx, floor, price, block.baseFee, block.coinbase, w1, Interpreter.run(init))
  }.ensuring(r => 0 <= r.gasUsed && r.gasUsed <= tx.gasLimit && r.gasRefunded >= 0)

  def run(tx: Transaction, block: BlockContext, world: WorldState): TxResult = {
    val t = tokens(tx.data)
    val intrinsic = BigInt(21000) + 4 * t
    val floor = BigInt(21000) + 10 * t
    if (tx.gasLimit < floor)
      TxResult(Status.Failed, tx.gasLimit, BigInt(0), Nil(), Nil(), world)
    else if (block.baseFee.value > tx.maxFeePerGas.value
      || tx.maxPriorityFeePerGas.value > tx.maxFeePerGas.value
      || tx.nonce != world.nonceOf(tx.origin)
      || world.balanceOf(tx.origin).value < tx.gasLimit * tx.maxFeePerGas.value + tx.value.value)
      TxResult(Status.Failed, BigInt(0), BigInt(0), Nil(), Nil(), world)
    else
      execTx(tx, block, world, intrinsic, floor)
  }.ensuring(r => 0 <= r.gasUsed && r.gasUsed <= tx.gasLimit && r.gasRefunded >= 0)
