package evm.env

import stainless.collection.*
import evm.value.Word256

object BlockContext:
  def empty: BlockContext = BlockContext(Address.zero, Word256.Zero, Word256.Zero,
    Word256.Zero, Word256.Zero, Word256.Zero, Word256.Zero, Word256.Zero)

case class BlockContext(
  coinbase: Address,
  timestamp: Word256,
  number: Word256,
  prevrandao: Word256,
  gasLimit: Word256,
  chainId: Word256,
  baseFee: Word256,
  blobBaseFee: Word256
)

object TxContext:
  def empty: TxContext = TxContext(Address.zero, Word256.Zero)

case class TxContext(
  origin: Address,
  gasPrice: Word256
)

object MessageContext:
  def empty: MessageContext = MessageContext(Address.zero, Address.zero, Word256.Zero, Nil())

case class MessageContext(
  self: Address,
  caller: Address,
  callValue: Word256,
  callData: List[BigInt]
)
