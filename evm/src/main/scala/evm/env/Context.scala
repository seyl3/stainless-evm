package evm.env

import stainless.collection.*
import evm.core.Word256

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

case class TxContext(
  origin: Address,
  gasPrice: Word256
)

case class MessageContext(
  self: Address,
  caller: Address,
  callValue: Word256,
  callData: List[BigInt]
)
