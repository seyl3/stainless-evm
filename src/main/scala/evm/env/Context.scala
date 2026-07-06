package evm.env

import stainless.collection.*
import stainless.lang.*
import evm.value.Word256

// Read-only execution context, split three ways: BlockContext (per block),
// TxContext (per transaction), MessageContext (per call frame). These back the
// environment opcodes (COINBASE, TIMESTAMP, ORIGIN, CALLER, CALLVALUE, ...).
object BlockContext:
  def empty: BlockContext = BlockContext(Address.zero, Word256.Zero, Word256.Zero,
    Word256.Zero, Word256.Zero, Word256.Zero, Word256.Zero, Word256.Zero, Map.empty[Word256, Word256])

case class BlockContext(
  coinbase: Address,
  timestamp: Word256,
  number: Word256,
  prevrandao: Word256,
  gasLimit: Word256,
  chainId: Word256,
  baseFee: Word256,
  blobBaseFee: Word256,
  blockHashes: Map[Word256, Word256]
):
  // BLOCKHASH: the hash of a block, available only for the last 256 blocks before
  // the current one; otherwise zero.
  def blockHash(num: Word256): Word256 =
    if (num.value < number.value && num.value + 256 >= number.value && blockHashes.contains(num))
      blockHashes(num)
    else Word256.Zero

object TxContext:
  def empty: TxContext = TxContext(Address.zero, Word256.Zero, Nil())
  def apply(origin: Address, gasPrice: Word256): TxContext = TxContext(origin, gasPrice, Nil())

case class TxContext(
  origin: Address,
  gasPrice: Word256,
  blobHashes: List[Word256]
):
  // BLOBHASH: the versioned hash at the given index, or zero if out of range.
  def blobHash(idx: Word256): Word256 =
    if (idx.value < blobHashes.size) blobHashes(idx.value) else Word256.Zero

// The current call frame: the executing account (self), its caller, the value
// sent with the call, and the input data. A CALL/DELEGATECALL builds a fresh one.
object MessageContext:
  def empty: MessageContext = MessageContext(Address.zero, Address.zero, Word256.Zero, Nil())

case class MessageContext(
  self: Address,
  caller: Address,
  callValue: Word256,
  callData: List[BigInt]
)
