package evm.math

import stainless.collection.*
import stainless.lang.*
import evm.math.EvmMath.pow

// Big-endian reads over a byte list (the model of calldata, which is a
// List[BigInt] rather than the sparse Map used for memory). Reads past the end
// yield zero bytes, matching EVM calldata semantics.
object ByteList:

  // The byte at index i, or zero if i is past the end.
  def byteOrZero(l: List[BigInt], i: BigInt): BigInt = {
    require(i >= 0)
    if (i < l.size) Bytes.emod256(l(i)) else BigInt(0)
  }.ensuring(r => 0 <= r && r < 256)

  // The big-endian integer packed from the n bytes starting at `start` (the
  // value CALLDATALOAD pushes). Missing tail bytes read as zero.
  def readWord(l: List[BigInt], start: BigInt, n: BigInt): BigInt = {
    require(start >= 0 && 0 <= n && n <= 32)
    decreases(n)
    if (n == 0) BigInt(0)
    else byteOrZero(l, start) * pow(BigInt(256), n - 1) + readWord(l, start + 1, n - 1)
  }.ensuring(r => 0 <= r && r < pow(BigInt(256), n))
