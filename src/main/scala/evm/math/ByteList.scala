package evm.math

import stainless.collection.*
import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*
import evm.math.EvmMath
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

  // The big-endian digit law: byte j (from the most significant) of the packed
  // value is exactly byteOrZero(l, start+j). Proven by induction on n, peeling the
  // top byte each step; the arithmetic goes through the EvmMath div/mod scaffold so
  // every verification condition stays tractable for the solver.
  @ghost
  def readWordDigit(l: List[BigInt], start: BigInt, n: BigInt, j: BigInt): Boolean = {
    require(start >= 0 && 1 <= n && n <= 32 && 0 <= j && j < n)
    decreases(n)
    val b0 = byteOrZero(l, start)
    val W = readWord(l, start + 1, n - 1)
    ((readWord(l, start, n) / pow(BigInt(256), n - 1 - j)) % 256 == byteOrZero(l, start + j)) because {
      if (j == 0) {
        EvmMath.powPos(BigInt(256), n - 1)
        EvmMath.divAddRemainder(pow(BigInt(256), n - 1), b0, W)
        trivial
      } else {
        val d = pow(BigInt(256), n - 1 - j)
        val p = pow(BigInt(256), j)
        readWordDigit(l, start + 1, n - 1, j - 1) // (W / d) % 256 == byteOrZero(l, start+j)
        EvmMath.powPos(BigInt(256), n - 1 - j)
        EvmMath.powNonNeg(BigInt(256), j)
        EvmMath.powNonNeg(BigInt(256), j - 1)
        EvmMath.mulNonNeg(b0, p)
        EvmMath.mulNonNeg(b0, pow(BigInt(256), j - 1))
        EvmMath.powAdd(BigInt(256), n - 1 - j, j) // pow(256,n-1) == d * p
        assert(readWord(l, start, n) == (b0 * p) * d + W)
        EvmMath.divAddMultiple(d, b0 * p, W) // readWord/d == b0*p + W/d
        assert(b0 * p == 256 * (b0 * pow(BigInt(256), j - 1)))
        val q = readWord(l, start, n) / d
        assert(q == 256 * (b0 * pow(BigInt(256), j - 1)) + W / d)
        // q % 256 == (W/d) % 256 == byteOrZero(l, start+j), proven opaquely.
        EvmMath.digitCombine(q, b0 * pow(BigInt(256), j - 1), W / d, byteOrZero(l, start + j))
        trivial
      }
    }
  }.holds
