package evm.math

import stainless.collection.*
import stainless.lang.*
import evm.math.EvmMath.pow

object ByteList:

  def byteOrZero(l: List[BigInt], i: BigInt): BigInt = {
    require(i >= 0)
    if (i < l.size) Bytes.emod256(l(i)) else BigInt(0)
  }.ensuring(r => 0 <= r && r < 256)

  def readWord(l: List[BigInt], start: BigInt, n: BigInt): BigInt = {
    require(start >= 0 && 0 <= n && n <= 32)
    decreases(n)
    if (n == 0) BigInt(0)
    else byteOrZero(l, start) * pow(BigInt(256), n - 1) + readWord(l, start + 1, n - 1)
  }.ensuring(r => 0 <= r && r < pow(BigInt(256), n))
