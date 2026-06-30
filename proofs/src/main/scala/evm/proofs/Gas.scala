package evm.proofs

import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*

object Gas {
  val WARM_ACCESS: BigInt  = 100
  val COLD_SLOAD: BigInt   = 2100
  val SSTORE_SET: BigInt   = 20000
  val SSTORE_RESET: BigInt = 5000

  def words(byteLen: BigInt): BigInt = {
    require(byteLen >= 0)
    (byteLen + 31) / 32
  }.ensuring(r => r >= 0 && 32 * r >= byteLen)

  def memoryCost(w: BigInt): BigInt = {
    require(w >= 0)
    3 * w + (w * w) / 512
  }.ensuring(r => r >= 0)

  @ghost
  def sqMonotone(a: BigInt, b: BigInt): Boolean = {
    require(0 <= a && a <= b)
    a * a <= b * b because (a * a <= a * b && a * b <= b * b)
  }.holds

  @ghost
  def memoryCostMonotone(a: BigInt, b: BigInt): Boolean = {
    require(0 <= a && a <= b)
    memoryCost(a) <= memoryCost(b) because sqMonotone(a, b)
  }.holds

  def memoryExpansionCost(oldWords: BigInt, newWords: BigInt): BigInt = {
    require(0 <= oldWords && oldWords <= newWords)
    memoryCostMonotone(oldWords, newWords)
    memoryCost(newWords) - memoryCost(oldWords)
  }.ensuring(r => r >= 0)

  def copyCost(len: BigInt): BigInt = {
    require(len >= 0)
    3 * words(len)
  }.ensuring(r => r >= 0)

  def keccakCost(len: BigInt): BigInt = {
    require(len >= 0)
    30 + 6 * words(len)
  }.ensuring(r => r >= 30)

  def expCost(exponentBytes: BigInt): BigInt = {
    require(exponentBytes >= 0)
    10 + 50 * exponentBytes
  }.ensuring(r => r >= 10)

  def logCost(len: BigInt, topics: BigInt): BigInt = {
    require(len >= 0 && topics >= 0)
    375 + 8 * len + 375 * topics
  }.ensuring(r => r >= 375)

  def accessCost(cold: Boolean): BigInt = {
    if (cold) COLD_SLOAD else WARM_ACCESS
  }.ensuring(r => r >= WARM_ACCESS)

  def sstoreCost(original: BigInt, current: BigInt, value: BigInt, cold: Boolean): BigInt = {
    val base =
      if (value == current) WARM_ACCESS
      else if (original == current) {
        if (original == 0) SSTORE_SET else SSTORE_RESET - COLD_SLOAD
      } else WARM_ACCESS
    base + (if (cold) COLD_SLOAD else BigInt(0))
  }.ensuring(r => r >= WARM_ACCESS)
}
