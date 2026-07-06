package evm.math

import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*

// Pure gas-pricing formulas (Osaka rules). Type-free so it stays in the theory
// layer; the interpreter combines these with per-opcode base costs. Each formula
// carries a non-negativity (or lower-bound) postcondition so callers never have
// to reprove that gas charges cannot go negative.
object Gas {
  val WARM_ACCESS: BigInt  = 100
  val COLD_SLOAD: BigInt   = 2100
  val SSTORE_SET: BigInt   = 20000
  val SSTORE_RESET: BigInt = 5000

  // Number of 32-byte words spanning `byteLen` bytes (ceiling division).
  def words(byteLen: BigInt): BigInt = {
    require(byteLen >= 0)
    (byteLen + 31) / 32
  }.ensuring(r => r >= 0 && 32 * r >= byteLen)

  // Total cost of holding `w` active memory words: linear plus a quadratic term.
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

  // Marginal cost of growing memory from oldWords to newWords. The monotonicity
  // lemma proves the difference is non-negative (the quadratic term is nonlinear,
  // so the solver needs the hint).
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

  // EIP-2200/2929 SSTORE charge. `original` is the slot value at the start of the
  // tx, `current` its present value, `value` the value being written. A no-op
  // write is warm-priced; first-touch of a clean slot pays set (20000, from zero)
  // or reset (5000 minus the cold surcharge); dirty writes are warm. The cold
  // surcharge is added on top when the slot has not been accessed this tx.
  def sstoreCost(original: BigInt, current: BigInt, value: BigInt, cold: Boolean): BigInt = {
    val base =
      if (value == current) WARM_ACCESS
      else if (original == current) {
        if (original == 0) SSTORE_SET else SSTORE_RESET - COLD_SLOAD
      } else WARM_ACCESS
    base + (if (cold) COLD_SLOAD else BigInt(0))
  }.ensuring(r => r >= WARM_ACCESS)

  val SSTORE_CLEARS: BigInt = 4800

  // EIP-3529 SSTORE refund counter delta (can be negative when a dirty slot
  // crosses zero). `cross` accounts for clearing/unclearing a nonzero slot;
  // `reset` credits restoring a dirty slot back to its original value.
  def sstoreRefund(original: BigInt, current: BigInt, value: BigInt): BigInt = {
    if (value == current) BigInt(0)
    else if (current == original) {
      if (original != 0 && value == 0) SSTORE_CLEARS else BigInt(0)
    } else {
      val cross =
        if (original != 0) {
          if (current == 0) -SSTORE_CLEARS
          else if (value == 0) SSTORE_CLEARS
          else BigInt(0)
        } else BigInt(0)
      val reset =
        if (value == original) {
          if (original == 0) SSTORE_SET - WARM_ACCESS else SSTORE_RESET - COLD_SLOAD - WARM_ACCESS
        } else BigInt(0)
      cross + reset
    }
  }.ensuring(r => r >= -SSTORE_CLEARS)
}
