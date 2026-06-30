package evm.proofs

import stainless.lang._
import stainless.annotation._
import stainless.proof._

object EvmMath {
  val MODULO: BigInt    = pow(BigInt(2), BigInt(256))
  val MAX_VALUE: BigInt = MODULO - 1
  val SIGN_BOUND: BigInt = pow(BigInt(2), BigInt(255))

  def pow(base: BigInt, exp: BigInt): BigInt = {
    require(exp >= 0)
    decreases(exp)
    if (exp == 0) BigInt(1)
    else base * pow(base, exp - 1)
  }.ensuring(result => if (exp == 0) result == 1 else result == base * pow(base, exp - 1))

  def inBounds(v: BigInt): Boolean = v >= 0 && v <= MAX_VALUE

  def toSigned(v: BigInt): BigInt = {
    require(v >= 0 && v < MODULO)
    signBoundDoubles
    powTwoPos(BigInt(255))
    if (v < SIGN_BOUND) v else v - MODULO
  }.ensuring(r => r >= -SIGN_BOUND && r < SIGN_BOUND)

  def wrap(s: BigInt): BigInt = {
    moduloPos
    ((s % MODULO) + MODULO) % MODULO
  }.ensuring(r => r >= 0 && r < MODULO)


  @ghost
  def powNonNeg(base: BigInt, exp: BigInt): Boolean = {
    require(base >= 0 && exp >= 0)
    decreases(exp)
    pow(base, exp) >= 0 because {
      if (exp == 0) trivial
      else powNonNeg(base, exp - 1)
    }
  }.holds

  @ghost
  def powTwoPos(n: BigInt): Boolean = {
    require(n >= 0)
    decreases(n)
    pow(BigInt(2), n) > 0 because {
      if (n == 0) trivial
      else powTwoPos(n - 1)
    }
  }.holds

  @ghost
  def moduloPos: Boolean = {
    MODULO > 0 because powTwoPos(BigInt(256))
  }.holds

  @ghost
  def signBoundDoubles: Boolean = {
    MODULO == 2 * SIGN_BOUND
  }.holds

  @ghost
  def toSignedNonZero(v: BigInt): Boolean = {
    require(v > 0 && v < MODULO)
    signBoundDoubles
    toSigned(v) != 0
  }.holds

  @ghost
  def wrapToSignedId(v: BigInt): Boolean = {
    require(v >= 0 && v < MODULO)
    signBoundDoubles
    wrap(toSigned(v)) == v
  }.holds

  @ghost
  def toSignedWrapId(s: BigInt): Boolean = {
    require(s >= -SIGN_BOUND && s < SIGN_BOUND)
    signBoundDoubles
    toSigned(wrap(s)) == s
  }.holds
}
