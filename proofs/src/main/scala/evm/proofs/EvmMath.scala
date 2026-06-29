package evm.proofs

import stainless.lang._
import stainless.annotation._
import stainless.proof._

object EvmMath {
  val MODULO: BigInt    = pow(BigInt(2), BigInt(256))
  val MAX_VALUE: BigInt = MODULO - 1

  def pow(base: BigInt, exp: BigInt): BigInt = {
    require(exp >= 0)
    decreases(exp)
    if (exp == 0) BigInt(1)
    else base * pow(base, exp - 1)
  }.ensuring(result => if (exp == 0) result == 1 else result == base * pow(base, exp - 1))

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
}
