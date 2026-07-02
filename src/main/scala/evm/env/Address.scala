package evm.env

import evm.math.EvmMath.pow

object Address:
  val MODULO: BigInt = pow(BigInt(2), BigInt(160))
  def zero: Address = Address(BigInt(0))

case class Address(value: BigInt):
  require(0 <= value && value < Address.MODULO)
