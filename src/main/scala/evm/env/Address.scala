package evm.env

import evm.math.EvmMath
import evm.math.EvmMath.pow
import evm.value.Word256

object Address:
  val MODULO: BigInt = pow(BigInt(2), BigInt(160))
  def zero: Address = Address(BigInt(0))

  def fromWord(w: Word256): Address = {
    EvmMath.powTwoPos(BigInt(160))
    Address(w.value % MODULO)
  }.ensuring(r => r.value == w.value % MODULO)

case class Address(value: BigInt):
  require(0 <= value && value < Address.MODULO)

  def toWord: Word256 = {
    EvmMath.powMonotone(BigInt(160), BigInt(256))
    Word256(value)
  }.ensuring(r => r.value == value)
