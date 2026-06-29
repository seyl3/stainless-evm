package evm.core

import stainless.lang._
import stainless.annotation._

object Word256 {
  val MODULO : BigInt = pow(BigInt(2), BigInt(256))
  val MAX_VALUE : BigInt = MODULO - 1
  val Zero : Word256 = Word256(BigInt(0))
  val One : Word256 = Word256(BigInt(1))

  def pow(base: BigInt, exp: BigInt): BigInt = {
  require(exp >= 0)
  decreases(exp)
  if (exp == 0) then BigInt(1)
  else base * pow(base, exp - 1)
  }.ensuring(result => if (exp == 0) result == 1 else result == base * pow(base, exp - 1))

  def inBounds(v: BigInt): Boolean = v >= 0 && v <= MAX_VALUE
}

case class Word256(value: BigInt) {
    require(Word256.inBounds(value))

    def +(other: Word256): Word256 = {
        Word256((value + other.value) % Word256.MODULO)
    }.ensuring(result => result.value == (value + other.value) % Word256.MODULO
            && Word256.inBounds(result.value))

    def -(other: Word256): Word256 = {
        Word256(((value - other.value) + Word256.MODULO) % Word256.MODULO)
    }.ensuring(result => result.value == (value - other.value + Word256.MODULO) % Word256.MODULO
            && Word256.inBounds(result.value))

    def *(other: Word256): Word256 = {
        Word256((value * other.value) % Word256.MODULO)
    }.ensuring(result => result.value == (value * other.value) % Word256.MODULO
            && Word256.inBounds(result.value))

    def /(other: Word256): Word256 = {
        if(other == Word256.Zero) then Word256.Zero
        else Word256(value / other.value)
    }.ensuring(result =>
        (if (other == Word256.Zero) result.value == BigInt(0)
         else result.value == (value / other.value))
        && Word256.inBounds(result.value))

    def %(other: Word256): Word256 = {
        if(other == Word256.Zero) then Word256.Zero
        else Word256(value % other.value)
    }.ensuring(result =>
        (if (other == Word256.Zero) result.value == BigInt(0)
         else result.value == value % other.value)
        && Word256.inBounds(result.value))

    @extern
    def &(other: Word256): Word256 = {
        Word256(value & other.value)
    }.ensuring(result => Word256.inBounds(result.value))

    @extern
    def |(other: Word256): Word256 = {
        Word256(value | other.value)
    }.ensuring(result => Word256.inBounds(result.value))

    @extern
    def ^(other: Word256): Word256 = {
        Word256(value ^ other.value)
    }.ensuring(result => Word256.inBounds(result.value))

    def unary_~ : Word256 = {
        Word256(Word256.MAX_VALUE - value)
    }.ensuring(result => Word256.inBounds(result.value))
}


