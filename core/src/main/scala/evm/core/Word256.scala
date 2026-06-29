package evm.core

import stainless.lang._
import stainless.annotation._
import stainless.proof._
import evm.proofs.EvmMath
import evm.proofs.EvmMath.{MODULO, MAX_VALUE, pow}
import evm.proofs.Bitwise

object Word256 {
  val Zero: Word256 = Word256(BigInt(0))
  val One: Word256  = Word256(BigInt(1))

  def inBounds(v: BigInt): Boolean = v >= 0 && v <= MAX_VALUE

  def addmod(a: Word256, b: Word256, n: Word256): Word256 = {
    if (n == Zero) Zero
    else Word256((a.value + b.value) % n.value)
  }.ensuring(result =>
    (if (n == Zero) result.value == BigInt(0)
     else result.value == (a.value + b.value) % n.value)
    && inBounds(result.value))

  def mulmod(a: Word256, b: Word256, n: Word256): Word256 = {
    if (n == Zero) Zero
    else Word256((a.value * b.value) % n.value)
  }.ensuring(result =>
    (if (n == Zero) result.value == BigInt(0)
     else result.value == (a.value * b.value) % n.value)
    && inBounds(result.value))
}

case class Word256(value: BigInt) {
  require(Word256.inBounds(value))

  def +(other: Word256): Word256 = {
    Word256((value + other.value) % MODULO)
  }.ensuring(result =>
    result.value == (value + other.value) % MODULO
    && Word256.inBounds(result.value))

  def -(other: Word256): Word256 = {
    Word256(((value - other.value) + MODULO) % MODULO)
  }.ensuring(result =>
    result.value == (value - other.value + MODULO) % MODULO
    && Word256.inBounds(result.value))

  def *(other: Word256): Word256 = {
    Word256((value * other.value) % MODULO)
  }.ensuring(result =>
    result.value == (value * other.value) % MODULO
    && Word256.inBounds(result.value))

  def /(other: Word256): Word256 = {
    if (other == Word256.Zero) Word256.Zero
    else Word256(value / other.value)
  }.ensuring(result =>
    (if (other == Word256.Zero) result.value == BigInt(0)
     else result.value == value / other.value)
    && Word256.inBounds(result.value))

  def %(other: Word256): Word256 = {
    if (other == Word256.Zero) Word256.Zero
    else Word256(value % other.value)
  }.ensuring(result =>
    (if (other == Word256.Zero) result.value == BigInt(0)
     else result.value == value % other.value)
    && Word256.inBounds(result.value))

  def &(other: Word256): Word256 = {
    Bitwise.andBound(value, other.value)
    Word256(Bitwise.and(value, other.value))
  }.ensuring(result =>
    result.value == Bitwise.and(value, other.value)
    && Word256.inBounds(result.value))

  def |(other: Word256): Word256 = {
    Bitwise.orBound(value, other.value)
    Word256(Bitwise.or(value, other.value))
  }.ensuring(result =>
    result.value == Bitwise.or(value, other.value)
    && Word256.inBounds(result.value))

  def ^(other: Word256): Word256 = {
    Bitwise.xorBound(value, other.value)
    Word256(Bitwise.xor(value, other.value))
  }.ensuring(result =>
    result.value == Bitwise.xor(value, other.value)
    && Word256.inBounds(result.value))

  def unary_~ : Word256 = {
    Word256(Bitwise.not(value))
  }.ensuring(result =>
    result.value == MAX_VALUE - value
    && Word256.inBounds(result.value))

  def **(exp: Word256): Word256 = {
    EvmMath.powNonNeg(value, exp.value)
    Word256(pow(value, exp.value) % MODULO)
  }.ensuring(result =>
    result.value == pow(value, exp.value) % MODULO
    && Word256.inBounds(result.value))

  def <<(shift: Word256): Word256 = {
    EvmMath.powNonNeg(BigInt(2), shift.value)
    if (shift.value >= BigInt(256)) Word256.Zero
    else Word256((value * pow(BigInt(2), shift.value)) % MODULO)
  }.ensuring(result =>
    (if (shift.value >= BigInt(256)) result.value == BigInt(0)
     else result.value == (value * pow(BigInt(2), shift.value)) % MODULO)
    && Word256.inBounds(result.value))

  def >>(shift: Word256): Word256 = {
    EvmMath.powTwoPos(shift.value)
    if (shift.value >= BigInt(256)) Word256.Zero
    else Word256(value / pow(BigInt(2), shift.value))
  }.ensuring(result =>
    (if (shift.value >= BigInt(256)) result.value == BigInt(0)
     else result.value == value / pow(BigInt(2), shift.value))
    && Word256.inBounds(result.value))
}