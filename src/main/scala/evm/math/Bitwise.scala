package evm.math

import stainless.lang._
import stainless.annotation._
import stainless.proof._

object Bitwise {
  import EvmMath.{MODULO, MAX_VALUE}

  @extern @pure
  def and(a: BigInt, b: BigInt): BigInt = a & b

  @extern @pure
  def or(a: BigInt, b: BigInt): BigInt = a | b

  @extern @pure
  def xor(a: BigInt, b: BigInt): BigInt = a ^ b

  def not(a: BigInt): BigInt = {
    require(a >= 0 && a <= MAX_VALUE)
    MAX_VALUE - a
  }.ensuring(res => res == MAX_VALUE - a && res >= 0 && res <= MAX_VALUE)

  @extern
  def andBound(a: BigInt, b: BigInt): Unit = {
    require(a >= 0 && b >= 0)
    ()
  }.ensuring(_ => and(a, b) >= 0 && and(a, b) <= a && and(a, b) <= b)

  @extern
  def orBound(a: BigInt, b: BigInt): Unit = {
    require(a >= 0 && a < MODULO && b >= 0 && b < MODULO)
    ()
  }.ensuring(_ => or(a, b) >= 0 && or(a, b) < MODULO && or(a, b) >= a && or(a, b) >= b)

  @extern
  def xorBound(a: BigInt, b: BigInt): Unit = {
    require(a >= 0 && a < MODULO && b >= 0 && b < MODULO)
    ()
  }.ensuring(_ => xor(a, b) >= 0 && xor(a, b) < MODULO)

  @extern
  def andComm(a: BigInt, b: BigInt): Unit = {
    ()
  }.ensuring(_ => and(a, b) == and(b, a))

  @extern
  def orComm(a: BigInt, b: BigInt): Unit = {
    ()
  }.ensuring(_ => or(a, b) == or(b, a))

  @extern
  def xorComm(a: BigInt, b: BigInt): Unit = {
    ()
  }.ensuring(_ => xor(a, b) == xor(b, a))

  @extern
  def andIdem(a: BigInt): Unit = {
    ()
  }.ensuring(_ => and(a, a) == a)

  @extern
  def orIdem(a: BigInt): Unit = {
    ()
  }.ensuring(_ => or(a, a) == a)

  @extern
  def andZero(a: BigInt): Unit = {
    ()
  }.ensuring(_ => and(a, BigInt(0)) == BigInt(0))

  @extern
  def orZero(a: BigInt): Unit = {
    ()
  }.ensuring(_ => or(a, BigInt(0)) == a)

  @extern
  def xorZero(a: BigInt): Unit = {
    ()
  }.ensuring(_ => xor(a, BigInt(0)) == a)

  @extern
  def xorSelf(a: BigInt): Unit = {
    ()
  }.ensuring(_ => xor(a, a) == BigInt(0))

  @extern
  def andAllOnes(a: BigInt): Unit = {
    require(a >= 0 && a <= MAX_VALUE)
    ()
  }.ensuring(_ => and(a, MAX_VALUE) == a)

  @extern
  def orAllOnes(a: BigInt): Unit = {
    require(a >= 0 && a <= MAX_VALUE)
    ()
  }.ensuring(_ => or(a, MAX_VALUE) == MAX_VALUE)

  def notInvolutive(a: BigInt): Boolean = {
    require(a >= 0 && a <= MAX_VALUE)
    not(not(a)) == a
  }.holds
}
