package evm.value

import stainless.lang._
import stainless.annotation._
import stainless.proof._
import evm.math.EvmMath
import evm.math.EvmMath.{MODULO, MAX_VALUE, pow, inBounds}
import evm.math.Bitwise

// Companion holding constants and the three-operand modular ops (ADDMOD, MULMOD),
// which take an explicit modulus rather than the implicit 2^256 of the binary ops.
object Word256 {
  val Zero: Word256 = Word256(BigInt(0))
  val One: Word256  = Word256(BigInt(1))

  // (a + b) mod n, or zero when n == 0, matching ADDMOD.
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

// The 256-bit EVM word: a BigInt pinned to [0, 2^256) by the class invariant.
// Every operation carries an exact-value postcondition (not just a bounds check),
// so the interpreter reasons about results, not only their range. Unsigned binary
// ops wrap mod 2^256; signed ops (sdiv/smod/slt/sgt/sar) go through EvmMath's
// two's-complement toSigned/wrap; bitwise ops delegate to the Bitwise axioms.
case class Word256(value: BigInt) {
  require(inBounds(value))

  // Re-exposes the class invariant as an invokable fact, so callers can obtain
  // value <= MAX_VALUE without the solver unfolding wherever this word came from
  // (for example a Map lookup). See the Transaction fee bounds.
  @ghost
  def bounded: Boolean = {
    value >= 0 && value <= MAX_VALUE
  }.holds

  def +(other: Word256): Word256 = {
    Word256((value + other.value) % MODULO)
  }.ensuring(result =>
    result.value == (value + other.value) % MODULO
    && inBounds(result.value))

  def -(other: Word256): Word256 = {
    Word256(((value - other.value) + MODULO) % MODULO)
  }.ensuring(result =>
    result.value == (value - other.value + MODULO) % MODULO
    && inBounds(result.value))

  def *(other: Word256): Word256 = {
    Word256((value * other.value) % MODULO)
  }.ensuring(result =>
    result.value == (value * other.value) % MODULO
    && inBounds(result.value))

  def /(other: Word256): Word256 = {
    if (other == Word256.Zero) Word256.Zero
    else Word256(value / other.value)
  }.ensuring(result =>
    (if (other == Word256.Zero) result.value == BigInt(0)
     else result.value == value / other.value)
    && inBounds(result.value))

  def %(other: Word256): Word256 = {
    if (other == Word256.Zero) Word256.Zero
    else Word256(value % other.value)
  }.ensuring(result =>
    (if (other == Word256.Zero) result.value == BigInt(0)
     else result.value == value % other.value)
    && inBounds(result.value))

  // Signed division (and smod below): interpret both operands as two's-complement,
  // divide, then wrap back. toSignedNonZero proves the signed divisor is nonzero.
  def sdiv(other: Word256): Word256 = {
    if (other == Word256.Zero) Word256.Zero
    else {
      EvmMath.toSignedNonZero(other.value)
      Word256(EvmMath.wrap(EvmMath.toSigned(value) / EvmMath.toSigned(other.value)))
    }
  }.ensuring(result =>
    (if (other == Word256.Zero) result.value == BigInt(0)
     else result.value == EvmMath.wrap(EvmMath.toSigned(value) / EvmMath.toSigned(other.value)))
    && inBounds(result.value))

  def smod(other: Word256): Word256 = {
    if (other == Word256.Zero) Word256.Zero
    else {
      EvmMath.toSignedNonZero(other.value)
      Word256(EvmMath.wrap(EvmMath.toSigned(value) % EvmMath.toSigned(other.value)))
    }
  }.ensuring(result =>
    (if (other == Word256.Zero) result.value == BigInt(0)
     else result.value == EvmMath.wrap(EvmMath.toSigned(value) % EvmMath.toSigned(other.value)))
    && inBounds(result.value))

  // Bitwise ops delegate to the uninterpreted Bitwise functions; the *Bound axioms
  // discharge that the result stays a valid 256-bit word.
  def &(other: Word256): Word256 = {
    Bitwise.andBound(value, other.value)
    Word256(Bitwise.and(value, other.value))
  }.ensuring(result =>
    result.value == Bitwise.and(value, other.value)
    && inBounds(result.value))

  def |(other: Word256): Word256 = {
    Bitwise.orBound(value, other.value)
    Word256(Bitwise.or(value, other.value))
  }.ensuring(result =>
    result.value == Bitwise.or(value, other.value)
    && inBounds(result.value))

  def ^(other: Word256): Word256 = {
    Bitwise.xorBound(value, other.value)
    Word256(Bitwise.xor(value, other.value))
  }.ensuring(result =>
    result.value == Bitwise.xor(value, other.value)
    && inBounds(result.value))

  def unary_~ : Word256 = {
    Word256(Bitwise.not(value))
  }.ensuring(result =>
    result.value == MAX_VALUE - value
    && inBounds(result.value))

  // Modular exponentiation (EXP). powNonNeg gives the solver pow(value, exp) >= 0.
  def **(exp: Word256): Word256 = {
    EvmMath.powNonNeg(value, exp.value)
    Word256(pow(value, exp.value) % MODULO)
  }.ensuring(result =>
    result.value == pow(value, exp.value) % MODULO
    && inBounds(result.value))

  // Shifts (SHL/SHR/SAR): a shift of 256 or more yields zero (or all-ones for a
  // negative SAR). SHL/SHR model the shift as multiply/divide by 2^shift; the pow
  // lemmas supply positivity of the divisor/factor. SAR uses signed floorDiv.
  def shl(shift: Word256): Word256 = {
    EvmMath.powNonNeg(BigInt(2), shift.value)
    if (shift.value >= BigInt(256)) Word256.Zero
    else Word256((value * pow(BigInt(2), shift.value)) % MODULO)
  }.ensuring(result =>
    (if (shift.value >= BigInt(256)) result.value == BigInt(0)
     else result.value == (value * pow(BigInt(2), shift.value)) % MODULO)
    && inBounds(result.value))

  def shr(shift: Word256): Word256 = {
    EvmMath.powTwoPos(shift.value)
    if (shift.value >= BigInt(256)) Word256.Zero
    else Word256(value / pow(BigInt(2), shift.value))
  }.ensuring(result =>
    (if (shift.value >= BigInt(256)) result.value == BigInt(0)
     else result.value == value / pow(BigInt(2), shift.value))
    && inBounds(result.value))

  def sar(shift: Word256): Word256 = {
    EvmMath.moduloPos
    if (shift.value >= BigInt(256))
      (if (EvmMath.toSigned(value) >= 0) Word256.Zero else Word256(MAX_VALUE))
    else {
      EvmMath.powTwoPos(shift.value)
      Word256(EvmMath.wrap(EvmMath.floorDiv(EvmMath.toSigned(value), pow(BigInt(2), shift.value))))
    }
  }.ensuring(result =>
    (if (shift.value >= BigInt(256))
       (if (EvmMath.toSigned(value) >= 0) result.value == BigInt(0) else result.value == MAX_VALUE)
     else result.value == EvmMath.wrap(EvmMath.floorDiv(EvmMath.toSigned(value), pow(BigInt(2), shift.value))))
    && inBounds(result.value))

  // BYTE: extract byte i (0 = most significant) by shifting it down and masking to
  // 8 bits; zero if i >= 32. The pow lemmas bound the shift amount and the mask.
  def byte(i: Word256): Word256 = {
    if (i.value >= BigInt(32)) Word256.Zero
    else {
      val sh = BigInt(8) * (BigInt(31) - i.value)
      EvmMath.powTwoPos(sh)
      EvmMath.powTwoPos(BigInt(8))
      EvmMath.powMonotone(BigInt(8), BigInt(256))
      Word256((value / pow(BigInt(2), sh)) % pow(BigInt(2), BigInt(8)))
    }
  }.ensuring(result =>
    (if (i.value >= BigInt(32)) result.value == BigInt(0)
     else result.value == (value / pow(BigInt(2), BigInt(8) * (BigInt(31) - i.value))) % pow(BigInt(2), BigInt(8)))
    && inBounds(result.value))

  // SIGNEXTEND: treat the low (b+1) bytes as a signed value and extend its sign
  // bit through the high bytes; a no-op when b >= 31. The pow lemmas bound the
  // mask `m` and the sign-bit position.
  def signextend(b: Word256): Word256 = {
    if (b.value >= BigInt(31)) this
    else {
      val bits = BigInt(8) * (b.value + 1)
      EvmMath.powTwoPos(bits)
      EvmMath.powTwoPos(bits - 1)
      EvmMath.powMonotone(bits, BigInt(256))
      val m   = pow(BigInt(2), bits)
      val low = value % m
      val sign = (value / pow(BigInt(2), bits - 1)) % 2
      Word256(if (sign == 1) low + (MODULO - m) else low)
    }
  }.ensuring(result =>
    (if (b.value >= BigInt(31)) result.value == value
     else result.value ==
       (if ((value / pow(BigInt(2), BigInt(8) * (b.value + 1) - 1)) % 2 == 1)
          (value % pow(BigInt(2), BigInt(8) * (b.value + 1))) + (MODULO - pow(BigInt(2), BigInt(8) * (b.value + 1)))
        else value % pow(BigInt(2), BigInt(8) * (b.value + 1))))
    && inBounds(result.value))

  // CLZ (EIP-7939): number of leading zero bits over 256 bits (256 when zero).
  def clz: Word256 = {
    EvmMath.n256InBounds
    Word256(EvmMath.clzWidth(value, BigInt(256)))
  }.ensuring(result =>
    result.value == EvmMath.clzWidth(value, BigInt(256))
    && inBounds(result.value))

  def isZero: Boolean = value == BigInt(0)
  def lt(other: Word256): Boolean = value < other.value
  def gt(other: Word256): Boolean = value > other.value
  def slt(other: Word256): Boolean =
    EvmMath.toSigned(value) < EvmMath.toSigned(other.value)
  def sgt(other: Word256): Boolean =
    EvmMath.toSigned(value) > EvmMath.toSigned(other.value)
}