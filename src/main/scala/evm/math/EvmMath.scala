package evm.math

import stainless.lang._
import stainless.annotation._
import stainless.proof._

// Number theory for 256-bit EVM arithmetic: the modulus, exponentiation, byte
// length, signed interpretation, and the inductive lemmas the solver needs (it
// cannot do induction or nonlinear reasoning itself). Type-free foundation layer.
object EvmMath {
  val MODULO: BigInt    = pow(BigInt(2), BigInt(256)) // 2^256, the wrap-around modulus
  val MAX_VALUE: BigInt = MODULO - 1                  // largest 256-bit value
  val SIGN_BOUND: BigInt = pow(BigInt(2), BigInt(255)) // first negative value in two's-complement

  // base^exp by structural recursion on exp (an executable definition the lemmas
  // reason about, not fast exponentiation).
  def pow(base: BigInt, exp: BigInt): BigInt = {
    require(exp >= 0)
    decreases(exp)
    if (exp == 0) BigInt(1)
    else base * pow(base, exp - 1)
  }.ensuring(res => (base >= 0 ==> res >= 0) && (base >= 1 ==> res >= 1))

  // Minimal number of base-256 digits of v (0 for v == 0); the EXP exponent size.
  def byteLength(v: BigInt): BigInt = {
    require(v >= 0)
    decreases(v)
    if (v == 0) BigInt(0) else 1 + byteLength(v / 256)
  }.ensuring(r => r >= 0)

  // The Word256 range predicate, reused as the class invariant.
  def inBounds(v: BigInt): Boolean = v >= 0 && v <= MAX_VALUE

  // Two's-complement reading of an unsigned 256-bit value into [-2^255, 2^255).
  // The lemma calls give the solver 2^255 > 0 and MODULO == 2*SIGN_BOUND, which
  // it needs to place the branch cut.
  def toSigned(v: BigInt): BigInt = {
    require(v >= 0 && v < MODULO)
    signBoundDoubles
    powTwoPos(BigInt(255))
    if (v < SIGN_BOUND) v else v - MODULO
  }.ensuring(r => r >= -SIGN_BOUND && r < SIGN_BOUND)

  // Reduce any integer into [0, MODULO); inverse of toSigned. moduloPos supplies
  // MODULO > 0 so the modulo is well defined.
  def wrap(s: BigInt): BigInt = {
    moduloPos
    ((s % MODULO) + MODULO) % MODULO
  }.ensuring(r => r >= 0 && r < MODULO)

  // Floor division (rounds toward negative infinity), unlike Scala's truncating
  // `/`. Used where signed semantics need mathematical floor.
  def floorDiv(a: BigInt, b: BigInt): BigInt = {
    require(b > 0)
    val q = a / b
    if (a >= 0 || q * b == a) q else q - 1
  }.ensuring(r => r * b <= a && a < (r + 1) * b)

  // Count-leading-zeros of a width-bit value (the CLZ opcode, EIP-7939). The
  // postcondition pins the exact result via the bit-position bracketing.
  def clzWidth(v: BigInt, width: BigInt): BigInt = {
    require(v >= 0 && width >= 0 && v < pow(BigInt(2), width))
    decreases(width)
    if (width == 0) BigInt(0)
    else if (v >= pow(BigInt(2), width - 1)) BigInt(0)
    else 1 + clzWidth(v, width - 1)
  }.ensuring(r =>
    0 <= r && r <= width
    && v < pow(BigInt(2), width - r)
    && (r < width ==> v >= pow(BigInt(2), width - r - 1)))

  // Inductive lemmas below. Each is a recursive Boolean proof (`.holds`) that the
  // termination checker validates, invoked as a ghost statement wherever the SMT
  // solver needs the fact. `@ghost` means they are erased from compiled bytecode.
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

  @ghost
  def powMonotone(a: BigInt, b: BigInt): Boolean = {
    require(0 <= a && a <= b)
    decreases(b - a)
    pow(BigInt(2), a) <= pow(BigInt(2), b) because {
      if (a == b) trivial
      else powMonotone(a, b - 1) && powTwoPos(b - 1)
    }
  }.holds

  @ghost
  def n256InBounds: Boolean = {
    inBounds(BigInt(256)) because
      (powMonotone(BigInt(9), BigInt(256)) && pow(BigInt(2), BigInt(9)) == 512)
  }.holds

  @ghost
  def powPos(base: BigInt, exp: BigInt): Boolean = {
    require(base > 0 && exp >= 0)
    decreases(exp)
    pow(base, exp) > 0 because {
      if (exp == 0) trivial
      else powPos(base, exp - 1)
    }
  }.holds

  @ghost
  def powAdd(base: BigInt, a: BigInt, b: BigInt): Boolean = {
    require(a >= 0 && b >= 0)
    decreases(b)
    pow(base, a + b) == pow(base, a) * pow(base, b) because {
      if (b == 0) trivial
      else powAdd(base, a, b - 1)
    }
  }.holds

  @ghost
  def powPow(base: BigInt, i: BigInt, j: BigInt): Boolean = {
    require(i >= 0 && j >= 0)
    decreases(j)
    pow(pow(base, i), j) == pow(base, i * j) because {
      if (j == 0) trivial
      else powPow(base, i, j - 1) && powAdd(base, i, i * (j - 1))
    }
  }.holds

  @ghost
  def pow256_32: Boolean = {
    pow(BigInt(256), BigInt(32)) == MODULO because
      (powPow(BigInt(2), BigInt(8), BigInt(32)) && pow(BigInt(2), BigInt(8)) == 256)
  }.holds

  @ghost
  def powMono(base: BigInt, a: BigInt, b: BigInt): Boolean = {
    require(base >= 1 && 0 <= a && a <= b)
    decreases(b - a)
    pow(base, a) <= pow(base, b) because {
      if (a == b) trivial
      else powMono(base, a, b - 1) && powPos(base, b - 1)
    }
  }.holds

  // Nonlinear helpers for the fee arithmetic (gasLimit * price bounds). The solver
  // handles products poorly, so these package the monotonicity facts. mulLeMono is
  // monotone in the second factor, mulLeMonoLeft in the first; sumBound turns an
  // affordability bound (t + v <= balance) into a MAX_VALUE bound on the product t.
  @ghost
  def mulNonNeg(a: BigInt, b: BigInt): Boolean = {
    require(a >= 0 && b >= 0)
    a * b >= 0
  }.holds

  @ghost
  def mulLeMono(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(a >= 0 && b <= c)
    a * b <= a * c because (a * (c - b) >= 0)
  }.holds

  // Arithmetic scaffold for the big-endian digit law (ByteList.readWordDigit).
  // These isolate the nonlinear pow/division/modulo steps so each stays tractable:
  // symbolic-divisor division goes through divAddRemainder, while every modulo is by
  // the constant 256 (linear for the solver).

  // Euclidean quotient of a multiple plus a bounded remainder.
  @ghost
  def divAddRemainder(d: BigInt, m: BigInt, r: BigInt): Boolean = {
    require(d > 0 && m >= 0 && 0 <= r && r < d)
    (d * m + r) / d == m
  }.holds

  // Dividing k*d + w by d peels off k and leaves w/d.
  @ghost
  def divAddMultiple(d: BigInt, k: BigInt, w: BigInt): Boolean = {
    require(d > 0 && k >= 0 && w >= 0)
    divAddRemainder(d, k + w / d, w % d)
    (k * d + w) / d == k + w / d
  }.holds

  // A multiple of 256 added in front does not change a value mod 256. Kept in
  // explicit 256*k form so the modulo stays by a constant (linear for the solver).
  @ghost
  def modAdd256Multiple(k: BigInt, b: BigInt): Boolean = {
    require(k >= 0 && b >= 0)
    (256 * k + b) % 256 == b % 256
  }.holds

  // The final digit step with fully opaque arguments, so the modulo reasoning runs
  // in a clean context away from the pow/division terms that produced q, k, wd.
  @ghost
  def digitCombine(q: BigInt, k: BigInt, wd: BigInt, byte: BigInt): Boolean = {
    require(k >= 0 && wd >= 0 && q == 256 * k + wd && wd % 256 == byte)
    modAdd256Multiple(k, wd)
    q % 256 == byte
  }.holds

  @ghost
  def mulLeMonoLeft(a: BigInt, b: BigInt, c: BigInt): Boolean = {
    require(a <= b && c >= 0)
    a * c <= b * c because ((b - a) * c >= 0)
  }.holds

  @ghost
  def sumBound(t: BigInt, v: BigInt, bal: BigInt): Boolean = {
    require(v >= 0 && t + v <= bal && bal <= MAX_VALUE)
    t <= MAX_VALUE
  }.holds

  @ghost
  def pow256Le(n: BigInt): Boolean = {
    require(0 <= n && n <= 32)
    pow(BigInt(256), n) <= MODULO because (powMono(BigInt(256), n, BigInt(32)) && pow256_32)
  }.holds
}
