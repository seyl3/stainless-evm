package evm.value

import stainless.annotation.*
import stainless.lang.*
import stainless.collection.{List => SList, Cons, Nil => SNil}
import evm.math.Gas
import evm.math.EvmMath

// The Ethereum precompiled contracts. Pure ones (identity, and MODEXP's arithmetic)
// are verified; the cryptographic ones follow the trusted-primitive pattern of
// Keccak256: a real, executable @extern body whose exact output the verifier does
// not reason about (it just knows a byte list comes back). Each is validated
// against official test vectors in the unit tests.
object Precompiles:

  // identity (0x04): returns its input unchanged. Fully verified.
  def identity(input: SList[BigInt]): SList[BigInt] = {
    input
  }.ensuring(_ == input)

  // SHA-256 (0x02): the JDK's verified implementation, as a trusted primitive.
  @extern
  def sha256(input: SList[BigInt]): SList[BigInt] = {
    fromBytes(java.security.MessageDigest.getInstance("SHA-256").digest(toBytes(input)))
  }

  // RIPEMD-160 (0x03): the digest is 20 bytes, left-padded to 32 in the output
  // (the EVM ABI convention). Reference implementation of the RIPEMD-160 spec.
  @extern
  def ripemd160(input: SList[BigInt]): SList[BigInt] = {
    val h = ripemd160Bytes(toBytes(input)) // 20 bytes
    val padded = new Array[Byte](32)
    System.arraycopy(h, 0, padded, 12, 20)
    fromBytes(padded)
  }

  // MODEXP (0x05) arithmetic. The verified specification is base^exp mod m (0 when
  // m == 0), pinned to be a canonical residue in [0, m).
  def modexpSpec(base: BigInt, exp: BigInt, mod: BigInt): BigInt = {
    require(base >= 0 && exp >= 0 && mod >= 0)
    if (mod == 0) BigInt(0)
    else {
      EvmMath.powNonNeg(base, exp)
      EvmMath.pow(base, exp) % mod
    }
  }.ensuring(r => r >= 0 && (mod == 0 || r < mod))

  // The executable core: the JDK's fast modular exponentiation (square-and-multiply).
  // The unit tests check it agrees with modexpSpec, so the trusted fast path is
  // differentially validated against the verified naive definition.
  @extern @pure
  def modexpValue(base: BigInt, exp: BigInt, mod: BigInt): BigInt = {
    if (mod <= 0) BigInt(0) else base.modPow(exp, mod)
  }

  // The byte-level MODEXP precompile: parse [baseLen|expLen|modLen|base|exp|mod]
  // and return base^exp mod m as modLen big-endian bytes.
  @extern
  def modexp(input: SList[BigInt]): SList[BigInt] = {
    val b = toBytes(input)
    def rd(off: Int, n: Int): BigInt = {
      var v = BigInt(0)
      var i = 0
      while (i < n) do { v = (v << 8) | BigInt(if (off + i < b.length) (b(off + i) & 0xff) else 0); i += 1 }
      v
    }
    val baseLen = rd(0, 32).toInt
    val expLen = rd(32, 32).toInt
    val modLen = rd(64, 32).toInt
    val base = rd(96, baseLen)
    val exp = rd(96 + baseLen, expLen)
    val mod = rd(96 + baseLen + expLen, modLen)
    val result = modexpValue(base, exp, mod)
    val out = new Array[Byte](modLen)
    var r = result
    var i = modLen - 1
    while (i >= 0) do { out(i) = (r % 256).toInt.toByte; r = r / 256; i -= 1 }
    fromBytes(out)
  }

  // BLAKE2F (0x09): the BLAKE2b compression function F (EIP-152). Input is 213
  // bytes: rounds (4, big-endian) | h (64) | m (128) | t (16) | f (1), all the
  // 8-byte words little-endian. Output is the 64-byte state h'. Reference algorithm.
  @extern
  def blake2f(input: SList[BigInt]): SList[BigInt] = {
    val b = toBytes(input)
    def le64(off: Int): Long = {
      var v = 0L; var i = 0
      while (i < 8) do { v |= (b(off + i).toLong & 0xffL) << (8 * i); i += 1 }
      v
    }
    val rounds = ((b(0) & 0xffL) << 24) | ((b(1) & 0xffL) << 16) | ((b(2) & 0xffL) << 8) | (b(3) & 0xffL)
    val h = new Array[Long](8); var i = 0
    while (i < 8) do { h(i) = le64(4 + 8 * i); i += 1 }
    val m = new Array[Long](16); i = 0
    while (i < 16) do { m(i) = le64(68 + 8 * i); i += 1 }
    val t0 = le64(196); val t1 = le64(204); val f = b(212) != 0

    val IV = Array(
      0x6a09e667f3bcc908L, 0xbb67ae8584caa73bL, 0x3c6ef372fe94f82bL, 0xa54ff53a5f1d36f1L,
      0x510e527fade682d1L, 0x9b05688c2b3e6c1fL, 0x1f83d9abfb41bd6bL, 0x5be0cd19137e2179L)
    val SIGMA = Array(
      Array(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
      Array(14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3),
      Array(11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4),
      Array(7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8),
      Array(9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13),
      Array(2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9),
      Array(12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11),
      Array(13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10),
      Array(6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5),
      Array(10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0))

    val v = new Array[Long](16)
    i = 0
    while (i < 8) do { v(i) = h(i); v(i + 8) = IV(i); i += 1 }
    v(12) ^= t0; v(13) ^= t1
    if (f) v(14) = ~v(14)
    def rotr(x: Long, n: Int): Long = (x >>> n) | (x << (64 - n))
    def mix(a: Int, bb: Int, c: Int, d: Int, x: Long, y: Long): Unit = {
      v(a) = v(a) + v(bb) + x; v(d) = rotr(v(d) ^ v(a), 32)
      v(c) = v(c) + v(d); v(bb) = rotr(v(bb) ^ v(c), 24)
      v(a) = v(a) + v(bb) + y; v(d) = rotr(v(d) ^ v(a), 16)
      v(c) = v(c) + v(d); v(bb) = rotr(v(bb) ^ v(c), 63)
    }
    var r = 0L
    while (r < rounds) do
      val sg = SIGMA((r % 10).toInt)
      mix(0, 4, 8, 12, m(sg(0)), m(sg(1)))
      mix(1, 5, 9, 13, m(sg(2)), m(sg(3)))
      mix(2, 6, 10, 14, m(sg(4)), m(sg(5)))
      mix(3, 7, 11, 15, m(sg(6)), m(sg(7)))
      mix(0, 5, 10, 15, m(sg(8)), m(sg(9)))
      mix(1, 6, 11, 12, m(sg(10)), m(sg(11)))
      mix(2, 7, 8, 13, m(sg(12)), m(sg(13)))
      mix(3, 4, 9, 14, m(sg(14)), m(sg(15)))
      r += 1

    val out = new Array[Byte](64)
    i = 0
    while (i < 8) do
      val hi = h(i) ^ v(i) ^ v(i + 8)
      var k = 0
      while (k < 8) do { out(8 * i + k) = ((hi >>> (8 * k)) & 0xff).toByte; k += 1 }
      i += 1
    fromBytes(out)
  }

  // BLAKE2F gas is one per round (the round count is the input's first 4 bytes).
  @extern @pure
  def blake2fGas(input: SList[BigInt]): BigInt = {
    val b = toBytes(input)
    BigInt(b(0) & 0xff) * 16777216 + BigInt(b(1) & 0xff) * 65536 + BigInt(b(2) & 0xff) * 256 + BigInt(b(3) & 0xff)
  }.ensuring(_ >= 0)

  // Gas: static base + per-word cost. words(len) = ceil(len/32).
  def identityGas(len: BigInt): BigInt = {
    require(len >= 0)
    BigInt(15) + 3 * Gas.words(len)
  }.ensuring(_ >= 15)

  def sha256Gas(len: BigInt): BigInt = {
    require(len >= 0)
    BigInt(60) + 12 * Gas.words(len)
  }.ensuring(_ >= 60)

  def ripemd160Gas(len: BigInt): BigInt = {
    require(len >= 0)
    BigInt(600) + 120 * Gas.words(len)
  }.ensuring(_ >= 600)

  // MODEXP gas (EIP-2565 shape with the EIP-7883 minimum of 500). Trusted parsing.
  @extern @pure
  def modexpGas(input: SList[BigInt]): BigInt = {
    val b = toBytes(input)
    def rd(off: Int, n: Int): BigInt = {
      var v = BigInt(0); var i = 0
      while (i < n) do { v = (v << 8) | BigInt(if (off + i < b.length) (b(off + i) & 0xff) else 0); i += 1 }
      v
    }
    val baseLen = rd(0, 32); val expLen = rd(32, 32); val modLen = rd(64, 32)
    val maxLen = if (baseLen > modLen) baseLen else modLen
    val words = (maxLen + 7) / 8
    val mult = words * words
    val expHead = rd(96 + baseLen.toInt, if (expLen < 32) expLen.toInt else 32)
    val headBits = if (expHead <= 0) BigInt(0) else BigInt(expHead.bitLength - 1)
    val iter0 = if (expLen <= 32) headBits else 8 * (expLen - 32) + headBits
    val iter = if (iter0 < 1) BigInt(1) else iter0
    val g = mult * iter / 3
    if (g < 500) BigInt(500) else g
  }.ensuring(_ >= 500)

  // The implemented precompile addresses: 0x02 SHA-256, 0x03 RIPEMD-160,
  // 0x04 identity, 0x05 MODEXP, 0x09 BLAKE2F. (0x01 and the EC ones still fall
  // through to the empty-account path.)
  def isImplemented(a: BigInt): Boolean = a == 2 || a == 3 || a == 4 || a == 5 || a == 9

  def gasFor(a: BigInt, input: SList[BigInt]): BigInt = {
    require(isImplemented(a) && input.size >= 0)
    if (a == 2) sha256Gas(input.size)
    else if (a == 3) ripemd160Gas(input.size)
    else if (a == 4) identityGas(input.size)
    else if (a == 5) modexpGas(input)
    else blake2fGas(input)
  }.ensuring(_ >= 0)

  def outputFor(a: BigInt, input: SList[BigInt]): SList[BigInt] = {
    require(isImplemented(a))
    if (a == 2) sha256(input)
    else if (a == 3) ripemd160(input)
    else if (a == 4) identity(input)
    else if (a == 5) modexp(input)
    else blake2f(input)
  }

  // --- trusted byte plumbing (ignored by the verifier) ---

  @extern @pure
  private def toBytes(l: SList[BigInt]): Array[Byte] = {
    val buf = scala.collection.mutable.ArrayBuffer[Byte]()
    var cur = l
    while (!cur.isEmpty) do { buf += (cur.head.toInt & 0xff).toByte; cur = cur.tail }
    buf.toArray
  }

  @extern @pure
  private def fromBytes(a: Array[Byte]): SList[BigInt] = {
    var l: SList[BigInt] = SNil()
    var i = a.length - 1
    while (i >= 0) do { l = Cons(BigInt(a(i) & 0xff), l); i -= 1 }
    l
  }

  // RIPEMD-160 core (returns 20 bytes). Standard reference algorithm.
  @extern @pure
  private def ripemd160Bytes(msg: Array[Byte]): Array[Byte] = {
    def rotl(x: Int, n: Int): Int = (x << n) | (x >>> (32 - n))
    val f: (Int, Int, Int, Int) => Int = (j, x, y, z) =>
      if (j < 16) x ^ y ^ z
      else if (j < 32) (x & y) | (~x & z)
      else if (j < 48) (x | ~y) ^ z
      else if (j < 64) (x & z) | (y & ~z)
      else x ^ (y | ~z)
    val K = Array(0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e)
    val KP = Array(0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000)
    val r = Array(
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
      7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
      3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
      1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
      4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13)
    val rp = Array(
      5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
      6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
      15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
      8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
      12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11)
    val s = Array(
      11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
      7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
      11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
      11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
      9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6)
    val sp = Array(
      8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
      9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
      9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
      15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
      8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11)

    val ml = msg.length
    val padLen = (((ml + 8) / 64) + 1) * 64
    val m = new Array[Byte](padLen)
    System.arraycopy(msg, 0, m, 0, ml)
    m(ml) = 0x80.toByte
    val bitLen = ml.toLong * 8
    var i = 0
    while (i < 8) do { m(padLen - 8 + i) = ((bitLen >>> (8 * i)) & 0xff).toByte; i += 1 }

    var h0 = 0x67452301; var h1 = 0xefcdab89; var h2 = 0x98badcfe; var h3 = 0x10325476; var h4 = 0xc3d2e1f0
    var off = 0
    while (off < padLen) do
      val x = new Array[Int](16)
      var k = 0
      while (k < 16) do
        x(k) = (m(off + 4 * k) & 0xff) | ((m(off + 4 * k + 1) & 0xff) << 8) |
          ((m(off + 4 * k + 2) & 0xff) << 16) | ((m(off + 4 * k + 3) & 0xff) << 24)
        k += 1
      var al = h0; var bl = h1; var cl = h2; var dl = h3; var el = h4
      var ar = h0; var br = h1; var cr = h2; var dr = h3; var er = h4
      var j = 0
      while (j < 80) do
        val t1 = rotl(al + f(j, bl, cl, dl) + x(r(j)) + K(j / 16), s(j)) + el
        al = el; el = dl; dl = rotl(cl, 10); cl = bl; bl = t1
        val t2 = rotl(ar + f(79 - j, br, cr, dr) + x(rp(j)) + KP(j / 16), sp(j)) + er
        ar = er; er = dr; dr = rotl(cr, 10); cr = br; br = t2
        j += 1
      val t = h1 + cl + dr
      h1 = h2 + dl + er; h2 = h3 + el + ar; h3 = h4 + al + br; h4 = h0 + bl + cr; h0 = t
      off += 64

    val out = new Array[Byte](20)
    val hs = Array(h0, h1, h2, h3, h4)
    var b = 0
    while (b < 5) do
      out(4 * b) = (hs(b) & 0xff).toByte
      out(4 * b + 1) = ((hs(b) >>> 8) & 0xff).toByte
      out(4 * b + 2) = ((hs(b) >>> 16) & 0xff).toByte
      out(4 * b + 3) = ((hs(b) >>> 24) & 0xff).toByte
      b += 1
    out
  }
