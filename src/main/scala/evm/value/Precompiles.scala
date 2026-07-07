package evm.value

import stainless.annotation.*
import stainless.collection.{List => SList, Cons, Nil => SNil}
import evm.math.Gas

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
