package evm.value

import stainless.annotation.*
import stainless.collection.*

// Keccak-256 (the Ethereum pre-standardization variant, 0x01 domain padding).
// A cryptographic hash has no simpler specification than its own algorithm, so it
// is a TRUSTED primitive: the body is a real, executable implementation but is
// marked @extern, so Stainless treats `hash` as a black box returning a Word256
// (all the verified interpreter needs). This mirrors the Bitwise axioms.
object Keccak256:

  @extern
  def hash(data: List[BigInt]): Word256 = {
    val rate = 136 // Keccak-256 rate in bytes (1088 bits)

    def rotl(x: Long, n: Int): Long = if (n == 0) x else (x << n) | (x >>> (64 - n))

    val RC: Array[Long] = Array(
      0x0000000000000001L, 0x0000000000008082L, 0x800000000000808aL, 0x8000000080008000L,
      0x000000000000808bL, 0x0000000080000001L, 0x8000000080008081L, 0x8000000000008009L,
      0x000000000000008aL, 0x0000000000000088L, 0x0000000080008009L, 0x000000008000000aL,
      0x000000008000808bL, 0x800000000000008bL, 0x8000000000008089L, 0x8000000000008003L,
      0x8000000000008002L, 0x8000000000000080L, 0x000000000000800aL, 0x800000008000000aL,
      0x8000000080008081L, 0x8000000000008080L, 0x0000000080000001L, 0x8000000080008008L)

    // rotation offsets indexed by x + 5*y
    val rot: Array[Int] = Array(
      0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
      41, 45, 15, 21, 8, 18, 2, 61, 56, 14)

    def keccakF(a: Array[Long]): Unit = {
      var round = 0
      while (round < 24) {
        val c = new Array[Long](5)
        var x = 0
        while (x < 5) { c(x) = a(x) ^ a(x + 5) ^ a(x + 10) ^ a(x + 15) ^ a(x + 20); x += 1 }
        val d = new Array[Long](5)
        x = 0
        while (x < 5) { d(x) = c((x + 4) % 5) ^ rotl(c((x + 1) % 5), 1); x += 1 }
        x = 0
        while (x < 5) { var y = 0; while (y < 5) { a(x + 5 * y) ^= d(x); y += 1 }; x += 1 }
        val b = new Array[Long](25)
        x = 0
        while (x < 5) {
          var y = 0
          while (y < 5) { b(y + 5 * ((2 * x + 3 * y) % 5)) = rotl(a(x + 5 * y), rot(x + 5 * y)); y += 1 }
          x += 1
        }
        x = 0
        while (x < 5) {
          var y = 0
          while (y < 5) { a(x + 5 * y) = b(x + 5 * y) ^ ((~b((x + 1) % 5 + 5 * y)) & b((x + 2) % 5 + 5 * y)); y += 1 }
          x += 1
        }
        a(0) ^= RC(round)
        round += 1
      }
    }

    // message bytes
    val n = data.size.toInt
    val msgLen = n
    val padLen = rate - (msgLen % rate)
    val padded = new Array[Byte](msgLen + padLen)
    var cur = data
    var idx = 0
    while (idx < n) { padded(idx) = (cur.head.toInt & 0xff).toByte; cur = cur.tail; idx += 1 }
    padded(msgLen) = (padded(msgLen) | 0x01).toByte
    padded(padded.length - 1) = (padded(padded.length - 1) | 0x80.toByte).toByte

    val state = new Array[Long](25)
    var off = 0
    while (off < padded.length) {
      var lane = 0
      while (lane < rate / 8) {
        var w = 0L
        var j = 0
        while (j < 8) { w |= (padded(off + lane * 8 + j).toLong & 0xffL) << (8 * j); j += 1 }
        state(lane) ^= w
        lane += 1
      }
      keccakF(state)
      off += rate
    }

    var v = BigInt(0)
    var k = 0
    while (k < 32) {
      val bytev = ((state(k / 8) >>> (8 * (k % 8))) & 0xffL).toInt
      v = (v << 8) | BigInt(bytev)
      k += 1
    }
    Word256(v)
  }
