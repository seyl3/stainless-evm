package evm.math

import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*
import stainless.proof.*
import evm.math.EvmMath.pow

// Byte-array packing over a sparse Map[address, byte] (the model of EVM memory).
// Provides big-endian read/write of multi-byte words and block copies, plus the
// framing lemmas (a write leaves bytes before/after untouched) and the read-write
// round-trip that the Memory operations rely on for their exact postconditions.
object Bytes {

  // Euclidean mod 256: normalize any integer to a single byte [0, 256).
  def emod256(x: BigInt): BigInt = {
    ((x % 256) + 256) % 256
  }.ensuring(r => 0 <= r && r < 256)

  // The byte stored at address a, or zero for an untouched cell.
  def getByteOf(data: Map[BigInt, BigInt], a: BigInt): BigInt = {
    if (data.contains(a)) emod256(data(a)) else BigInt(0)
  }.ensuring(r => 0 <= r && r < 256)

  def setByteOf(data: Map[BigInt, BigInt], a: BigInt, b: BigInt): Map[BigInt, BigInt] = {
    data.updated(a, emod256(b))
  }.ensuring(r => getByteOf(r, a) == emod256(b))

  // Big-endian integer packed from n bytes starting at a (the MLOAD value).
  def readBytes(data: Map[BigInt, BigInt], a: BigInt, n: BigInt): BigInt = {
    require(n >= 0)
    decreases(n)
    if (n == 0) BigInt(0)
    else getByteOf(data, a) * pow(BigInt(256), n - 1) + readBytes(data, a + 1, n - 1)
  }.ensuring(r => 0 <= r && r < pow(BigInt(256), n))

  // Store v big-endian across n bytes from a (the MSTORE effect); peels off the
  // most significant byte (v / 256^(n-1)) each step.
  def writeBytes(data: Map[BigInt, BigInt], a: BigInt, n: BigInt, v: BigInt): Map[BigInt, BigInt] = {
    require(n >= 0 && v >= 0)
    decreases(n)
    if (n == 0) data
    else {
      val p = pow(BigInt(256), n - 1)
      writeBytes(setByteOf(data, a, v / p), a + 1, n - 1, v % p)
    }
  }

  // Framing and round-trip lemmas below, proven by induction on the byte count.
  // They let Memory/copy ops state exact per-byte postconditions: a write touches
  // only [a, a+n) and reading back what was written returns the original value.
  @ghost
  def writeBytesPreservesBefore(data: Map[BigInt, BigInt], a: BigInt, n: BigInt, v: BigInt, x: BigInt): Boolean = {
    require(n >= 0 && v >= 0 && x < a)
    decreases(n)
    (getByteOf(writeBytes(data, a, n, v), x) == getByteOf(data, x)) because {
      if (n == 0) trivial
      else {
        val p = pow(BigInt(256), n - 1)
        val d2 = setByteOf(data, a, v / p)
        writeBytesPreservesBefore(d2, a + 1, n - 1, v % p, x) &&
        getByteOf(d2, x) == getByteOf(data, x)
      }
    }
  }.holds

  @ghost
  def writeBytesPreservesAfter(data: Map[BigInt, BigInt], a: BigInt, n: BigInt, v: BigInt, x: BigInt): Boolean = {
    require(n >= 0 && v >= 0 && x >= a + n)
    decreases(n)
    (getByteOf(writeBytes(data, a, n, v), x) == getByteOf(data, x)) because {
      if (n == 0) trivial
      else {
        val p = pow(BigInt(256), n - 1)
        val d2 = setByteOf(data, a, v / p)
        writeBytesPreservesAfter(d2, a + 1, n - 1, v % p, x) &&
        getByteOf(d2, x) == getByteOf(data, x)
      }
    }
  }.holds

  @ghost
  def readWriteRoundtrip(data: Map[BigInt, BigInt], a: BigInt, n: BigInt, v: BigInt): Boolean = {
    require(n >= 0 && 0 <= v && v < pow(BigInt(256), n))
    decreases(n)
    (readBytes(writeBytes(data, a, n, v), a, n) == v) because {
      if (n == 0) trivial
      else {
        val p = pow(BigInt(256), n - 1)
        val d2 = setByteOf(data, a, v / p)
        writeBytesPreservesBefore(d2, a + 1, n - 1, v % p, a) &&
        readWriteRoundtrip(d2, a + 1, n - 1, v % p)
      }
    }
  }.holds

  // Map-to-map block copy (MCOPY): len bytes from `from` to `to`.
  def copyBytes(orig: Map[BigInt, BigInt], dst: Map[BigInt, BigInt],
                to: BigInt, from: BigInt, len: BigInt): Map[BigInt, BigInt] = {
    require(len >= 0)
    decreases(len)
    if (len == 0) dst
    else copyBytes(orig, setByteOf(dst, to, getByteOf(orig, from)), to + 1, from + 1, len - 1)
  }

  // List-to-map block copy with zero padding past the source end (CALLDATACOPY).
  def copyFromList(dst: Map[BigInt, BigInt], to: BigInt,
                   src: List[BigInt], from: BigInt, len: BigInt): Map[BigInt, BigInt] = {
    require(from >= 0 && len >= 0)
    decreases(len)
    if (len == 0) dst
    else copyFromList(setByteOf(dst, to, ByteList.byteOrZero(src, from)), to + 1, src, from + 1, len - 1)
  }

  // Read len memory bytes out as a list (RETURN/log data capture).
  def readList(data: Map[BigInt, BigInt], from: BigInt, len: BigInt): List[BigInt] = {
    require(len >= 0)
    decreases(len)
    if (len == 0) Nil[BigInt]()
    else Cons(getByteOf(data, from), readList(data, from + 1, len - 1))
  }.ensuring(r => r.size == len)

  @ghost
  def copyByteAt(orig: Map[BigInt, BigInt], dst: Map[BigInt, BigInt],
                 to: BigInt, from: BigInt, len: BigInt, k: BigInt): Boolean = {
    require(len >= 0 && 0 <= k && k < len)
    decreases(len)
    (getByteOf(copyBytes(orig, dst, to, from, len), to + k) == getByteOf(orig, from + k)) because {
      val dst2 = setByteOf(dst, to, getByteOf(orig, from))
      if (k == 0) copyBytesPreservesBefore(orig, dst2, to + 1, from + 1, len - 1, to)
      else copyByteAt(orig, dst2, to + 1, from + 1, len - 1, k - 1)
    }
  }.holds

  @ghost
  def copyBytesPreservesBefore(orig: Map[BigInt, BigInt], dst: Map[BigInt, BigInt],
                               to: BigInt, from: BigInt, len: BigInt, x: BigInt): Boolean = {
    require(len >= 0 && x < to)
    decreases(len)
    (getByteOf(copyBytes(orig, dst, to, from, len), x) == getByteOf(dst, x)) because {
      if (len == 0) trivial
      else {
        val dst2 = setByteOf(dst, to, getByteOf(orig, from))
        copyBytesPreservesBefore(orig, dst2, to + 1, from + 1, len - 1, x) &&
        getByteOf(dst2, x) == getByteOf(dst, x)
      }
    }
  }.holds

  @ghost
  def copyBytesPreservesAfter(orig: Map[BigInt, BigInt], dst: Map[BigInt, BigInt],
                              to: BigInt, from: BigInt, len: BigInt, x: BigInt): Boolean = {
    require(len >= 0 && x >= to + len)
    decreases(len)
    (getByteOf(copyBytes(orig, dst, to, from, len), x) == getByteOf(dst, x)) because {
      if (len == 0) trivial
      else {
        val dst2 = setByteOf(dst, to, getByteOf(orig, from))
        copyBytesPreservesAfter(orig, dst2, to + 1, from + 1, len - 1, x) &&
        getByteOf(dst2, x) == getByteOf(dst, x)
      }
    }
  }.holds

  @ghost
  def copyFromListPreservesBefore(dst: Map[BigInt, BigInt], to: BigInt,
                                  src: List[BigInt], from: BigInt, len: BigInt, x: BigInt): Boolean = {
    require(from >= 0 && len >= 0 && x < to)
    decreases(len)
    (getByteOf(copyFromList(dst, to, src, from, len), x) == getByteOf(dst, x)) because {
      if (len == 0) trivial
      else {
        val dst2 = setByteOf(dst, to, ByteList.byteOrZero(src, from))
        copyFromListPreservesBefore(dst2, to + 1, src, from + 1, len - 1, x) &&
        getByteOf(dst2, x) == getByteOf(dst, x)
      }
    }
  }.holds

  @ghost
  def copyFromListPreservesAfter(dst: Map[BigInt, BigInt], to: BigInt,
                                 src: List[BigInt], from: BigInt, len: BigInt, x: BigInt): Boolean = {
    require(from >= 0 && len >= 0 && x >= to + len)
    decreases(len)
    (getByteOf(copyFromList(dst, to, src, from, len), x) == getByteOf(dst, x)) because {
      if (len == 0) trivial
      else {
        val dst2 = setByteOf(dst, to, ByteList.byteOrZero(src, from))
        copyFromListPreservesAfter(dst2, to + 1, src, from + 1, len - 1, x) &&
        getByteOf(dst2, x) == getByteOf(dst, x)
      }
    }
  }.holds

  @ghost
  def copyFromListAt(dst: Map[BigInt, BigInt], to: BigInt,
                     src: List[BigInt], from: BigInt, len: BigInt, k: BigInt): Boolean = {
    require(from >= 0 && len >= 0 && 0 <= k && k < len)
    decreases(len)
    (getByteOf(copyFromList(dst, to, src, from, len), to + k) == ByteList.byteOrZero(src, from + k)) because {
      val dst2 = setByteOf(dst, to, ByteList.byteOrZero(src, from))
      if (k == 0) copyFromListPreservesBefore(dst2, to + 1, src, from + 1, len - 1, to)
      else copyFromListAt(dst2, to + 1, src, from + 1, len - 1, k - 1)
    }
  }.holds

  @ghost
  def readListAt(data: Map[BigInt, BigInt], from: BigInt, len: BigInt, k: BigInt): Boolean = {
    require(len >= 0 && 0 <= k && k < len)
    decreases(len)
    (readList(data, from, len)(k) == getByteOf(data, from + k)) because {
      if (k == 0) trivial
      else readListAt(data, from + 1, len - 1, k - 1)
    }
  }.holds
}
