package evm.state

import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*
import stainless.proof.*
import evm.value.Word256
import evm.math.EvmMath
import evm.math.Bytes
import evm.math.ByteList

// Byte-addressable EVM memory: a sparse byte map plus the active `size`, which is
// always a multiple of 32 and only grows. Reads/writes are word-oriented and pin
// exact per-byte behaviour via the Bytes lemmas.
object Memory {
  def empty: Memory = Memory(Map.empty[BigInt, BigInt], BigInt(0))
}

case class Memory(data: Map[BigInt, BigInt], size: BigInt) {
  require(size >= 0 && size % 32 == 0)

  def getByte(a: BigInt): BigInt = Bytes.getByteOf(data, a)

  def msize: BigInt = size

  // The word-aligned size after an access reaching byte `end` (exclusive); never
  // shrinks. Drives the memory-expansion gas charge.
  def expandedTo(end: BigInt): BigInt = {
    require(end >= 0)
    val needed = ((end + 31) / 32) * 32
    if (needed > size) needed else size
  }.ensuring(r => r >= size && r >= end && r % 32 == 0)

  def expand(end: BigInt): Memory = {
    require(end >= 0)
    Memory(data, expandedTo(end))
  }.ensuring(r => r.data == data && r.size == expandedTo(end) && r.size >= size && r.size >= end)

  // MLOAD: the 32-byte big-endian word at offset. pow256_32 gives 256^32 == 2^256
  // so the result is provably in Word256 range.
  def load(offset: BigInt): Word256 = {
    require(offset >= 0)
    EvmMath.pow256_32
    Word256(Bytes.readBytes(data, offset, 32))
  }.ensuring(r => r.value == Bytes.readBytes(data, offset, 32))

  // MSTORE: write a word big-endian and grow to cover it. The round-trip lemma
  // proves load(offset) reads back exactly w.
  def store(offset: BigInt, w: Word256): Memory = {
    require(offset >= 0)
    EvmMath.pow256_32
    Bytes.readWriteRoundtrip(data, offset, 32, w.value)
    Memory(Bytes.writeBytes(data, offset, 32, w.value), expandedTo(offset + 32))
  }.ensuring(r =>
    r.load(offset).value == w.value
    && r.data == Bytes.writeBytes(data, offset, 32, w.value)
    && r.size >= size && r.size >= offset + 32)

  // MSTORE8: write a single low byte of b, growing by one byte.
  def store8(offset: BigInt, b: Word256): Memory = {
    require(offset >= 0)
    Memory(Bytes.setByteOf(data, offset, b.value % 256), expandedTo(offset + 1))
  }.ensuring(r =>
    r.getByte(offset) == b.value % 256
    && r.size >= size && r.size >= offset + 1)

  // MCOPY: overlap-safe block copy within memory; a zero-length copy never grows.
  def mcopy(dst: BigInt, src: BigInt, len: BigInt): Memory = {
    require(dst >= 0 && src >= 0 && len >= 0)
    val newSize =
      if (len == 0) size
      else expandedTo(if (dst > src) dst + len else src + len)
    Memory(Bytes.copyBytes(data, data, dst, src, len), newSize)
  }.ensuring(r =>
    r.data == Bytes.copyBytes(data, data, dst, src, len)
    && r.size >= size
    && (len == 0 || (r.size >= dst + len && r.size >= src + len)))

  // Copy len bytes from an external list into memory (CALLDATACOPY/CODECOPY),
  // zero-filling past the source end.
  def copyIn(dst: BigInt, src: List[BigInt], srcOffset: BigInt, len: BigInt): Memory = {
    require(dst >= 0 && srcOffset >= 0 && len >= 0)
    val newSize = if (len == 0) size else expandedTo(dst + len)
    Memory(Bytes.copyFromList(data, dst, src, srcOffset, len), newSize)
  }.ensuring(r =>
    r.data == Bytes.copyFromList(data, dst, src, srcOffset, len)
    && r.size >= size
    && (len == 0 || r.size >= dst + len))

  // Per-byte lemmas below (delegating to Bytes): each op writes exactly its target
  // range and every byte outside it is preserved. These give the copy opcodes
  // their exact correctness postconditions.
  @ghost
  def storePreservesOutside(offset: BigInt, w: Word256, x: BigInt): Boolean = {
    require(offset >= 0 && (x < offset || x >= offset + 32))
    (store(offset, w).getByte(x) == getByte(x)) because {
      if (x < offset) Bytes.writeBytesPreservesBefore(data, offset, 32, w.value, x)
      else Bytes.writeBytesPreservesAfter(data, offset, 32, w.value, x)
    }
  }.holds

  @ghost
  def mcopyByteAt(dst: BigInt, src: BigInt, len: BigInt, k: BigInt): Boolean = {
    require(dst >= 0 && src >= 0 && len >= 0 && 0 <= k && k < len)
    (mcopy(dst, src, len).getByte(dst + k) == getByte(src + k)) because
      Bytes.copyByteAt(data, data, dst, src, len, k)
  }.holds

  @ghost
  def mcopyPreservesOutside(dst: BigInt, src: BigInt, len: BigInt, x: BigInt): Boolean = {
    require(dst >= 0 && src >= 0 && len >= 0 && (x < dst || x >= dst + len))
    (mcopy(dst, src, len).getByte(x) == getByte(x)) because {
      if (x < dst) Bytes.copyBytesPreservesBefore(data, data, dst, src, len, x)
      else Bytes.copyBytesPreservesAfter(data, data, dst, src, len, x)
    }
  }.holds

  @ghost
  def copyInByteAt(dst: BigInt, src: List[BigInt], srcOffset: BigInt, len: BigInt, k: BigInt): Boolean = {
    require(dst >= 0 && srcOffset >= 0 && len >= 0 && 0 <= k && k < len)
    (copyIn(dst, src, srcOffset, len).getByte(dst + k) == ByteList.byteOrZero(src, srcOffset + k)) because
      Bytes.copyFromListAt(data, dst, src, srcOffset, len, k)
  }.holds

  @ghost
  def copyInPreservesOutside(dst: BigInt, src: List[BigInt], srcOffset: BigInt, len: BigInt, x: BigInt): Boolean = {
    require(dst >= 0 && srcOffset >= 0 && len >= 0 && (x < dst || x >= dst + len))
    (copyIn(dst, src, srcOffset, len).getByte(x) == getByte(x)) because {
      if (x < dst) Bytes.copyFromListPreservesBefore(data, dst, src, srcOffset, len, x)
      else Bytes.copyFromListPreservesAfter(data, dst, src, srcOffset, len, x)
    }
  }.holds
}
