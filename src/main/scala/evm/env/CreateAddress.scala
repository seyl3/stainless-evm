package evm.env

import stainless.annotation.*
import stainless.collection.{List => SList, Cons, Nil => SNil}
import evm.value.{Word256, Keccak256}

// Trusted derivation of contract addresses. The address of a created contract is a
// consensus-defined encoding (RLP for CREATE, a fixed byte layout for CREATE2) fed
// through keccak-256; like the hash itself it has no simpler specification, so it
// is an @extern primitive with a real executable body. The verifier treats it as a
// black box returning an Address (whose invariant guarantees the 160-bit range).
object CreateAddress:

  // CREATE: keccak256(rlp([sender, nonce]))[12:].
  @extern
  def create(sender: Address, nonce: BigInt): Address = {
    val addrRlp = Array(0x94.toByte) ++ beBytes(sender.value, 20) // 0x80+20 length prefix, then 20 bytes
    val nonceRlp =
      if (nonce == 0) Array(0x80.toByte)
      else if (nonce < 128) Array(nonce.toByte)
      else { val nb = minimalBE(nonce); Array((0x80 + nb.length).toByte) ++ nb }
    val payload = addrRlp ++ nonceRlp
    val rlp = Array((0xc0 + payload.length).toByte) ++ payload // payload is well under 56 bytes
    addrOf(rlp)
  }

  // CREATE2: keccak256(0xff ++ sender ++ salt ++ keccak256(initcode))[12:].
  @extern
  def create2(sender: Address, salt: Word256, initHash: Word256): Address = {
    val pre = Array(0xff.toByte) ++ beBytes(sender.value, 20) ++ beBytes(salt.value, 32) ++ beBytes(initHash.value, 32)
    addrOf(pre)
  }

  // Hash a preimage and take its low 160 bits as an address.
  @extern @pure
  private def addrOf(preimage: Array[Byte]): Address = {
    var l: SList[BigInt] = SNil()
    var i = preimage.length - 1
    while (i >= 0) do { l = Cons(BigInt(preimage(i) & 0xff), l); i -= 1 }
    Address.fromWord(Keccak256.hash(l))
  }

  // The low n bytes of v, big-endian.
  @extern @pure
  private def beBytes(v: BigInt, n: Int): Array[Byte] = {
    val a = new Array[Byte](n)
    var x = v
    var i = n - 1
    while (i >= 0) do { a(i) = (x % 256).toInt.toByte; x = x / 256; i -= 1 }
    a
  }

  // The minimal big-endian byte string of v > 0 (no leading zeros).
  @extern @pure
  private def minimalBE(v: BigInt): Array[Byte] = {
    var bytes = scala.collection.immutable.List[Byte]()
    var x = v
    while (x > 0) do { bytes = (x % 256).toInt.toByte :: bytes; x = x / 256 }
    bytes.toArray
  }
