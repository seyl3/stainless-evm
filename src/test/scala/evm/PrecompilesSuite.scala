package evm

import stainless.collection.{List => SList, Cons, Nil => SNil}
import evm.value.*

class PrecompilesSuite extends munit.FunSuite {

  def bytes(xs: Int*): SList[BigInt] =
    xs.foldRight(SNil[BigInt](): SList[BigInt])((x, acc) => Cons(BigInt(x), acc))

  def toBig(l: SList[BigInt]): BigInt =
    l.foldLeft(BigInt(0))((acc, b) => (acc << 8) | b)

  test("identity (0x04) returns its input unchanged") {
    val in = bytes(1, 2, 3, 0xFF, 0x00, 0x42)
    assertEquals(Precompiles.identity(in), in)
  }

  test("SHA-256 (0x02) of the empty input") {
    assertEquals(Precompiles.sha256(SNil()).size, BigInt(32))
    assertEquals(toBig(Precompiles.sha256(SNil())),
      BigInt("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 16))
  }

  test("SHA-256 (0x02) of 'abc'") {
    assertEquals(toBig(Precompiles.sha256(bytes(0x61, 0x62, 0x63))),
      BigInt("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad", 16))
  }

  test("RIPEMD-160 (0x03) of the empty input, left-padded to 32 bytes") {
    val out = Precompiles.ripemd160(SNil())
    assertEquals(out.size, BigInt(32))
    assertEquals(toBig(out), BigInt("9c1185a5c5e9fc54612808977ee8f548b2258d31", 16))
  }

  test("RIPEMD-160 (0x03) of 'abc'") {
    assertEquals(toBig(Precompiles.ripemd160(bytes(0x61, 0x62, 0x63))),
      BigInt("8eb208f7e05d987a9b044a8e98c6b087f15a0bfc", 16))
  }

  test("RIPEMD-160 (0x03) of 'message digest'") {
    // "message digest" -> 5d0689ef49d2fae572b881b123a85ffa21595f36
    val md = bytes(0x6d, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x20, 0x64, 0x69, 0x67, 0x65, 0x73, 0x74)
    assertEquals(toBig(Precompiles.ripemd160(md)),
      BigInt("5d0689ef49d2fae572b881b123a85ffa21595f36", 16))
  }

  def sl(xs: Seq[Int]): SList[BigInt] =
    xs.foldRight(SNil[BigInt](): SList[BigInt])((x, acc) => Cons(BigInt(x), acc))
  def pad32(v: Int): Seq[Int] = Seq.fill(31)(0) :+ v
  def modexpInput(bl: Int, el: Int, ml: Int, base: Seq[Int], exp: Seq[Int], mod: Seq[Int]): SList[BigInt] =
    sl(pad32(bl) ++ pad32(el) ++ pad32(ml) ++ base ++ exp ++ mod)

  test("MODEXP (0x05) fast path agrees with the verified spec (differential)") {
    assertEquals(Precompiles.modexpValue(3, 5, 7), Precompiles.modexpSpec(3, 5, 7))
    assertEquals(Precompiles.modexpValue(2, 10, 1000), Precompiles.modexpSpec(2, 10, 1000))
    assertEquals(Precompiles.modexpValue(7, 0, 13), Precompiles.modexpSpec(7, 0, 13))
    assertEquals(Precompiles.modexpValue(123, 456, 789), Precompiles.modexpSpec(123, 456, 789))
    assertEquals(Precompiles.modexpSpec(3, 5, 7), BigInt(5)) // 243 mod 7
  }

  test("MODEXP (0x05) byte-level: 3^5 mod 7 = 5") {
    val out = Precompiles.modexp(modexpInput(1, 1, 1, Seq(3), Seq(5), Seq(7)))
    assertEquals(out.size, BigInt(1))
    assertEquals(toBig(out), BigInt(5))
  }

  test("MODEXP (0x05) byte-level: 2^10 mod 1000 = 24, output is modLen bytes") {
    val out = Precompiles.modexp(modexpInput(1, 1, 2, Seq(2), Seq(10), Seq(0x03, 0xE8)))
    assertEquals(out.size, BigInt(2))
    assertEquals(toBig(out), BigInt(24))
  }

  test("MODEXP (0x05) byte-level: exp 0 gives 1, mod 0 gives 0") {
    assertEquals(toBig(Precompiles.modexp(modexpInput(1, 1, 1, Seq(9), Seq(0), Seq(13)))), BigInt(1))
    assertEquals(toBig(Precompiles.modexp(modexpInput(1, 1, 1, Seq(9), Seq(2), Seq(0)))), BigInt(0))
  }

  def hex(s: String): SList[BigInt] =
    s.grouped(2).map(h => BigInt(h, 16)).toList.foldRight(SNil[BigInt](): SList[BigInt])((b, acc) => Cons(b, acc))

  test("ecRecover (0x01) recovers the signer address (known vector)") {
    val input = hex(
      "456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3" +
      "000000000000000000000000000000000000000000000000000000000000001c" +
      "9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608" +
      "4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada")
    val out = Precompiles.ecrecover(input)
    assertEquals(out.size, BigInt(32))
    assertEquals(toBig(out), BigInt("7156526fbd7a3c72969b54f64e42c10fbb768c8a", 16))
  }

  test("ecRecover (0x01) returns empty for an out-of-range v") {
    val input = hex(
      "456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3" +
      "0000000000000000000000000000000000000000000000000000000000000001" +
      "9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608" +
      "4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada")
    assertEquals(Precompiles.ecrecover(input).size, BigInt(0))
  }

  test("BLAKE2F (0x09) matches the EIP-152 vector") {
    val input = hex("0000000c" +
      "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" +
      "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b" +
      "616263" + "00" * 125 +
      "0300000000000000" + "0000000000000000" + "01")
    assertEquals(input.size, BigInt(213))
    val out = Precompiles.blake2f(input)
    assertEquals(out.size, BigInt(64))
    assertEquals(toBig(out), BigInt(
      "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" +
      "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923", 16))
  }

  test("P-256 verify (0x100) accepts a valid signature and rejects a tampered one") {
    val kpg = java.security.KeyPairGenerator.getInstance("EC")
    kpg.initialize(new java.security.spec.ECGenParameterSpec("secp256r1"))
    val kp = kpg.generateKeyPair()
    val hash = Array.tabulate(32)(i => (i * 7 + 1).toByte)
    val signer = java.security.Signature.getInstance("NONEwithECDSA")
    signer.initSign(kp.getPrivate)
    signer.update(hash)
    val der = signer.sign()
    val rlen = der(3).toInt
    val r = new java.math.BigInteger(1, java.util.Arrays.copyOfRange(der, 4, 4 + rlen))
    val soff = 4 + rlen
    val slen = der(soff + 1).toInt
    val s = new java.math.BigInteger(1, java.util.Arrays.copyOfRange(der, soff + 2, soff + 2 + slen))
    val pub = kp.getPublic.asInstanceOf[java.security.interfaces.ECPublicKey]
    def to32(v: java.math.BigInteger): Array[Byte] = {
      val bs = v.toByteArray
      val src = if (bs.length > 32) bs.takeRight(32) else bs
      val out = new Array[Byte](32); System.arraycopy(src, 0, out, 32 - src.length, src.length); out
    }
    def slb(a: Array[Byte]): SList[BigInt] =
      a.foldRight(SNil[BigInt](): SList[BigInt])((x, acc) => Cons(BigInt(x & 0xff), acc))
    val input = hash ++ to32(r) ++ to32(s) ++ to32(pub.getW.getAffineX) ++ to32(pub.getW.getAffineY)
    assertEquals(input.length, 160)
    assertEquals(toBig(Precompiles.p256Verify(slb(input))), BigInt(1))
    val bad = input.clone(); bad(0) = (bad(0) ^ 0xFF).toByte
    assertEquals(Precompiles.p256Verify(slb(bad)).size, BigInt(0))
  }

  def w256(v: BigInt): String = { val s = v.toString(16); "0" * (64 - s.length) + s }

  test("bn254 ecMul (0x07): 2*G equals the known doubled generator") {
    val out = Precompiles.bn254Mul(hex(w256(1) + w256(2) + w256(2)))
    assertEquals(out.size, BigInt(64))
    val full = toBig(out)
    assertEquals(full >> 256, BigInt("1368015179489954701390400359078579693043519447331113978918064868415326638035"))
    assertEquals(full % BigInt(2).pow(256), BigInt("9918110051302171585080402603319702774565515993150576347155970296011118125764"))
  }

  test("bn254 ecAdd (0x06): G + G equals 2*G") {
    val add = Precompiles.bn254Add(hex(w256(1) + w256(2) + w256(1) + w256(2)))
    val mul = Precompiles.bn254Mul(hex(w256(1) + w256(2) + w256(2)))
    assertEquals(add, mul)
  }

  test("bn254: scalar 0 gives the identity, adding the identity is a no-op") {
    assertEquals(toBig(Precompiles.bn254Mul(hex(w256(1) + w256(2) + w256(0)))), BigInt(0))
    val addId = Precompiles.bn254Add(hex(w256(1) + w256(2) + w256(0) + w256(0)))
    assertEquals(toBig(addId), BigInt(1) * BigInt(2).pow(256) + BigInt(2))
  }

  test("precompile gas costs") {
    assertEquals(Precompiles.identityGas(0), BigInt(15))
    assertEquals(Precompiles.identityGas(32), BigInt(18))
    assertEquals(Precompiles.identityGas(33), BigInt(21))
    assertEquals(Precompiles.sha256Gas(0), BigInt(60))
    assertEquals(Precompiles.sha256Gas(32), BigInt(72))
    assertEquals(Precompiles.ripemd160Gas(0), BigInt(600))
    assertEquals(Precompiles.ripemd160Gas(32), BigInt(720))
  }
}
