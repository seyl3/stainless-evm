package evm

import stainless.collection.*
import evm.value.*
import evm.env.*

class CreateAddressSuite extends munit.FunSuite {

  test("CREATE2 address matches the EIP-1014 vector") {
    // sender 0x0, salt 0x0, init_code 0x00 -> 0x4D1A2e2bB4F88F0250f26Ffff098B0b30B26Bf38
    val initHash = Keccak256.hash(Cons(BigInt(0), Nil()))
    val addr = CreateAddress.create2(Address(BigInt(0)), Word256.Zero, initHash)
    assertEquals(addr.value, BigInt("4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38", 16))
  }

  test("CREATE address matches known nonce vectors") {
    val sender = Address(BigInt("6ac7ea33f8831ea9dcc53393aaa88b25a785dbf0", 16))
    assertEquals(CreateAddress.create(sender, 0).value, BigInt("cd234a471b72ba2f1ccf0a70fcaba648a5eecd8d", 16))
    assertEquals(CreateAddress.create(sender, 1).value, BigInt("343c43a37d37dff08ae8c4a11544c718abb4fcf8", 16))
  }

  test("CREATE address is deterministic and nonce-dependent") {
    val s = Address(BigInt(0x1234))
    assertEquals(CreateAddress.create(s, 5), CreateAddress.create(s, 5))
    assert(CreateAddress.create(s, 5) != CreateAddress.create(s, 6))
  }

  test("CREATE2 address depends on the salt and the initcode hash") {
    val s = Address(BigInt(0x1234))
    val h = Keccak256.hash(Cons(BigInt(0), Nil()))
    assertEquals(CreateAddress.create2(s, Word256(BigInt(1)), h), CreateAddress.create2(s, Word256(BigInt(1)), h))
    assert(CreateAddress.create2(s, Word256(BigInt(1)), h) != CreateAddress.create2(s, Word256(BigInt(2)), h))
  }
}
