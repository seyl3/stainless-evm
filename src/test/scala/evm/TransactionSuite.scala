package evm

import stainless.collection.*
import stainless.lang.Map
import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*

class TransactionSuite extends munit.FunSuite {

  def code(bytes: Int*): Code =
    Code(bytes.foldRight(Nil[BigInt](): List[BigInt])((b, acc) => Cons(BigInt(b), acc)))

  val to: Address = Address(BigInt(0x1000))

  def worldWith(c: Code): WorldState =
    WorldState(Map(to -> Account(Word256.Zero, c)))

  val sender: Address = Address(BigInt(1))

  def tx(gasLimit: BigInt, data: List[BigInt] = Nil(), nonce: BigInt = 0): Transaction =
    Transaction(sender, to, Word256.Zero, gasLimit, Word256.Zero, Word256.Zero, nonce, data)

  test("a simple transaction runs the recipient code and bills intrinsic plus execution gas") {
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(code(0x60, 0x01, 0x00)))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasUsed, BigInt(21003))
  }

  test("a transaction with gas below the intrinsic cost fails and consumes its whole limit") {
    val res = Transaction.run(tx(20000), BlockContext.empty, worldWith(code(0x60, 0x01, 0x00)))
    assertEquals(res.status, Status.Failed)
    assertEquals(res.gasUsed, BigInt(20000))
  }

  test("clearing a dirty slot back to its original grants a refund capped at gasUsed/5") {
    val program = code(0x60, 0x05, 0x60, 0x01, 0x55, 0x60, 0x00, 0x60, 0x01, 0x55, 0x00)
    val res = Transaction.run(tx(100000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasRefunded, BigInt(8642))
    assertEquals(res.gasUsed, BigInt(34570))
  }

  test("a reverting transaction reports Reverted, grants no refund and commits no storage") {
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(code(0x60, 0x00, 0x60, 0x00, 0xFD)))
    assertEquals(res.status, Status.Reverted)
    assertEquals(res.gasRefunded, BigInt(0))
    assertEquals(res.world.storageOf(to).load(Word256(BigInt(1))).value, BigInt(0))
  }

  test("RETURN sets the transaction output to the returned memory region") {
    // MSTORE8 0xAB at offset 0, then RETURN offset 0 length 1
    val program = code(0x60, 0xAB, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xF3)
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.returnData.size, BigInt(1))
    assertEquals(res.returnData.head, BigInt(0xAB))
  }

  test("REVERT returns its data at the transaction boundary") {
    val program = code(0x60, 0xAB, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xFD)
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Reverted)
    assertEquals(res.returnData.size, BigInt(1))
    assertEquals(res.returnData.head, BigInt(0xAB))
  }

  test("the recipient account is pre-warmed so BALANCE on self is warm") {
    // PUSH2 0x1000 (== to), BALANCE, STOP: warm access costs 100, not cold 2600
    val res = Transaction.run(tx(30000), BlockContext.empty, worldWith(code(0x61, 0x10, 0x00, 0x31, 0x00)))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasUsed, BigInt(21103))
  }

  test("intrinsic gas charges 16 per nonzero and 4 per zero calldata byte") {
    val data: List[BigInt] = Cons(BigInt(0x00), Cons(BigInt(0xFF), Nil()))
    assertEquals(Transaction.intrinsicGas(data), BigInt(21000 + 4 + 16))
  }

  test("storage persists across transactions through the world state") {
    // contract increments slot 0: PUSH0key SLOAD PUSH1 ADD PUSH0key SSTORE STOP
    val counter = code(0x60, 0x00, 0x54, 0x60, 0x01, 0x01, 0x60, 0x00, 0x55, 0x00)
    val w0 = worldWith(counter)
    val r1 = Transaction.run(tx(100000), BlockContext.empty, w0)
    assertEquals(r1.status, Status.Halted)
    assertEquals(r1.world.storageOf(to).load(Word256.Zero).value, BigInt(1))
    // second tx runs against the world produced by the first
    val r2 = Transaction.run(tx(100000, nonce = 1), BlockContext.empty, r1.world)
    assertEquals(r2.world.storageOf(to).load(Word256.Zero).value, BigInt(2))
  }

  test("a reverting transaction does not persist its storage writes") {
    // SSTORE slot 0 = 7, then REVERT
    val program = code(0x60, 0x07, 0x60, 0x00, 0x55, 0x60, 0x00, 0x60, 0x00, 0xFD)
    val res = Transaction.run(tx(100000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Reverted)
    assertEquals(res.world.storageOf(to).load(Word256.Zero).value, BigInt(0))
  }

  val callee: Address = Address(BigInt(0x2000))

  // caller: STATICCALL(gas=50000, callee, no args, no ret), then MSTORE8 the
  // success flag at 0 and RETURN 1 byte.
  def callerReturningFlag: Code = code(
    0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x61, 0x20, 0x00, 0x61, 0xC3, 0x50, 0xFA,
    0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xF3)

  test("STATICCALL runs a child frame and returns its success flag") {
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256.Zero, callerReturningFlag),
      callee -> Account(Word256.Zero, code(0x00))))   // callee: STOP -> success
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.returnData.head, BigInt(1))
  }

  test("STATICCALL to a failing callee returns zero") {
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256.Zero, callerReturningFlag),
      callee -> Account(Word256.Zero, code(0xFE))))    // callee: INVALID -> failure
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.returnData.head, BigInt(0))
  }

  test("STATICCALL exposes the child's return data to the caller (RETURNDATACOPY)") {
    // callee returns the byte 0x42
    val calleeCode = code(0x60, 0x42, 0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xF3)
    // caller STATICCALLs, then RETURNDATACOPY(dest=0, off=0, len=1) and RETURN [0,1]
    val callerCode = code(
      0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x61, 0x20, 0x00, 0x61, 0xC3, 0x50, 0xFA,
      0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0x3E, 0x60, 0x01, 0x60, 0x00, 0xF3)
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256.Zero, callerCode),
      callee -> Account(Word256.Zero, calleeCode)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.returnData.head, BigInt(0x42))
  }

  test("DELEGATECALL runs the target's code against the caller's own storage") {
    // target SSTOREs slot 0 = 0x42
    val targetCode = code(0x60, 0x42, 0x60, 0x00, 0x55, 0x00)
    // caller DELEGATECALLs the target then STOPs
    val callerCode = code(
      0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x61, 0x20, 0x00, 0x61, 0xC3, 0x50, 0xF4, 0x00)
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256.Zero, callerCode),
      callee -> Account(Word256.Zero, targetCode)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    // the write landed in the CALLER's storage, not the target's
    assertEquals(res.world.storageOf(to).load(Word256.Zero).value, BigInt(0x42))
    assertEquals(res.world.storageOf(callee).load(Word256.Zero).value, BigInt(0))
  }

  test("CALL transfers value and runs the callee in its own storage") {
    // callee stores its received CALLVALUE into slot 0
    val calleeCode = code(0x34, 0x60, 0x00, 0x55, 0x00)
    // caller CALLs callee with value 5 (gas 50000, no args/ret), then STOPs
    val callerCode = code(
      0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x05, 0x61, 0x20, 0x00, 0x61, 0xC3, 0x50,
      0xF1, 0x00)
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256(BigInt(100)), callerCode),
      callee -> Account(Word256.Zero, calleeCode)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.world.balanceOf(callee).value, BigInt(5))
    assertEquals(res.world.balanceOf(to).value, BigInt(95))
    assertEquals(res.world.storageOf(callee).load(Word256.Zero).value, BigInt(5))
    assertEquals(res.world.storageOf(to).load(Word256.Zero).value, BigInt(0))
  }

  test("CALL with insufficient balance fails and moves no value") {
    val calleeCode = code(0x34, 0x60, 0x00, 0x55, 0x00)
    // caller CALLs with value 200 (> its 100 balance), then STOPs
    val callerCode = code(
      0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0xC8, 0x61, 0x20, 0x00, 0x61, 0xC3, 0x50,
      0xF1, 0x00)
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256(BigInt(100)), callerCode),
      callee -> Account(Word256.Zero, calleeCode)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.world.balanceOf(to).value, BigInt(100))
    assertEquals(res.world.balanceOf(callee).value, BigInt(0))
  }

  test("SELFDESTRUCT sends the contract's whole balance to the beneficiary") {
    val beneficiary = Address(BigInt(0x3000))
    // contract PUSHes the beneficiary and SELFDESTRUCTs
    val program = code(0x61, 0x30, 0x00, 0xFF)
    val world = WorldState(stainless.lang.Map(to -> Account(Word256(BigInt(50)), program)))
    val res = Transaction.run(tx(100000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.world.balanceOf(beneficiary).value, BigInt(50))
    assertEquals(res.world.balanceOf(to).value, BigInt(0))
  }

  test("CALLCODE runs the target's code against the caller's storage") {
    // target SSTOREs its CALLVALUE into slot 0
    val targetCode = code(0x34, 0x60, 0x00, 0x55, 0x00)
    // caller CALLCODEs the target with value 7 then STOPs
    val callerCode = code(
      0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x07, 0x61, 0x20, 0x00, 0x61, 0xC3, 0x50,
      0xF2, 0x00)
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256(BigInt(100)), callerCode),
      callee -> Account(Word256.Zero, targetCode)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    // the SSTORE landed in the caller's storage (value 7), target's stays 0
    assertEquals(res.world.storageOf(to).load(Word256.Zero).value, BigInt(7))
    assertEquals(res.world.storageOf(callee).load(Word256.Zero).value, BigInt(0))
  }

  test("KECCAK256 of an empty region returns the empty keccak hash") {
    // KECCAK256(len=0, off=0), MSTORE it at 0, RETURN [0,32]
    val program = code(0x60, 0x00, 0x60, 0x00, 0x20, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xF3)
    val res = Transaction.run(tx(100000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.returnData.size, BigInt(32))
    val v = res.returnData.foldLeft(BigInt(0))((acc, b) => (acc << 8) | b)
    assertEquals(v, BigInt("c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470", 16))
  }

  test("EXTCODEHASH of an existing account is the keccak of its code") {
    val program = code(0x61, 0x20, 0x00, 0x3F, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xF3)
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256.Zero, program),
      callee -> Account(Word256.Zero, code(0x00))))
    val res = Transaction.run(tx(100000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    val v = res.returnData.foldLeft(BigInt(0))((acc, b) => (acc << 8) | b)
    assertEquals(v, BigInt("bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a", 16))
  }

  test("EXTCODEHASH of an absent account is zero") {
    val program = code(0x61, 0x99, 0x99, 0x3F, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xF3)
    val res = Transaction.run(tx(100000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    val v = res.returnData.foldLeft(BigInt(0))((acc, b) => (acc << 8) | b)
    assertEquals(v, BigInt(0))
  }

  test("EXTCODECOPY copies external code into memory zero-padded") {
    val program = code(
      0x60, 0x04, 0x60, 0x00, 0x60, 0x00, 0x61, 0x20, 0x00, 0x3C,
      0x60, 0x04, 0x60, 0x00, 0xF3)
    val world = WorldState(stainless.lang.Map(
      to -> Account(Word256.Zero, program),
      callee -> Account(Word256.Zero, code(0x60, 0x2A, 0x00))))
    val res = Transaction.run(tx(100000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.returnData, Cons(BigInt(0x60), Cons(BigInt(0x2A), Cons(BigInt(0x00), Cons(BigInt(0x00), Nil())))))
  }

  test("a transaction transfers its value to the recipient and bumps the sender nonce") {
    val world = WorldState(stainless.lang.Map(
      sender -> Account(Word256(BigInt(100)), Code.empty),
      to -> Account(Word256.Zero, code(0x00))))
    val t = Transaction(sender, to, Word256(BigInt(10)), 30000, Word256.Zero, Word256.Zero, 0, Nil())
    val res = Transaction.run(t, BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.world.balanceOf(sender).value, BigInt(90))
    assertEquals(res.world.balanceOf(to).value, BigInt(10))
    assertEquals(res.world.nonceOf(sender), BigInt(1))
  }

  test("a transaction whose sender cannot afford value plus fees is invalid") {
    val world = WorldState(stainless.lang.Map(
      sender -> Account(Word256(BigInt(100)), Code.empty),
      to -> Account(Word256.Zero, code(0x00))))
    val t = Transaction(sender, to, Word256(BigInt(200)), 30000, Word256.Zero, Word256.Zero, 0, Nil())
    val res = Transaction.run(t, BlockContext.empty, world)
    assertEquals(res.status, Status.Failed)
    assertEquals(res.gasUsed, BigInt(0))
    assertEquals(res.world.balanceOf(sender).value, BigInt(100))
    assertEquals(res.world.nonceOf(sender), BigInt(0))
  }

  test("a transaction with the wrong nonce is invalid") {
    val res = Transaction.run(tx(30000, nonce = 5), BlockContext.empty, worldWith(code(0x00)))
    assertEquals(res.status, Status.Failed)
    assertEquals(res.gasUsed, BigInt(0))
  }

  test("EIP-1559: the sender pays the effective price and the coinbase earns the tip") {
    val coinbase = Address(BigInt(0xC0))
    val block = BlockContext(coinbase, Word256.Zero, Word256.Zero, Word256.Zero,
      Word256.Zero, Word256.Zero, Word256(BigInt(2)), Word256.Zero, stainless.lang.Map.empty[Word256, Word256])
    val world = WorldState(stainless.lang.Map(
      sender -> Account(Word256(BigInt(100000)), Code.empty),
      to -> Account(Word256.Zero, code(0x00))))
    val t = Transaction(sender, to, Word256.Zero, 30000,
      Word256(BigInt(3)), Word256(BigInt(1)), 0, Nil())
    val res = Transaction.run(t, block, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasUsed, BigInt(21000))
    assertEquals(res.world.balanceOf(sender).value, BigInt(100000 - 21000 * 3))
    assertEquals(res.world.balanceOf(coinbase).value, BigInt(21000))
  }

  test("a transaction whose max fee is below the base fee is invalid") {
    val block = BlockContext(Address.zero, Word256.Zero, Word256.Zero, Word256.Zero,
      Word256.Zero, Word256.Zero, Word256(BigInt(5)), Word256.Zero, stainless.lang.Map.empty[Word256, Word256])
    val world = WorldState(stainless.lang.Map(
      sender -> Account(Word256(BigInt(1000000)), Code.empty),
      to -> Account(Word256.Zero, code(0x00))))
    val t = Transaction(sender, to, Word256.Zero, 30000,
      Word256(BigInt(3)), Word256.Zero, 0, Nil())
    val res = Transaction.run(t, block, world)
    assertEquals(res.status, Status.Failed)
    assertEquals(res.gasUsed, BigInt(0))
  }

  test("a reverting transaction still pays fees and keeps the nonce bump but rolls back the value") {
    val world = WorldState(stainless.lang.Map(
      sender -> Account(Word256(BigInt(100)), Code.empty),
      to -> Account(Word256.Zero, code(0x60, 0x00, 0x60, 0x00, 0xFD))))
    val t = Transaction(sender, to, Word256(BigInt(10)), 30000, Word256.Zero, Word256.Zero, 0, Nil())
    val res = Transaction.run(t, BlockContext.empty, world)
    assertEquals(res.status, Status.Reverted)
    assertEquals(res.world.balanceOf(sender).value, BigInt(100))
    assertEquals(res.world.balanceOf(to).value, BigInt(0))
    assertEquals(res.world.nonceOf(sender), BigInt(1))
  }

  test("GASPRICE pushes the effective gas price") {
    val block = BlockContext(Address.zero, Word256.Zero, Word256.Zero, Word256.Zero,
      Word256.Zero, Word256.Zero, Word256(BigInt(2)), Word256.Zero, stainless.lang.Map.empty[Word256, Word256])
    val program = code(0x3A, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xF3)
    val world = WorldState(stainless.lang.Map(
      sender -> Account(Word256(BigInt(1000000)), Code.empty),
      to -> Account(Word256.Zero, program)))
    val t = Transaction(sender, to, Word256.Zero, 100000,
      Word256(BigInt(3)), Word256(BigInt(1)), 0, Nil())
    val res = Transaction.run(t, block, world)
    assertEquals(res.status, Status.Halted)
    val v = res.returnData.foldLeft(BigInt(0))((acc, b) => (acc << 8) | b)
    assertEquals(v, BigInt(3))
  }

  test("EIP-7623: a calldata-heavy low-execution tx is charged the token floor") {
    val data: List[BigInt] = Cons(BigInt(0xFF), Cons(BigInt(0xFF), Nil()))
    // tokens = 8; floor = 21000 + 80 = 21080; standard intrinsic = 21000 + 32 = 21032; STOP adds 0
    val res = Transaction.run(
      Transaction(sender, to, Word256.Zero, 30000, Word256.Zero, Word256.Zero, 0, data),
      BlockContext.empty, worldWith(code(0x00)))
    assertEquals(res.status, Status.Halted)
    assertEquals(res.gasUsed, BigInt(21080))
  }

  // Helper: read a 32-byte returnData word (a returned address) as a BigInt.
  def returnedWord(res: TxResult): BigInt =
    res.returnData.foldLeft(BigInt(0))((acc, b) => (acc << 8) | b)

  test("CREATE deploys a contract at the derived address and bumps the creator nonce") {
    // CREATE(value=0, off=0, len=1) over mem[0]=0x00 (memory is zero, so initcode is STOP),
    // then MSTORE the returned address and RETURN it
    val program = code(0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0xF0, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xF3)
    val res = Transaction.run(tx(200000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    val expected = CreateAddress.create(to, 0)
    assertEquals(returnedWord(res), expected.value)
    assertEquals(res.world.nonceOf(to), BigInt(1))
    assert(res.world.accounts.contains(expected))
    assertEquals(res.world.codeOf(expected).size, BigInt(0)) // STOP initcode returns no code
  }

  test("CREATE installs the runtime code returned by the initcode") {
    // initcode 0x6001600 0f3 (PUSH1 1, PUSH1 0, RETURN) returns mem[0:1] = 0x00, a 1-byte STOP.
    // Outer: PUSH5 the initcode, MSTORE at 0 (lands in mem[27:32]), CREATE(0, 27, 5), STOP.
    val program = code(
      0x64, 0x60, 0x01, 0x60, 0x00, 0xF3, 0x60, 0x00, 0x52,
      0x60, 0x05, 0x60, 0x1B, 0x60, 0x00, 0xF0, 0x00)
    val res = Transaction.run(tx(200000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    val created = CreateAddress.create(to, 0)
    assertEquals(res.world.codeOf(created).code, Cons(BigInt(0), Nil[BigInt]()))
  }

  test("CREATE2 deploys at the salted address") {
    // Same initcode as above, via CREATE2 with salt 0x99: push salt, len, off, value.
    val program = code(
      0x64, 0x60, 0x01, 0x60, 0x00, 0xF3, 0x60, 0x00, 0x52,
      0x60, 0x99, 0x60, 0x05, 0x60, 0x1B, 0x60, 0x00, 0xF5, 0x00)
    val res = Transaction.run(tx(200000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    val initcode: List[BigInt] = Cons(BigInt(0x60), Cons(BigInt(0x01), Cons(BigInt(0x60), Cons(BigInt(0x00), Cons(BigInt(0xF3), Nil())))))
    val expected = CreateAddress.create2(to, Word256(BigInt(0x99)), Keccak256.hash(initcode))
    assert(res.world.accounts.contains(expected))
    assertEquals(res.world.codeOf(expected).code, Cons(BigInt(0), Nil[BigInt]()))
  }

  test("CREATE transfers value to the new contract") {
    // CREATE(value=100, off=0, len=1); the creator (to) is funded with 100.
    val program = code(0x60, 0x01, 0x60, 0x00, 0x60, 0x64, 0xF0, 0x00)
    val world = WorldState(Map(to -> Account(Word256(BigInt(100)), program)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    val created = CreateAddress.create(to, 0)
    assertEquals(res.world.balanceOf(created).value, BigInt(100))
    assertEquals(res.world.balanceOf(to).value, BigInt(0))
  }

  test("CREATE with reverting initcode pushes zero but keeps the nonce bump") {
    // initcode 0x6000600 0fd (PUSH1 0, PUSH1 0, REVERT); outer MSTOREs the result and returns it.
    val program = code(
      0x64, 0x60, 0x00, 0x60, 0x00, 0xFD, 0x60, 0x00, 0x52,
      0x60, 0x05, 0x60, 0x1B, 0x60, 0x00, 0xF0, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xF3)
    val res = Transaction.run(tx(200000), BlockContext.empty, worldWith(program))
    assertEquals(res.status, Status.Halted)
    assertEquals(returnedWord(res), BigInt(0)) // CREATE returned 0 (failure)
    assertEquals(res.world.nonceOf(to), BigInt(1)) // nonce bump persists
    assert(!res.world.accounts.contains(CreateAddress.create(to, 0)))
  }

  test("EIP-6780: SELFDESTRUCT of a same-transaction CREATE deletes the account") {
    // outer CREATEs (value 100) a contract whose initcode is PUSH1 0x99, SELFDESTRUCT.
    // The new contract is created and destroyed in one tx, so it is deleted; its value
    // escapes to the beneficiary 0x99.
    val program = code(
      0x62, 0x60, 0x99, 0xFF, 0x60, 0x00, 0x52,
      0x60, 0x03, 0x60, 0x1D, 0x60, 0x64, 0xF0, 0x00)
    val world = WorldState(Map(to -> Account(Word256(BigInt(100)), program)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    val created = CreateAddress.create(to, 0)
    assertEquals(res.world.balanceOf(Address(BigInt(0x99))).value, BigInt(100)) // value escaped
    assertEquals(res.world.balanceOf(created).value, BigInt(0))
    assertEquals(res.world.codeOf(created).size, BigInt(0)) // account deleted
  }

  test("EIP-6780: SELFDESTRUCT of a pre-existing contract keeps its code") {
    // to is pre-existing (not created this tx): PUSH1 0x99, SELFDESTRUCT. Only the
    // balance moves; the code survives.
    val program = code(0x60, 0x99, 0xFF)
    val world = WorldState(Map(to -> Account(Word256(BigInt(50)), program)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.world.balanceOf(Address(BigInt(0x99))).value, BigInt(50))
    assertEquals(res.world.codeOf(to).size, BigInt(3)) // not deleted
  }

  test("CREATE inside a STATICCALL fails (read-only context)") {
    // to STATICCALLs callee; callee's code does CREATE then STOP. The CREATE must fail,
    // so the whole callee frame fails and STATICCALL returns 0.
    val calleeCode = code(0x60, 0x01, 0x60, 0x00, 0x60, 0x00, 0xF0, 0x00)
    val callerCode = code(
      0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x61, 0x20, 0x00, 0x61, 0xC3, 0x50, 0xFA,
      0x60, 0x00, 0x53, 0x60, 0x01, 0x60, 0x00, 0xF3)
    val world = WorldState(Map(
      to -> Account(Word256.Zero, callerCode),
      callee -> Account(Word256.Zero, calleeCode)))
    val res = Transaction.run(tx(200000), BlockContext.empty, world)
    assertEquals(res.status, Status.Halted)
    assertEquals(res.returnData.head, BigInt(0)) // STATICCALL failed
  }
}
