package evm.exec

import stainless.lang.*
import stainless.collection.*
import evm.value.Word256
import evm.value.Keccak256
import evm.math.Gas
import evm.math.EvmMath
import evm.math.EvmMath.MAX_VALUE
import evm.math.ByteList
import evm.math.Bytes
import evm.state.Stack
import evm.code.Opcode
import evm.code.Code
import evm.env.Address
import evm.env.CreateAddress
import evm.env.Log
import evm.env.WorldState

// Result of preparing a call: either a state to continue the parent from (the
// call was rejected or the frame failed), or a child frame to run plus the
// gas-forwarded parent to merge the result into.
sealed abstract class CallPrep
case class CallReject(state: ExecState) extends CallPrep
// On a successful child: commitState says whether to commit its effects at all
// (false for STATICCALL); self is the child's own account (its storage is written
// back into the world there); sameAccount means the child ran on the parent's own
// storage (DELEGATECALL), so the parent's storage reflects the child's; preWorld is
// the world to restore if the child fails/reverts (rolls back value transfer too);
// retOff/retLen is the caller memory region the child's return data is written to.
case class CallEnter(child: ExecState, parentForwarded: ExecState, rest: Stack, forwarded: BigInt,
                     commitState: Boolean, sameAccount: Boolean, self: Address, preWorld: WorldState,
                     retOff: BigInt, retLen: BigInt) extends CallPrep:
  require(retOff >= 0 && retLen >= 0)

// The analogue for CREATE/CREATE2: a rejected creation (push 0, continue the
// parent) or an initcode frame to run. newAddr is the derived contract address;
// preWorld is the world to restore on initcode failure (the creator's nonce has
// already been incremented in it, so that increment persists, but the value
// transfer is rolled back).
sealed abstract class CreatePrep
case class CreateReject(state: ExecState) extends CreatePrep
case class CreateEnter(child: ExecState, parentForwarded: ExecState, rest: Stack, forwarded: BigInt,
                       newAddr: Address, preWorld: WorldState) extends CreatePrep

// The interpreter. `step` charges base gas and dispatches one opcode to a helper;
// `run` iterates step to completion and also handles the recursive call opcodes.
// Each helper takes and returns an ExecState and carries a functional
// postcondition of the form `r.isRunning ==> (exact effect)`, so correctness (not
// just safety) is proven per opcode. A stack underflow, gas exhaustion, or bad
// jump routes to `fail`. On the fallback smt-z3 solver a helper must fold its
// changes into a single `copy` rather than chaining copies, or the VC blows up.
object Interpreter:

  // Memory-expansion gas for an access reaching byte `end`, in words.
  def memExpandCost(st: ExecState, end: BigInt): BigInt = {
    require(end >= 0)
    Gas.memoryExpansionCost(st.memory.size / 32, st.memory.expandedTo(end) / 32)
  }.ensuring(r => r >= 0)

  // Push a constant word (PUSH0 and the environment reads route here), advancing
  // the pc by one; fails on stack overflow.
  def pushConst(st: ExecState, v: Word256): ExecState = {
    if (st.stack.data.size >= Stack.MAXIMUM_STACK_SIZE) st.fail
    else st.copy(stack = st.stack.push(v)).advancePc(1)
  }.ensuring(r =>
    (!r.isRunning || r.gas == st.gas)
    && ((st.isRunning && st.stack.data.size < Stack.MAXIMUM_STACK_SIZE) ==>
         (r.isRunning && r.gas == st.gas && r.pc == st.pc + 1
          && r.stack.data.head == v
          && r.stack.data.tail == st.stack.data)))

  // The arithmetic/bitwise/comparison dispatch shared by most opcodes: pop 1, 2,
  // or 3 words, push f applied to them, advance the pc. The passed f is the
  // opcode's Word256 operation, so the postcondition pins the exact result.
  def unop(st: ExecState, f: Word256 => Word256): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (a, t) = st.stack.pop()
      st.copy(stack = t.push(f(a))).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas == st.gas)
    && ((st.isRunning && st.stack.data.nonEmpty) ==>
         (r.isRunning && r.gas == st.gas && r.pc == st.pc + 1
          && r.stack.data.head == f(st.stack.data.head)
          && r.stack.data.tail == st.stack.data.tail)))

  def binop(st: ExecState, f: (Word256, Word256) => Word256): ExecState = {
    if (st.stack.data.size < 2) st.fail
    else {
      val (a, t1) = st.stack.pop()
      val (b, t2) = t1.pop()
      st.copy(stack = t2.push(f(a, b))).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas == st.gas)
    && ((st.isRunning && st.stack.data.size >= 2) ==>
         (r.isRunning && r.gas == st.gas && r.pc == st.pc + 1
          && r.stack.data.head == f(st.stack.data.head, st.stack.data.tail.head)
          && r.stack.data.tail == st.stack.data.tail.tail)))

  def terop(st: ExecState, f: (Word256, Word256, Word256) => Word256): ExecState = {
    if (st.stack.data.size < 3) st.fail
    else {
      val (a, t1) = st.stack.pop()
      val (b, t2) = t1.pop()
      val (c, t3) = t2.pop()
      st.copy(stack = t3.push(f(a, b, c))).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas == st.gas)
    && ((st.isRunning && st.stack.data.size >= 3) ==>
         (r.isRunning && r.gas == st.gas && r.pc == st.pc + 1
          && r.stack.data.head == f(st.stack.data.head, st.stack.data.tail.head, st.stack.data.tail.tail.head)
          && r.stack.data.tail == st.stack.data.tail.tail.tail)))

  // PUSHn / DUPn / SWAPn / POP. pushN reads the n-byte immediate after the opcode
  // and advances past it; dupN clones the nth item; swapN exchanges top and nth.
  def pushN(st: ExecState, n: BigInt): ExecState = {
    require(0 <= n && n <= 32)
    if (st.stack.data.size >= Stack.MAXIMUM_STACK_SIZE) st.fail
    else st.copy(stack = st.stack.push(st.code.pushValue(st.pc + 1, n))).advancePc(1 + n)
  }.ensuring(r =>
    (!r.isRunning || r.gas == st.gas)
    && ((st.isRunning && st.stack.data.size < Stack.MAXIMUM_STACK_SIZE) ==>
         (r.isRunning && r.gas == st.gas && r.pc == st.pc + 1 + n
          && r.stack.data.head == st.code.pushValue(st.pc + 1, n)
          && r.stack.data.tail == st.stack.data)))

  def dupN(st: ExecState, n: BigInt): ExecState = {
    require(1 <= n && n <= 16)
    if (st.stack.data.size < n || st.stack.data.size >= Stack.MAXIMUM_STACK_SIZE) st.fail
    else st.copy(stack = st.stack.dup(n)).advancePc(1)
  }.ensuring(r =>
    (!r.isRunning || r.gas == st.gas)
    && ((st.isRunning && n <= st.stack.data.size && st.stack.data.size < Stack.MAXIMUM_STACK_SIZE) ==>
         (r.isRunning && r.gas == st.gas && r.pc == st.pc + 1
          && r.stack.data.head == st.stack.data(n - 1)
          && r.stack.data.tail == st.stack.data)))

  def swapN(st: ExecState, n: BigInt): ExecState = {
    require(1 <= n && n <= 16)
    if (st.stack.data.size <= n) st.fail
    else st.copy(stack = st.stack.swap(n)).advancePc(1)
  }.ensuring(r =>
    (!r.isRunning || r.gas == st.gas)
    && ((st.isRunning && n < st.stack.data.size) ==>
         (r.isRunning && r.gas == st.gas && r.pc == st.pc + 1
          && r.stack.data(0) == st.stack.data(n)
          && r.stack.data(n) == st.stack.data(0))))

  def popOp(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else st.copy(stack = st.stack.pop()._2).advancePc(1)
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail)))

  // MLOAD / MSTORE / MSTORE8: read or write memory, charging the expansion gas for
  // growing active memory to cover the access. MSTORE8 writes a single byte.
  def mload(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (o, t) = st.stack.pop()
      val extra = memExpandCost(st, o.value + 32)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t.push(st.memory.load(o.value)),
             memory = st.memory.expand(o.value + 32)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty && r.pc == st.pc + 1
          && r.stack.data.head == st.memory.load(st.stack.data.head.value)
          && r.stack.data.tail == st.stack.data.tail)))

  def mstore(st: ExecState): ExecState = {
    if (st.stack.data.size < 2) st.fail
    else {
      val (o, t1) = st.stack.pop()
      val (v, t2) = t1.pop()
      val extra = memExpandCost(st, o.value + 32)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t2, memory = st.memory.store(o.value, v)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 2 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail
          && r.memory.load(st.stack.data.head.value).value == st.stack.data.tail.head.value)))

  def mstore8(st: ExecState): ExecState = {
    if (st.stack.data.size < 2) st.fail
    else {
      val (o, t1) = st.stack.pop()
      val (v, t2) = t1.pop()
      val extra = memExpandCost(st, o.value + 1)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t2, memory = st.memory.store8(o.value, v)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 2 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail
          && r.memory.getByte(st.stack.data.head.value) == st.stack.data.tail.head.value % 256)))

  // MCOPY: in-memory block copy, charging per-word plus expansion to the furthest
  // of the source and destination ranges. A zero-length copy is free of both.
  def mcopyOp(st: ExecState): ExecState = {
    if (st.stack.data.size < 3) st.fail
    else {
      val (d, t1) = st.stack.pop()
      val (sr, t2) = t1.pop()
      val (l, t3) = t2.pop()
      val end = if (d.value > sr.value) d.value + l.value else sr.value + l.value
      val extra = if (l.value == 0) BigInt(0) else 3 * Gas.words(l.value) + memExpandCost(st, end)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t3, memory = st.memory.mcopy(d.value, sr.value, l.value)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 3 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail.tail
          && r.memory == st.memory.mcopy(st.stack.data.head.value,
               st.stack.data.tail.head.value, st.stack.data.tail.tail.head.value))))

  // BALANCE / EXTCODESIZE: read another account, paying the EIP-2929 cold surcharge
  // (2500 over the warm base) on first touch and marking it warm afterward.
  def balanceOp(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (a, t) = st.stack.pop()
      val addr = Address.fromWord(a)
      val extra = if (st.accessedAccounts.contains(addr)) BigInt(0) else BigInt(2500)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t.push(st.world.balanceOf(addr)),
             accessedAccounts = st.accessedAccounts ++ Set(addr)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty && r.pc == st.pc + 1
          && r.stack.data.head == st.world.balanceOf(Address.fromWord(st.stack.data.head))
          && r.stack.data.tail == st.stack.data.tail
          && r.accessedAccounts.contains(Address.fromWord(st.stack.data.head)))))

  def extcodesizeOp(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (a, t) = st.stack.pop()
      val addr = Address.fromWord(a)
      val extra = if (st.accessedAccounts.contains(addr)) BigInt(0) else BigInt(2500)
      val sz = st.world.codeOf(addr).size
      if (st.outOfGas(extra) || sz > MAX_VALUE) st.fail
      else st.chargeGas(extra).copy(stack = t.push(Word256(sz)),
             accessedAccounts = st.accessedAccounts ++ Set(addr)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty && r.pc == st.pc + 1
          && r.stack.data.head.value == st.world.codeOf(Address.fromWord(st.stack.data.head)).size
          && r.stack.data.tail == st.stack.data.tail
          && r.accessedAccounts.contains(Address.fromWord(st.stack.data.head)))))

  // TLOAD / TSTORE: EIP-1153 transient storage, flat-priced with no cold/warm and
  // cleared at end of transaction. TSTORE fails in a static context.
  def tload(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (k, t) = st.stack.pop()
      st.copy(stack = t.push(st.transient.load(k))).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty && r.pc == st.pc + 1
          && r.stack.data.head == st.transient.load(st.stack.data.head)
          && r.stack.data.tail == st.stack.data.tail)))

  def tstore(st: ExecState): ExecState = {
    if (st.static || st.stack.data.size < 2) st.fail
    else {
      val (k, t1) = st.stack.pop()
      val (v, t2) = t1.pop()
      st.copy(stack = t2, transient = st.transient.store(k, v)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 2 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail
          && r.transient.load(st.stack.data.head) == st.stack.data.tail.head)))

  // SLOAD: read a storage slot, paying the cold surcharge (2000 over the warm base)
  // on first access this tx and marking the slot warm.
  def sload(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (k, t) = st.stack.pop()
      val extra = if (st.accessedSlots.contains(k)) BigInt(0) else BigInt(2000)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t.push(st.storage.load(k)),
             accessedSlots = st.accessedSlots ++ Set(k)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty && r.pc == st.pc + 1
          && r.stack.data.head == st.storage.load(st.stack.data.head)
          && r.stack.data.tail == st.stack.data.tail
          && r.accessedSlots.contains(st.stack.data.head))))

  // SSTORE: write a storage slot. Fails in a static context or below the EIP-2200
  // stipend sentry (gas must exceed 2300). The charge and refund come from Gas,
  // keyed on the slot's original (start-of-tx), current, and new values; the base
  // 100 is subtracted here because step already charged it. Updates the refund
  // counter (EIP-3529).
  def sstore(st: ExecState): ExecState = {
    if (st.static || st.stack.data.size < 2 || st.gas + 100 <= 2300) st.fail
    else {
      val (k, t1) = st.stack.pop()
      val (v, t2) = t1.pop()
      val cold = !st.accessedSlots.contains(k)
      val extra = Gas.sstoreCost(st.original.load(k).value, st.storage.load(k).value, v.value, cold) - 100
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t2, storage = st.storage.store(k, v),
             accessedSlots = st.accessedSlots ++ Set(k),
             refund = st.refund + Gas.sstoreRefund(st.original.load(k).value, st.storage.load(k).value, v.value)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 2 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail
          && r.storage.load(st.stack.data.head) == st.stack.data.tail.head
          && r.accessedSlots.contains(st.stack.data.head))))

  // JUMP / JUMPI: set the pc to the target, but only if it is a valid JUMPDEST
  // (per the code's precomputed analysis); otherwise fail. JUMPI jumps only when
  // the condition is nonzero, else falls through.
  def jump(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (d, t) = st.stack.pop()
      if (st.code.isValidJumpDest(d.value)) st.copy(stack = t, pc = d.value)
      else st.fail
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty
          && st.code.isValidJumpDest(st.stack.data.head.value)
          && r.pc == st.stack.data.head.value
          && r.stack.data == st.stack.data.tail)))

  def jumpi(st: ExecState): ExecState = {
    if (st.stack.data.size < 2) st.fail
    else {
      val (d, t1) = st.stack.pop()
      val (cond, t2) = t1.pop()
      if (cond.isZero) st.copy(stack = t2).advancePc(1)
      else if (st.code.isValidJumpDest(d.value)) st.copy(stack = t2, pc = d.value)
      else st.fail
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 2
          && r.stack.data == st.stack.data.tail.tail
          && (if (st.stack.data.tail.head.isZero) r.pc == st.pc + 1
              else st.code.isValidJumpDest(st.stack.data.head.value)
                   && r.pc == st.stack.data.head.value))))

  // RETURN / REVERT: capture the memory region [offset, offset+len) as the frame's
  // return data and stop. RETURN halts (success); REVERT reverts (state rolled back
  // by the caller) but still surfaces the data.
  def returnOp(st: ExecState): ExecState = {
    if (st.stack.data.size < 2) st.fail
    else {
      val (o, t1) = st.stack.pop()
      val (l, t2) = t1.pop()
      val extra = if (l.value == 0) BigInt(0) else memExpandCost(st, o.value + l.value)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t2,
             returnData = Bytes.readList(st.memory.data, o.value, l.value),
             memory = if (l.value == 0) st.memory else st.memory.expand(o.value + l.value)).halt
    }
  }.ensuring(r =>
    !r.isRunning && r.gas <= st.gas
    && (r.status == Status.Halted ==>
         (st.stack.data.size >= 2
          && r.returnData == Bytes.readList(st.memory.data, st.stack.data.head.value, st.stack.data.tail.head.value))))

  def revertOp(st: ExecState): ExecState = {
    if (st.stack.data.size < 2) st.fail
    else {
      val (o, t1) = st.stack.pop()
      val (l, t2) = t1.pop()
      val extra = if (l.value == 0) BigInt(0) else memExpandCost(st, o.value + l.value)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t2,
             returnData = Bytes.readList(st.memory.data, o.value, l.value),
             memory = if (l.value == 0) st.memory else st.memory.expand(o.value + l.value)).revert
    }
  }.ensuring(r =>
    !r.isRunning && r.gas <= st.gas
    && (r.status == Status.Reverted ==>
         (st.stack.data.size >= 2
          && r.returnData == Bytes.readList(st.memory.data, st.stack.data.head.value, st.stack.data.tail.head.value))))

  // CALLDATALOAD: read a 32-byte word from calldata at offset, zero-padded past
  // the end. pow256Le(32) bounds the result to a Word256.
  def calldataload(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (o, t) = st.stack.pop()
      EvmMath.pow256Le(32)
      st.copy(stack = t.push(Word256(ByteList.readWord(st.msg.callData, o.value, 32)))).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty && r.pc == st.pc + 1
          && r.stack.data.head.value == ByteList.readWord(st.msg.callData, st.stack.data.head.value, 32)
          && r.stack.data.tail == st.stack.data.tail)))

  // CALLDATACOPY / CODECOPY / RETURNDATACOPY: copy a source region into memory,
  // zero-padded past the source end, charging per-word plus expansion. They differ
  // only in the source (calldata / this code / prior return data). RETURNDATACOPY
  // additionally fails if the read runs past the return data (no zero padding).
  def calldatacopy(st: ExecState): ExecState = {
    if (st.stack.data.size < 3) st.fail
    else {
      val (d, t1) = st.stack.pop()
      val (o, t2) = t1.pop()
      val (l, t3) = t2.pop()
      val extra = if (l.value == 0) BigInt(0) else 3 * Gas.words(l.value) + memExpandCost(st, d.value + l.value)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t3,
             memory = st.memory.copyIn(d.value, st.msg.callData, o.value, l.value)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 3 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail.tail
          && r.memory == st.memory.copyIn(st.stack.data.head.value, st.msg.callData,
               st.stack.data.tail.head.value, st.stack.data.tail.tail.head.value))))

  def codecopy(st: ExecState): ExecState = {
    if (st.stack.data.size < 3) st.fail
    else {
      val (d, t1) = st.stack.pop()
      val (o, t2) = t1.pop()
      val (l, t3) = t2.pop()
      val extra = if (l.value == 0) BigInt(0) else 3 * Gas.words(l.value) + memExpandCost(st, d.value + l.value)
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t3,
             memory = st.memory.copyIn(d.value, st.code.code, o.value, l.value)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 3 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail.tail
          && r.memory == st.memory.copyIn(st.stack.data.head.value, st.code.code,
               st.stack.data.tail.head.value, st.stack.data.tail.tail.head.value))))

  def returndatacopy(st: ExecState): ExecState = {
    if (st.stack.data.size < 3) st.fail
    else {
      val (d, t1) = st.stack.pop()
      val (o, t2) = t1.pop()
      val (l, t3) = t2.pop()
      if (o.value + l.value > st.returnData.size) st.fail
      else {
        val extra = if (l.value == 0) BigInt(0) else 3 * Gas.words(l.value) + memExpandCost(st, d.value + l.value)
        if (st.outOfGas(extra)) st.fail
        else st.chargeGas(extra).copy(stack = t3,
               memory = st.memory.copyIn(d.value, st.returnData, o.value, l.value)).advancePc(1)
      }
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 3 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail.tail)))

  // Pop the n topic words for a LOGn off the stack, in order.
  def popTopics(s: Stack, n: BigInt): (List[Word256], Stack) = {
    require(n >= 0 && s.data.size >= n)
    decreases(n)
    if (n == 0) (Nil[Word256](), s)
    else {
      val (top, rest) = s.pop()
      val (more, remaining) = popTopics(rest, n - 1)
      (top :: more, remaining)
    }
  }.ensuring(r =>
    r._2.data.size == s.data.size - n
    && r._1 == s.data.take(n)
    && r._2.data == s.data.drop(n))

  // LOG0-4: append a log record (emitter, n topics, memory data region) to the
  // frame's log list, charging 8 per data byte plus expansion. Fails in a static
  // context. The postcondition pins the exact record appended.
  def logN(st: ExecState, n: BigInt): ExecState = {
    require(0 <= n && n <= 4)
    if (st.static || st.stack.data.size < 2 + n) st.fail
    else {
      val (o, t1) = st.stack.pop()
      val (l, t2) = t1.pop()
      val (topics, rest) = popTopics(t2, n)
      val extra = 8 * l.value + (if (l.value == 0) BigInt(0) else memExpandCost(st, o.value + l.value))
      if (st.outOfGas(extra)) st.fail
      else {
        val data = Bytes.readList(st.memory.data, o.value, l.value)
        val mem = if (l.value == 0) st.memory else st.memory.expand(o.value + l.value)
        st.chargeGas(extra).copy(stack = rest, memory = mem,
          logs = st.logs :+ Log(st.msg.self, topics, data)).advancePc(1)
      }
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 2 + n
          && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.drop(2 + n)
          && r.logs == st.logs :+ Log(st.msg.self, st.stack.data.tail.tail.take(n),
               Bytes.readList(st.memory.data, st.stack.data.head.value, st.stack.data.tail.head.value)))))

  // KECCAK256: hash memory[offset:offset+len] and push the digest. Gas 30 (base) +
  // 6 per word + memory expansion. Keccak256.hash is a trusted primitive.
  def keccak256Op(st: ExecState): ExecState = {
    if (st.stack.data.size < 2) st.fail
    else {
      val (o, t1) = st.stack.pop()
      val (l, t2) = t1.pop()
      val extra = 6 * Gas.words(l.value) + (if (l.value == 0) BigInt(0) else memExpandCost(st, o.value + l.value))
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(
        stack = t2.push(Keccak256.hash(Bytes.readList(st.memory.data, o.value, l.value))),
        memory = if (l.value == 0) st.memory else st.memory.expand(o.value + l.value)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 2 && r.pc == st.pc + 1
          && r.stack.data.head == Keccak256.hash(Bytes.readList(st.memory.data, st.stack.data.head.value, st.stack.data.tail.head.value))
          && r.stack.data.tail == st.stack.data.tail.tail)))

  // EXTCODEHASH: the keccak of an account's code, or zero for an account that does
  // not exist. Cold/warm priced like the other account reads.
  def extcodehashOp(st: ExecState): ExecState = {
    if (st.stack.data.isEmpty) st.fail
    else {
      val (a, t) = st.stack.pop()
      val addr = Address.fromWord(a)
      val extra = if (st.accessedAccounts.contains(addr)) BigInt(0) else BigInt(2500)
      if (st.outOfGas(extra)) st.fail
      else {
        val h = if (st.world.accounts.contains(addr)) Keccak256.hash(st.world.codeOf(addr).code) else Word256.Zero
        st.chargeGas(extra).copy(stack = t.push(h),
          accessedAccounts = st.accessedAccounts ++ Set(addr)).advancePc(1)
      }
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.nonEmpty && r.pc == st.pc + 1
          && r.stack.data.head == (if (st.world.accounts.contains(Address.fromWord(st.stack.data.head)))
               Keccak256.hash(st.world.codeOf(Address.fromWord(st.stack.data.head)).code) else Word256.Zero)
          && r.stack.data.tail == st.stack.data.tail
          && r.accessedAccounts.contains(Address.fromWord(st.stack.data.head)))))

  // EXTCODECOPY: copy another account's code into memory (zero-padded past its
  // end), charging the account cold/warm surcharge plus the per-word copy cost.
  def extcodecopyOp(st: ExecState): ExecState = {
    if (st.stack.data.size < 4) st.fail
    else {
      val (a, t1) = st.stack.pop()
      val (d, t2) = t1.pop()
      val (o, t3) = t2.pop()
      val (l, t4) = t3.pop()
      val addr = Address.fromWord(a)
      val extra = (if (st.accessedAccounts.contains(addr)) BigInt(0) else BigInt(2500)) +
        (if (l.value == 0) BigInt(0) else 3 * Gas.words(l.value) + memExpandCost(st, d.value + l.value))
      if (st.outOfGas(extra)) st.fail
      else st.chargeGas(extra).copy(stack = t4,
        memory = st.memory.copyIn(d.value, st.world.codeOf(addr).code, o.value, l.value),
        accessedAccounts = st.accessedAccounts ++ Set(addr)).advancePc(1)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 4 && r.pc == st.pc + 1
          && r.stack.data == st.stack.data.tail.tail.tail.tail
          && r.memory == st.memory.copyIn(st.stack.data.tail.head.value,
               st.world.codeOf(Address.fromWord(st.stack.data.head)).code,
               st.stack.data.tail.tail.head.value, st.stack.data.tail.tail.tail.head.value)
          && r.accessedAccounts.contains(Address.fromWord(st.stack.data.head)))))

  // EXP: base ** exponent, charging 50 gas per byte of the exponent on top of the
  // static base; the result comes from the verified binop.
  def expOp(st: ExecState): ExecState = {
    if (st.stack.data.size < 2) st.fail
    else {
      val extra = 50 * EvmMath.byteLength(st.stack.data.tail.head.value)
      if (st.outOfGas(extra)) st.fail
      else binop(st.chargeGas(extra), (a, b) => a ** b)
    }
  }.ensuring(r =>
    (!r.isRunning || r.gas <= st.gas)
    && (r.isRunning ==>
         (st.stack.data.size >= 2 && r.pc == st.pc + 1
          && r.stack.data.head == (st.stack.data.head ** st.stack.data.tail.head)
          && r.stack.data.tail == st.stack.data.tail.tail)))

  // SELFDESTRUCT: transfer the whole balance of the executing account to the
  // beneficiary and halt. Post-EIP-6780 the account's code/storage are deleted only
  // if it was created in the same transaction (tracked in `created`); otherwise the
  // account survives and only the balance moves.
  def selfdestructOp(st: ExecState): ExecState = {
    if (st.static || st.stack.data.isEmpty) st.fail
    else {
      val beneficiary = Address.fromWord(st.stack.data.head)
      val bal = st.world.balanceOf(st.msg.self)
      val extra = (if (st.accessedAccounts.contains(beneficiary)) BigInt(0) else BigInt(2600)) +
        (if (bal.value > 0 && !st.world.accounts.contains(beneficiary)) BigInt(25000) else BigInt(0))
      if (st.outOfGas(extra)) st.fail
      else {
        val moved = st.world.transfer(st.msg.self, beneficiary, bal)
        val newWorld = if (st.created.contains(st.msg.self)) moved.destroy(st.msg.self) else moved
        st.copy(
          gas = st.gas - extra,
          world = newWorld,
          accessedAccounts = st.accessedAccounts ++ Set(beneficiary),
          status = Status.Halted)
      }
    }
  }.ensuring(r =>
    !r.isRunning && r.gas <= st.gas
    && (r.status == Status.Halted ==>
         (st.stack.data.nonEmpty
          && r.accessedAccounts.contains(Address.fromWord(st.stack.data.head))
          && r.world == (if (st.created.contains(st.msg.self))
               st.world.transfer(st.msg.self, Address.fromWord(st.stack.data.head), st.world.balanceOf(st.msg.self)).destroy(st.msg.self)
             else st.world.transfer(st.msg.self, Address.fromWord(st.stack.data.head), st.world.balanceOf(st.msg.self))))))

  // Dispatch a single already-base-charged opcode to its helper. Called by step
  // with base gas removed; the call opcodes are not handled here but in run (they
  // need to spawn a child frame). An unrecognized opcode falls through to fail.
  def execute(s1: ExecState, op: Opcode): ExecState = {
    op match
      case Opcode.STOP => s1.halt
      case Opcode.JUMPDEST => s1.advancePc(1)
      case Opcode.POP => popOp(s1)

      case Opcode.ADD => binop(s1, (a, b) => a + b)
      case Opcode.SUB => binop(s1, (a, b) => a - b)
      case Opcode.MUL => binop(s1, (a, b) => a * b)
      case Opcode.DIV => binop(s1, (a, b) => a / b)
      case Opcode.SDIV => binop(s1, (a, b) => a.sdiv(b))
      case Opcode.MOD => binop(s1, (a, b) => a % b)
      case Opcode.SMOD => binop(s1, (a, b) => a.smod(b))
      case Opcode.KECCAK256 => keccak256Op(s1)
      case Opcode.EXP => expOp(s1)
      case Opcode.SIGNEXTEND => binop(s1, (a, b) => b.signextend(a))

      case Opcode.LT => binop(s1, (a, b) => if (a.lt(b)) Word256.One else Word256.Zero)
      case Opcode.GT => binop(s1, (a, b) => if (a.gt(b)) Word256.One else Word256.Zero)
      case Opcode.SLT => binop(s1, (a, b) => if (a.slt(b)) Word256.One else Word256.Zero)
      case Opcode.SGT => binop(s1, (a, b) => if (a.sgt(b)) Word256.One else Word256.Zero)
      case Opcode.EQ => binop(s1, (a, b) => if (a == b) Word256.One else Word256.Zero)
      case Opcode.ISZERO => unop(s1, a => if (a.isZero) Word256.One else Word256.Zero)

      case Opcode.AND => binop(s1, (a, b) => a & b)
      case Opcode.OR => binop(s1, (a, b) => a | b)
      case Opcode.XOR => binop(s1, (a, b) => a ^ b)
      case Opcode.NOT => unop(s1, a => ~a)
      case Opcode.BYTE => binop(s1, (a, b) => b.byte(a))
      case Opcode.SHL => binop(s1, (a, b) => b.shl(a))
      case Opcode.SHR => binop(s1, (a, b) => b.shr(a))
      case Opcode.SAR => binop(s1, (a, b) => b.sar(a))
      case Opcode.CLZ => unop(s1, a => a.clz)

      case Opcode.ADDMOD => terop(s1, (a, b, n) => Word256.addmod(a, b, n))
      case Opcode.MULMOD => terop(s1, (a, b, n) => Word256.mulmod(a, b, n))

      case Opcode.PUSH0 => pushN(s1, 0)
      case Opcode.PUSH1 => pushN(s1, 1)
      case Opcode.PUSH2 => pushN(s1, 2)
      case Opcode.PUSH3 => pushN(s1, 3)
      case Opcode.PUSH4 => pushN(s1, 4)
      case Opcode.PUSH5 => pushN(s1, 5)
      case Opcode.PUSH6 => pushN(s1, 6)
      case Opcode.PUSH7 => pushN(s1, 7)
      case Opcode.PUSH8 => pushN(s1, 8)
      case Opcode.PUSH9 => pushN(s1, 9)
      case Opcode.PUSH10 => pushN(s1, 10)
      case Opcode.PUSH11 => pushN(s1, 11)
      case Opcode.PUSH12 => pushN(s1, 12)
      case Opcode.PUSH13 => pushN(s1, 13)
      case Opcode.PUSH14 => pushN(s1, 14)
      case Opcode.PUSH15 => pushN(s1, 15)
      case Opcode.PUSH16 => pushN(s1, 16)
      case Opcode.PUSH17 => pushN(s1, 17)
      case Opcode.PUSH18 => pushN(s1, 18)
      case Opcode.PUSH19 => pushN(s1, 19)
      case Opcode.PUSH20 => pushN(s1, 20)
      case Opcode.PUSH21 => pushN(s1, 21)
      case Opcode.PUSH22 => pushN(s1, 22)
      case Opcode.PUSH23 => pushN(s1, 23)
      case Opcode.PUSH24 => pushN(s1, 24)
      case Opcode.PUSH25 => pushN(s1, 25)
      case Opcode.PUSH26 => pushN(s1, 26)
      case Opcode.PUSH27 => pushN(s1, 27)
      case Opcode.PUSH28 => pushN(s1, 28)
      case Opcode.PUSH29 => pushN(s1, 29)
      case Opcode.PUSH30 => pushN(s1, 30)
      case Opcode.PUSH31 => pushN(s1, 31)
      case Opcode.PUSH32 => pushN(s1, 32)

      case Opcode.DUP1 => dupN(s1, 1)
      case Opcode.DUP2 => dupN(s1, 2)
      case Opcode.DUP3 => dupN(s1, 3)
      case Opcode.DUP4 => dupN(s1, 4)
      case Opcode.DUP5 => dupN(s1, 5)
      case Opcode.DUP6 => dupN(s1, 6)
      case Opcode.DUP7 => dupN(s1, 7)
      case Opcode.DUP8 => dupN(s1, 8)
      case Opcode.DUP9 => dupN(s1, 9)
      case Opcode.DUP10 => dupN(s1, 10)
      case Opcode.DUP11 => dupN(s1, 11)
      case Opcode.DUP12 => dupN(s1, 12)
      case Opcode.DUP13 => dupN(s1, 13)
      case Opcode.DUP14 => dupN(s1, 14)
      case Opcode.DUP15 => dupN(s1, 15)
      case Opcode.DUP16 => dupN(s1, 16)

      case Opcode.SWAP1 => swapN(s1, 1)
      case Opcode.SWAP2 => swapN(s1, 2)
      case Opcode.SWAP3 => swapN(s1, 3)
      case Opcode.SWAP4 => swapN(s1, 4)
      case Opcode.SWAP5 => swapN(s1, 5)
      case Opcode.SWAP6 => swapN(s1, 6)
      case Opcode.SWAP7 => swapN(s1, 7)
      case Opcode.SWAP8 => swapN(s1, 8)
      case Opcode.SWAP9 => swapN(s1, 9)
      case Opcode.SWAP10 => swapN(s1, 10)
      case Opcode.SWAP11 => swapN(s1, 11)
      case Opcode.SWAP12 => swapN(s1, 12)
      case Opcode.SWAP13 => swapN(s1, 13)
      case Opcode.SWAP14 => swapN(s1, 14)
      case Opcode.SWAP15 => swapN(s1, 15)
      case Opcode.SWAP16 => swapN(s1, 16)

      case Opcode.MSIZE =>
        if (s1.memory.size > MAX_VALUE) s1.fail
        else pushConst(s1, Word256(s1.memory.size))
      case Opcode.MLOAD => mload(s1)
      case Opcode.MSTORE => mstore(s1)
      case Opcode.MSTORE8 => mstore8(s1)
      case Opcode.MCOPY => mcopyOp(s1)

      case Opcode.ADDRESS => pushConst(s1, s1.msg.self.toWord)
      case Opcode.ORIGIN => pushConst(s1, s1.tx.origin.toWord)
      case Opcode.CALLER => pushConst(s1, s1.msg.caller.toWord)
      case Opcode.CALLVALUE => pushConst(s1, s1.msg.callValue)
      case Opcode.GASPRICE => pushConst(s1, s1.tx.gasPrice)
      case Opcode.COINBASE => pushConst(s1, s1.block.coinbase.toWord)
      case Opcode.TIMESTAMP => pushConst(s1, s1.block.timestamp)
      case Opcode.NUMBER => pushConst(s1, s1.block.number)
      case Opcode.PREVRANDAO => pushConst(s1, s1.block.prevrandao)
      case Opcode.GASLIMIT => pushConst(s1, s1.block.gasLimit)
      case Opcode.CHAINID => pushConst(s1, s1.block.chainId)
      case Opcode.SELFBALANCE => pushConst(s1, s1.world.balanceOf(s1.msg.self))
      case Opcode.BASEFEE => pushConst(s1, s1.block.baseFee)
      case Opcode.BLOBBASEFEE => pushConst(s1, s1.block.blobBaseFee)

      case Opcode.CALLDATASIZE =>
        if (s1.msg.callData.size > MAX_VALUE) s1.fail
        else pushConst(s1, Word256(s1.msg.callData.size))
      case Opcode.CODESIZE =>
        if (s1.code.size > MAX_VALUE) s1.fail
        else pushConst(s1, Word256(s1.code.size))
      case Opcode.PC =>
        if (s1.pc > MAX_VALUE) s1.fail
        else pushConst(s1, Word256(s1.pc))
      case Opcode.GAS =>
        if (s1.gas > MAX_VALUE) s1.fail
        else pushConst(s1, Word256(s1.gas))

      case Opcode.BLOCKHASH => unop(s1, num => s1.block.blockHash(num))
      case Opcode.BLOBHASH => unop(s1, idx => s1.tx.blobHash(idx))
      case Opcode.BALANCE => balanceOp(s1)
      case Opcode.EXTCODESIZE => extcodesizeOp(s1)
      case Opcode.EXTCODEHASH => extcodehashOp(s1)
      case Opcode.EXTCODECOPY => extcodecopyOp(s1)
      case Opcode.TLOAD => tload(s1)
      case Opcode.TSTORE => tstore(s1)
      case Opcode.SLOAD => sload(s1)
      case Opcode.SSTORE => sstore(s1)

      case Opcode.JUMP => jump(s1)
      case Opcode.JUMPI => jumpi(s1)
      case Opcode.RETURN => returnOp(s1)
      case Opcode.REVERT => revertOp(s1)

      case Opcode.CALLDATALOAD => calldataload(s1)
      case Opcode.CALLDATACOPY => calldatacopy(s1)
      case Opcode.CODECOPY => codecopy(s1)
      case Opcode.RETURNDATACOPY => returndatacopy(s1)
      case Opcode.RETURNDATASIZE =>
        if (s1.returnData.size > MAX_VALUE) s1.fail
        else pushConst(s1, Word256(s1.returnData.size))

      case Opcode.SELFDESTRUCT => selfdestructOp(s1)

      case Opcode.LOG0 => logN(s1, 0)
      case Opcode.LOG1 => logN(s1, 1)
      case Opcode.LOG2 => logN(s1, 2)
      case Opcode.LOG3 => logN(s1, 3)
      case Opcode.LOG4 => logN(s1, 4)

      case _ => s1.fail
  }.ensuring(r => !r.isRunning || (r.gas <= s1.gas && Opcode.baseGas(op) >= 1))

  // One machine step: halt at end of code, fail on an undefined byte or when the
  // base gas is unaffordable, otherwise charge base gas and execute. The `r.gas <
  // s.gas` postcondition (base gas is always >= 1 for real opcodes) is what makes
  // the gas measure strictly decrease, so run terminates even across backward jumps.
  def step(s: ExecState): ExecState = {

    if (!s.isRunning) s
    else if (s.pc >= s.code.size) s.halt
    else

      s.code.opcodeAt(s.pc) match
        case None() => s.fail
        case Some(op) =>

          val cost = Opcode.baseGas(op)
          if (s.outOfGas(cost)) s.fail
          else execute(s.chargeGas(cost), op)
  }.ensuring(r => !r.isRunning || r.gas < s.gas)

  // Pop the 6 STATICCALL args, charge the base cost, and either reject the call
  // (continue the parent) or build the child frame and the gas-forwarded parent.
  def prepareStaticCall(s: ExecState): CallPrep = {
    require(s.isRunning)
    if (s.stack.data.size < 6) CallReject(s.fail)
    else {
      val (gasReq, a1) = s.stack.pop()
      val (addr, a2) = a1.pop()
      val (argsOff, a3) = a2.pop()
      val (argsLen, a4) = a3.pop()
      val (retOff, a5) = a4.pop()
      val (retLen, rest) = a5.pop()
      val callee = Address.fromWord(addr)
      val cost = BigInt(100) + (if (s.accessedAccounts.contains(callee)) BigInt(0) else BigInt(2500))
      if (s.outOfGas(cost)) CallReject(s.fail)
      else {
        // single copy to keep the VC term small (the fallback solver hangs on
        // chargeGas(...).copy(...) here)
        val s1 = s.copy(gas = s.gas - cost, accessedAccounts = s.accessedAccounts ++ Set(callee))
        if (s1.depth >= ExecState.MAX_DEPTH) {
          if (rest.data.size >= Stack.MAXIMUM_STACK_SIZE) CallReject(s1.fail)
          else CallReject(s1.copy(stack = rest.push(Word256.Zero)).advancePc(1))
        } else {
          val avail = s1.gas - s1.gas / 64
          val g = if (gasReq.value < avail) gasReq.value else avail
          val callData = Bytes.readList(s.memory.data, argsOff.value, argsLen.value)
          val calleeStorage = s1.world.storageOf(callee)
          val child = ExecState.subFrame(s1.world.codeOf(callee), callee, s1.msg.self, Word256.Zero,
            callData, g, s1.depth + 1, true, s1.block, s1.tx, s1.world, calleeStorage, calleeStorage,
            s1.accessedAccounts, s1.created)
          retOff.bounded
          retLen.bounded
          CallEnter(child, s1.copy(gas = s1.gas - g), rest, g, false, false, callee, s.world, retOff.value, retLen.value)
        }
      }
    }
  }.ensuring(r => r match
    case CallReject(sr) => !sr.isRunning || sr.gas < s.gas
    case ce: CallEnter => ce.forwarded >= 0 && ce.parentForwarded.gas >= 0 && ce.child.gas < s.gas && ce.parentForwarded.gas + ce.forwarded < s.gas)

  // DELEGATECALL: run the target's code but in the caller's own context (self,
  // sender, value, and storage are all the parent's), so state changes commit.
  def prepareDelegateCall(s: ExecState): CallPrep = {
    require(s.isRunning)
    if (s.stack.data.size < 6) CallReject(s.fail)
    else {
      val (gasReq, a1) = s.stack.pop()
      val (addr, a2) = a1.pop()
      val (argsOff, a3) = a2.pop()
      val (argsLen, a4) = a3.pop()
      val (retOff, a5) = a4.pop()
      val (retLen, rest) = a5.pop()
      val target = Address.fromWord(addr)
      val cost = BigInt(100) + (if (s.accessedAccounts.contains(target)) BigInt(0) else BigInt(2500))
      if (s.outOfGas(cost)) CallReject(s.fail)
      else {
        val s1 = s.copy(gas = s.gas - cost, accessedAccounts = s.accessedAccounts ++ Set(target))
        if (s1.depth >= ExecState.MAX_DEPTH) {
          if (rest.data.size >= Stack.MAXIMUM_STACK_SIZE) CallReject(s1.fail)
          else CallReject(s1.copy(stack = rest.push(Word256.Zero)).advancePc(1))
        } else {
          val avail = s1.gas - s1.gas / 64
          val g = if (gasReq.value < avail) gasReq.value else avail
          val callData = Bytes.readList(s.memory.data, argsOff.value, argsLen.value)
          val child = ExecState.subFrame(s1.world.codeOf(target), s1.msg.self, s1.msg.caller,
            s1.msg.callValue, callData, g, s1.depth + 1, s1.static, s1.block, s1.tx, s1.world,
            s1.storage, s1.original, s1.accessedAccounts, s1.created)
          retOff.bounded
          retLen.bounded
          CallEnter(child, s1.copy(gas = s1.gas - g), rest, g, true, true, s1.msg.self, s.world, retOff.value, retLen.value)
        }
      }
    }
  }.ensuring(r => r match
    case CallReject(sr) => !sr.isRunning || sr.gas < s.gas
    case ce: CallEnter => ce.forwarded >= 0 && ce.parentForwarded.gas >= 0 && ce.child.gas < s.gas && ce.parentForwarded.gas + ce.forwarded < s.gas)

  // CALL: run the callee's code in the callee's own account, transferring value
  // from the current account to the callee. State (incl. the balance move) commits
  // on success and rolls back on failure. 7 args (value is the extra one).
  def prepareCall(s: ExecState): CallPrep = {
    require(s.isRunning)
    if (s.stack.data.size < 7) CallReject(s.fail)
    else {
      val (gasReq, a1) = s.stack.pop()
      val (addr, a2) = a1.pop()
      val (value, a3) = a2.pop()
      val (argsOff, a4) = a3.pop()
      val (argsLen, a5) = a4.pop()
      val (retOff, a6) = a5.pop()
      val (retLen, rest) = a6.pop()
      val callee = Address.fromWord(addr)
      val hasValue = value.value > 0
      val newAcct = hasValue && !s.world.accounts.contains(callee)
      val cost = BigInt(100) + (if (s.accessedAccounts.contains(callee)) BigInt(0) else BigInt(2500)) +
        (if (hasValue) BigInt(9000) else BigInt(0)) + (if (newAcct) BigInt(25000) else BigInt(0))
      if ((s.static && hasValue) || s.outOfGas(cost)) CallReject(s.fail)
      else {
        val s1 = s.copy(gas = s.gas - cost, accessedAccounts = s.accessedAccounts ++ Set(callee))
        if (s1.depth >= ExecState.MAX_DEPTH || s.world.balanceOf(s.msg.self).value < value.value) {
          if (rest.data.size >= Stack.MAXIMUM_STACK_SIZE) CallReject(s1.fail)
          else CallReject(s1.copy(stack = rest.push(Word256.Zero)).advancePc(1))
        } else {
          val avail = s1.gas - s1.gas / 64
          val baseFwd = if (gasReq.value < avail) gasReq.value else avail
          val g = baseFwd + (if (hasValue) BigInt(2300) else BigInt(0))
          val callData = Bytes.readList(s.memory.data, argsOff.value, argsLen.value)
          val transferred = s1.world.transfer(s1.msg.self, callee, value)
          val child = ExecState.subFrame(transferred.codeOf(callee), callee, s1.msg.self, value,
            callData, g, s1.depth + 1, s1.static, s1.block, s1.tx, transferred,
            transferred.storageOf(callee), transferred.storageOf(callee), s1.accessedAccounts, s1.created)
          retOff.bounded
          retLen.bounded
          CallEnter(child, s1.copy(gas = s1.gas - baseFwd), rest, g, true, false, callee, s.world, retOff.value, retLen.value)
        }
      }
    }
  }.ensuring(r => r match
    case CallReject(sr) => !sr.isRunning || sr.gas < s.gas
    case ce: CallEnter => ce.forwarded >= 0 && ce.parentForwarded.gas >= 0 && ce.child.gas < s.gas && ce.parentForwarded.gas + ce.forwarded < s.gas)

  // CALLCODE: like CALL (has value, 7 args) but runs the target's code in the
  // caller's own account (storage/self preserved, so state commits like
  // DELEGATECALL); the value is sent to self, so no net balance change.
  def prepareCallcode(s: ExecState): CallPrep = {
    require(s.isRunning)
    if (s.stack.data.size < 7) CallReject(s.fail)
    else {
      val (gasReq, a1) = s.stack.pop()
      val (addr, a2) = a1.pop()
      val (value, a3) = a2.pop()
      val (argsOff, a4) = a3.pop()
      val (argsLen, a5) = a4.pop()
      val (retOff, a6) = a5.pop()
      val (retLen, rest) = a6.pop()
      val target = Address.fromWord(addr)
      val hasValue = value.value > 0
      val cost = BigInt(100) + (if (s.accessedAccounts.contains(target)) BigInt(0) else BigInt(2500)) +
        (if (hasValue) BigInt(9000) else BigInt(0))
      if ((s.static && hasValue) || s.outOfGas(cost)) CallReject(s.fail)
      else {
        val s1 = s.copy(gas = s.gas - cost, accessedAccounts = s.accessedAccounts ++ Set(target))
        if (s1.depth >= ExecState.MAX_DEPTH || s.world.balanceOf(s.msg.self).value < value.value) {
          if (rest.data.size >= Stack.MAXIMUM_STACK_SIZE) CallReject(s1.fail)
          else CallReject(s1.copy(stack = rest.push(Word256.Zero)).advancePc(1))
        } else {
          val avail = s1.gas - s1.gas / 64
          val baseFwd = if (gasReq.value < avail) gasReq.value else avail
          val g = baseFwd + (if (hasValue) BigInt(2300) else BigInt(0))
          val callData = Bytes.readList(s.memory.data, argsOff.value, argsLen.value)
          val child = ExecState.subFrame(s1.world.codeOf(target), s1.msg.self, s1.msg.self, value,
            callData, g, s1.depth + 1, s1.static, s1.block, s1.tx, s1.world, s1.storage, s1.original,
            s1.accessedAccounts, s1.created)
          retOff.bounded
          retLen.bounded
          CallEnter(child, s1.copy(gas = s1.gas - baseFwd), rest, g, true, true, s1.msg.self, s.world, retOff.value, retLen.value)
        }
      }
    }
  }.ensuring(r => r match
    case CallReject(sr) => !sr.isRunning || sr.gas < s.gas
    case ce: CallEnter => ce.forwarded >= 0 && ce.parentForwarded.gas >= 0 && ce.child.gas < s.gas && ce.parentForwarded.gas + ce.forwarded < s.gas)

  // Merge a finished child frame into the parent: push success (1/0), refund the
  // child's unused gas (capped at what was forwarded), expose its return data, and
  // (if commitState and success) commit its world/storage/slots/logs/refund; a
  // failed/reverted child rolls the world back to preWorld.
  def mergeCall(enter: CallEnter, childRes: ExecState): ExecState = {
    require(enter.parentForwarded.gas >= 0 && enter.forwarded >= 0)
    val success = childRes.status == Status.Halted
    val commit = success && enter.commitState
    val refund = if (childRes.gas < enter.forwarded) childRes.gas else enter.forwarded
    // The child's return data is written into the caller's memory at retOff, up to
    // retLen bytes (min with the actual data length). A failed child has no data.
    val writeLen = if (enter.retLen < childRes.returnData.size) enter.retLen else childRes.returnData.size
    if (enter.rest.data.size >= Stack.MAXIMUM_STACK_SIZE) enter.parentForwarded.fail
    else enter.parentForwarded.copy(
      gas = enter.parentForwarded.gas + refund,
      stack = enter.rest.push(if (success) Word256.One else Word256.Zero),
      memory = enter.parentForwarded.memory.copyIn(enter.retOff, childRes.returnData, 0, writeLen),
      returnData = childRes.returnData,
      world = if (commit) childRes.world.withStorage(enter.self, childRes.storage) else enter.preWorld,
      storage = if (commit && enter.sameAccount) childRes.storage else enter.parentForwarded.storage,
      accessedSlots = if (commit && enter.sameAccount) childRes.accessedSlots else enter.parentForwarded.accessedSlots,
      logs = if (commit) childRes.logs else enter.parentForwarded.logs,
      refund = if (commit) enter.parentForwarded.refund + childRes.refund else enter.parentForwarded.refund,
      created = childRes.created
    ).advancePc(1)
  }.ensuring(r => r.gas <= enter.parentForwarded.gas + enter.forwarded)

  // CREATE / CREATE2: charge 32000 + 2/word initcode (plus 6/word for the CREATE2
  // keccak) + memory, increment the creator nonce, derive the new address, and
  // either reject (static, out of gas, depth/balance limit, or an address collision
  // -> push 0) or build the initcode frame with 63/64 of the gas forwarded and the
  // value transferred. The nonce bump lives in preWorld so it survives a failure.
  def prepareCreate(s: ExecState, isCreate2: Boolean): CreatePrep = {
    require(s.isRunning)
    val need = if (isCreate2) BigInt(4) else BigInt(3)
    if (s.static || s.stack.data.size < need) CreateReject(s.fail)
    else {
      val (value, a1) = s.stack.pop()
      val (off, a2) = a1.pop()
      val (len, a3) = a2.pop()
      val (salt, rest) = if (isCreate2) a3.pop() else (Word256.Zero, a3)
      val initcode = Bytes.readList(s.memory.data, off.value, len.value)
      val w = Gas.words(len.value)
      val memCost = if (len.value == 0) BigInt(0) else memExpandCost(s, off.value + len.value)
      val cost = BigInt(32000) + 2 * w + memCost + (if (isCreate2) 6 * w else BigInt(0))
      if (len.value > 49152 || s.outOfGas(cost)) CreateReject(s.fail)
      else {
        val nonce = s.world.nonceOf(s.msg.self)
        val newAddr = if (isCreate2) CreateAddress.create2(s.msg.self, salt, Keccak256.hash(initcode))
                      else CreateAddress.create(s.msg.self, nonce)
        val bumped = s.world.withNonce(s.msg.self, nonce + 1)
        val s1 = s.copy(gas = s.gas - cost, world = bumped,
          memory = if (len.value == 0) s.memory else s.memory.expand(off.value + len.value),
          accessedAccounts = s.accessedAccounts ++ Set(newAddr))
        val collision = s.world.accounts.contains(newAddr) &&
          (s.world.nonceOf(newAddr) != 0 || s.world.codeOf(newAddr).size > 0)
        if (s1.depth >= ExecState.MAX_DEPTH || s.world.balanceOf(s.msg.self).value < value.value || collision) {
          if (rest.data.size >= Stack.MAXIMUM_STACK_SIZE) CreateReject(s1.fail)
          else CreateReject(s1.copy(stack = rest.push(Word256.Zero)).advancePc(1))
        } else {
          val forwarded = s1.gas - s1.gas / 64
          val transferred = bumped.transfer(s.msg.self, newAddr, value)
          val child = ExecState.subFrame(Code(initcode), newAddr, s.msg.self, value, Nil[BigInt](),
            forwarded, s1.depth + 1, s1.static, s1.block, s1.tx, transferred,
            transferred.storageOf(newAddr), transferred.storageOf(newAddr), s1.accessedAccounts, s1.created ++ Set(newAddr))
          CreateEnter(child, s1.copy(gas = s1.gas - forwarded), rest, forwarded, newAddr, bumped)
        }
      }
    }
  }.ensuring(r => r match
    case CreateReject(sr) => !sr.isRunning || sr.gas < s.gas
    case ce: CreateEnter => ce.forwarded >= 0 && ce.parentForwarded.gas >= 0 && ce.child.gas < s.gas && ce.parentForwarded.gas + ce.forwarded < s.gas)

  // Merge a finished initcode frame. On success the returned bytes become the new
  // contract's code (charged 200/byte from the child's leftover gas, capped at
  // 24576 by EIP-170), the new address is pushed, and the account (storage + code +
  // transferred value) is committed. Otherwise (failure, reverted, code too big, or
  // deployment gas short) push 0 and roll back to preWorld, undoing the transfer.
  def mergeCreate(enter: CreateEnter, childRes: ExecState): ExecState = {
    require(enter.parentForwarded.gas >= 0 && enter.forwarded >= 0)
    val success = childRes.status == Status.Halted
    val code = childRes.returnData
    val depCost = 200 * code.size
    val refund = if (childRes.gas < enter.forwarded) childRes.gas else enter.forwarded
    val deployOk = success && code.size <= 24576 && depCost <= refund
    if (enter.rest.data.size >= Stack.MAXIMUM_STACK_SIZE) enter.parentForwarded.fail
    else if (deployOk)
      enter.parentForwarded.copy(
        gas = enter.parentForwarded.gas + (refund - depCost),
        stack = enter.rest.push(enter.newAddr.toWord),
        returnData = Nil[BigInt](),
        world = childRes.world.withStorage(enter.newAddr, childRes.storage).withCode(enter.newAddr, Code(code)),
        logs = childRes.logs,
        refund = enter.parentForwarded.refund + childRes.refund,
        accessedAccounts = childRes.accessedAccounts,
        accessedSlots = childRes.accessedSlots,
        created = childRes.created).advancePc(1)
    else
      enter.parentForwarded.copy(
        gas = enter.parentForwarded.gas + refund,
        stack = enter.rest.push(Word256.Zero),
        returnData = if (childRes.status == Status.Reverted) childRes.returnData else Nil[BigInt](),
        world = enter.preWorld,
        accessedAccounts = childRes.accessedAccounts,
        created = childRes.created).advancePc(1)
  }.ensuring(r => r.gas <= enter.parentForwarded.gas + enter.forwarded)

  // Drive the frame to a stopped state. The call opcodes are intercepted here (not
  // in execute) so run stays self-recursive with a single `decreases(s.gas)`
  // measure: the child runs on strictly less gas (63/64 rule), and the merged
  // parent's gas is bounded by parentForwarded + forwarded, which mergeCall proves
  // is also below s.gas. Every other opcode goes through step.
  def run(s: ExecState): ExecState = {
    decreases(s.gas)
    if (!s.isRunning) s
    else if (s.pc < s.code.size && s.code.opcodeAt(s.pc) == Some(Opcode.STATICCALL)) {
      prepareStaticCall(s) match
        case CallReject(sr) => if (!sr.isRunning) sr else run(sr)
        case ce: CallEnter =>
          val parent2 = mergeCall(ce, run(ce.child))
          if (!parent2.isRunning) parent2 else run(parent2)
    } else if (s.pc < s.code.size && s.code.opcodeAt(s.pc) == Some(Opcode.DELEGATECALL)) {
      prepareDelegateCall(s) match
        case CallReject(sr) => if (!sr.isRunning) sr else run(sr)
        case ce: CallEnter =>
          val parent2 = mergeCall(ce, run(ce.child))
          if (!parent2.isRunning) parent2 else run(parent2)
    } else if (s.pc < s.code.size && s.code.opcodeAt(s.pc) == Some(Opcode.CALL)) {
      prepareCall(s) match
        case CallReject(sr) => if (!sr.isRunning) sr else run(sr)
        case ce: CallEnter =>
          val parent2 = mergeCall(ce, run(ce.child))
          if (!parent2.isRunning) parent2 else run(parent2)
    } else if (s.pc < s.code.size && s.code.opcodeAt(s.pc) == Some(Opcode.CALLCODE)) {
      prepareCallcode(s) match
        case CallReject(sr) => if (!sr.isRunning) sr else run(sr)
        case ce: CallEnter =>
          val parent2 = mergeCall(ce, run(ce.child))
          if (!parent2.isRunning) parent2 else run(parent2)
    } else if (s.pc < s.code.size && s.code.opcodeAt(s.pc) == Some(Opcode.CREATE)) {
      prepareCreate(s, false) match
        case CreateReject(sr) => if (!sr.isRunning) sr else run(sr)
        case ce: CreateEnter =>
          val parent2 = mergeCreate(ce, run(ce.child))
          if (!parent2.isRunning) parent2 else run(parent2)
    } else if (s.pc < s.code.size && s.code.opcodeAt(s.pc) == Some(Opcode.CREATE2)) {
      prepareCreate(s, true) match
        case CreateReject(sr) => if (!sr.isRunning) sr else run(sr)
        case ce: CreateEnter =>
          val parent2 = mergeCreate(ce, run(ce.child))
          if (!parent2.isRunning) parent2 else run(parent2)
    } else {
      val s1 = step(s)
      if (!s1.isRunning) s1 else run(s1)
    }
  }.ensuring(r => !r.isRunning)
