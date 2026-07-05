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
import evm.env.Address
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
// the world to restore if the child fails/reverts (rolls back value transfer too).
case class CallEnter(child: ExecState, parentForwarded: ExecState, rest: Stack, forwarded: BigInt,
                     commitState: Boolean, sameAccount: Boolean, self: Address, preWorld: WorldState) extends CallPrep

object Interpreter:

  def memExpandCost(st: ExecState, end: BigInt): BigInt = {
    require(end >= 0)
    Gas.memoryExpansionCost(st.memory.size / 32, st.memory.expandedTo(end) / 32)
  }.ensuring(r => r >= 0)

  def pushConst(st: ExecState, v: Word256): ExecState = {
    if (st.stack.data.size >= Stack.MAXIMUM_STACK_SIZE) st.fail
    else st.copy(stack = st.stack.push(v)).advancePc(1)
  }.ensuring(r =>
    (!r.isRunning || r.gas == st.gas)
    && ((st.isRunning && st.stack.data.size < Stack.MAXIMUM_STACK_SIZE) ==>
         (r.isRunning && r.gas == st.gas && r.pc == st.pc + 1
          && r.stack.data.head == v
          && r.stack.data.tail == st.stack.data)))

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
  // beneficiary and halt. Post-EIP-6780 it does not delete code/storage unless the
  // account was created in the same transaction (unreachable until CREATE exists).
  def selfdestructOp(st: ExecState): ExecState = {
    if (st.static || st.stack.data.isEmpty) st.fail
    else {
      val beneficiary = Address.fromWord(st.stack.data.head)
      val bal = st.world.balanceOf(st.msg.self)
      val extra = (if (st.accessedAccounts.contains(beneficiary)) BigInt(0) else BigInt(2600)) +
        (if (bal.value > 0 && !st.world.accounts.contains(beneficiary)) BigInt(25000) else BigInt(0))
      if (st.outOfGas(extra)) st.fail
      else st.copy(
        gas = st.gas - extra,
        world = st.world.transfer(st.msg.self, beneficiary, bal),
        accessedAccounts = st.accessedAccounts ++ Set(beneficiary),
        status = Status.Halted)
    }
  }.ensuring(r =>
    !r.isRunning && r.gas <= st.gas
    && (r.status == Status.Halted ==>
         (st.stack.data.nonEmpty
          && r.accessedAccounts.contains(Address.fromWord(st.stack.data.head))
          && r.world == st.world.transfer(st.msg.self, Address.fromWord(st.stack.data.head), st.world.balanceOf(st.msg.self)))))

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
            s1.accessedAccounts)
          CallEnter(child, s1.copy(gas = s1.gas - g), rest, g, false, false, callee, s.world)
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
            s1.storage, s1.original, s1.accessedAccounts)
          CallEnter(child, s1.copy(gas = s1.gas - g), rest, g, true, true, s1.msg.self, s.world)
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
            transferred.storageOf(callee), transferred.storageOf(callee), s1.accessedAccounts)
          CallEnter(child, s1.copy(gas = s1.gas - baseFwd), rest, g, true, false, callee, s.world)
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
            s1.accessedAccounts)
          CallEnter(child, s1.copy(gas = s1.gas - baseFwd), rest, g, true, true, s1.msg.self, s.world)
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
    if (enter.rest.data.size >= Stack.MAXIMUM_STACK_SIZE) enter.parentForwarded.fail
    else enter.parentForwarded.copy(
      gas = enter.parentForwarded.gas + refund,
      stack = enter.rest.push(if (success) Word256.One else Word256.Zero),
      returnData = childRes.returnData,
      world = if (commit) childRes.world.withStorage(enter.self, childRes.storage) else enter.preWorld,
      storage = if (commit && enter.sameAccount) childRes.storage else enter.parentForwarded.storage,
      accessedSlots = if (commit && enter.sameAccount) childRes.accessedSlots else enter.parentForwarded.accessedSlots,
      logs = if (commit) childRes.logs else enter.parentForwarded.logs,
      refund = if (commit) enter.parentForwarded.refund + childRes.refund else enter.parentForwarded.refund
    ).advancePc(1)
  }.ensuring(r => r.gas <= enter.parentForwarded.gas + enter.forwarded)

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
    } else {
      val s1 = step(s)
      if (!s1.isRunning) s1 else run(s1)
    }
  }.ensuring(r => !r.isRunning)
