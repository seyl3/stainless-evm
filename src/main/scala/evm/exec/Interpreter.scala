package evm.exec

import stainless.lang.*
import evm.value.Word256
import evm.math.Gas
import evm.math.EvmMath
import evm.math.EvmMath.MAX_VALUE
import evm.state.Stack
import evm.code.Opcode

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

  def execute(s1: ExecState, op: Opcode): ExecState = {
    op match
      case Opcode.STOP => s1.halt
      case Opcode.JUMPDEST => s1.advancePc(1)
      case Opcode.POP =>
        if (s1.stack.data.isEmpty) s1.fail
        else s1.copy(stack = s1.stack.pop()._2).advancePc(1)

      case Opcode.ADD => binop(s1, (a, b) => a + b)
      case Opcode.SUB => binop(s1, (a, b) => a - b)
      case Opcode.MUL => binop(s1, (a, b) => a * b)
      case Opcode.DIV => binop(s1, (a, b) => a / b)
      case Opcode.SDIV => binop(s1, (a, b) => a.sdiv(b))
      case Opcode.MOD => binop(s1, (a, b) => a % b)
      case Opcode.SMOD => binop(s1, (a, b) => a.smod(b))
      case Opcode.EXP =>
        if (s1.stack.data.size < 2) s1.fail
        else {
          val extra = 50 * EvmMath.byteLength(s1.stack.data.tail.head.value)
          if (s1.outOfGas(extra)) s1.fail
          else binop(s1.chargeGas(extra), (a, b) => a ** b)
        }
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
        if (s1.stack.data.size >= Stack.MAXIMUM_STACK_SIZE || s1.memory.size > MAX_VALUE) s1.fail
        else s1.copy(stack = s1.stack.push(Word256(s1.memory.size))).advancePc(1)

      case Opcode.MLOAD =>
        if (s1.stack.data.isEmpty) s1.fail
        else {
          val (o, t) = s1.stack.pop()
          val extra = memExpandCost(s1, o.value + 32)
          if (s1.outOfGas(extra)) s1.fail
          else {
            val s2 = s1.chargeGas(extra)
            s2.copy(stack = t.push(s2.memory.load(o.value)),
                    memory = s2.memory.expand(o.value + 32)).advancePc(1)
          }
        }

      case Opcode.MSTORE =>
        if (s1.stack.data.size < 2) s1.fail
        else {
          val (o, t1) = s1.stack.pop()
          val (v, t2) = t1.pop()
          val extra = memExpandCost(s1, o.value + 32)
          if (s1.outOfGas(extra)) s1.fail
          else s1.chargeGas(extra).copy(stack = t2, memory = s1.memory.store(o.value, v)).advancePc(1)
        }

      case Opcode.MSTORE8 =>
        if (s1.stack.data.size < 2) s1.fail
        else {
          val (o, t1) = s1.stack.pop()
          val (v, t2) = t1.pop()
          val extra = memExpandCost(s1, o.value + 1)
          if (s1.outOfGas(extra)) s1.fail
          else s1.chargeGas(extra).copy(stack = t2, memory = s1.memory.store8(o.value, v)).advancePc(1)
        }

      case Opcode.MCOPY =>
        if (s1.stack.data.size < 3) s1.fail
        else {
          val (d, t1) = s1.stack.pop()
          val (sr, t2) = t1.pop()
          val (l, t3) = t2.pop()
          val end = if (d.value > sr.value) d.value + l.value else sr.value + l.value
          val extra = if (l.value == 0) BigInt(0) else 3 * Gas.words(l.value) + memExpandCost(s1, end)
          if (s1.outOfGas(extra)) s1.fail
          else s1.chargeGas(extra).copy(stack = t3, memory = s1.memory.mcopy(d.value, sr.value, l.value)).advancePc(1)
        }

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

  def run(s: ExecState): ExecState = {
    decreases(s.gas)
    if (!s.isRunning) s
    else {
      val s1 = step(s)
      if (!s1.isRunning) s1 else run(s1)
    }
  }.ensuring(r => !r.isRunning)
