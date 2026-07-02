package evm

import stainless.lang.*
import evm.core.Word256

object Interpreter:

  def step(s: ExecState): ExecState = {
    if (!s.isRunning) s
    else if (s.pc >= s.code.size) s.halt
    else

      s.code.opcodeAt(s.pc) match
        case None() => s.fail
        case Some(op) =>

          val cost = Opcode.baseGas(op)
          if (s.outOfGas(cost)) s.fail
          else {
            val s1 = s.chargeGas(cost)
            
            op match
              case Opcode.STOP => s1.halt
              case Opcode.JUMPDEST => s1.advancePc(1)
              case Opcode.POP =>
                if (s1.stack.data.isEmpty) s1.fail
                else s1.copy(stack = s1.stack.pop()._2).advancePc(1)
              case Opcode.ADD =>
                if (s1.stack.data.size < 2) s1.fail
                else {
                  val (a, t1) = s1.stack.pop()
                  val (b, t2) = t1.pop()
                  s1.copy(stack = t2.push(a + b)).advancePc(1)
                }
              case Opcode.PUSH1 =>
                if (s1.stack.data.size >= Stack.MAXIMUM_STACK_SIZE) s1.fail
                else s1.copy(stack = s1.stack.push(s1.code.pushValue(s1.pc + 1, 1))).advancePc(2)
              case _ => s1.fail
          }
  }.ensuring(r => !r.isRunning || r.gas < s.gas)

  def run(s: ExecState): ExecState = {
    decreases(s.gas)
    if (!s.isRunning) s
    else {
      val s1 = step(s)
      if (!s1.isRunning) s1 else run(s1)
    }
  }.ensuring(r => !r.isRunning)
