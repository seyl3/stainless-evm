package evm

import stainless.collection.*
import stainless.lang.*

object Code:
  def empty: Code = Code(Nil())

case class Code(code: List[Int]):

  def size: BigInt = code.size

  def byteAt(pc: BigInt): Int = {
    require(0 <= pc && pc < code.size)
    code(pc)
  }.ensuring(_ == code(pc))

  def opcodeAt(pc: BigInt): Option[Opcode] = {
    require(0 <= pc && pc < code.size)
    Opcode.decode(code(pc))
  }

  def jumpDestsFrom(i: BigInt, acc: Set[BigInt]): Set[BigInt] = {
    require(0 <= i && i <= code.size)
    decreases(code.size - i)
    if (i >= code.size) acc
    else {
      val w = Opcode.decode(code(i)) match
        case Some(op) => Opcode.pushWidth(op)
        case None() => BigInt(0)
      val acc2 = if (Opcode.decode(code(i)) == Some(Opcode.JUMPDEST)) acc ++ Set(i) else acc
      val next = i + 1 + w
      jumpDestsFrom(if (next > code.size) code.size else next, acc2)
    }
  }

  def validJumpDests: Set[BigInt] = jumpDestsFrom(0, Set.empty[BigInt])

  def isValidJumpDest(pc: BigInt): Boolean = validJumpDests.contains(pc)
