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
