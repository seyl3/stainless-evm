package evm.code

import stainless.collection.*
import stainless.lang.*
import evm.value.Word256
import evm.math.EvmMath
import evm.math.EvmMath.pow
import evm.math.Bytes

object Code:
  def empty: Code = Code(Nil())

case class Code(code: List[BigInt]):

  def size: BigInt = code.size

  def byteAt(pc: BigInt): BigInt = {
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

  def byteOrZero(i: BigInt): BigInt = {
    require(i >= 0)
    if (i < code.size) Bytes.emod256(code(i)) else BigInt(0)
  }.ensuring(r => 0 <= r && r < 256)

  def immediateValue(start: BigInt, n: BigInt): BigInt = {
    require(start >= 0 && 0 <= n && n <= 32)
    decreases(n)
    if (n == 0) BigInt(0)
    else byteOrZero(start) * pow(BigInt(256), n - 1) + immediateValue(start + 1, n - 1)
  }.ensuring(r => 0 <= r && r < pow(BigInt(256), n))

  def pushValue(start: BigInt, n: BigInt): Word256 = {
    require(start >= 0 && 0 <= n && n <= 32)
    EvmMath.pow256Le(n)
    Word256(immediateValue(start, n))
  }.ensuring(r => r.value == immediateValue(start, n))
