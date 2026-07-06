package evm.code

import stainless.collection.*
import stainless.lang.*
import evm.value.Word256
import evm.math.EvmMath
import evm.math.EvmMath.pow
import evm.math.Bytes
import evm.math.ByteList

// A contract's bytecode as a byte list, with opcode decoding, JUMPDEST analysis,
// and PUSH-immediate reading. This layer sits below env/exec so an Account can
// hold Code.
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

  // Scan from index i collecting the valid JUMPDEST positions. Skipping each
  // opcode's immediate bytes (pushWidth) is what makes a JUMPDEST byte that is
  // actually PUSH data correctly excluded. Decreases on the remaining code.
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

  // The set of legal jump targets; JUMP/JUMPI check membership.
  def validJumpDests: Set[BigInt] = jumpDestsFrom(0, Set.empty[BigInt])

  def isValidJumpDest(pc: BigInt): Boolean = validJumpDests.contains(pc)

  def byteOrZero(i: BigInt): BigInt = {
    require(i >= 0)
    ByteList.byteOrZero(code, i)
  }.ensuring(r => 0 <= r && r < 256)

  def immediateValue(start: BigInt, n: BigInt): BigInt = {
    require(start >= 0 && 0 <= n && n <= 32)
    ByteList.readWord(code, start, n)
  }.ensuring(r => 0 <= r && r < pow(BigInt(256), n))

  // The n-byte PUSH immediate at `start`, as a word. pow256Le bounds it below
  // 2^256 so it fits a Word256.
  def pushValue(start: BigInt, n: BigInt): Word256 = {
    require(start >= 0 && 0 <= n && n <= 32)
    EvmMath.pow256Le(n)
    Word256(immediateValue(start, n))
  }.ensuring(r => r.value == immediateValue(start, n))
