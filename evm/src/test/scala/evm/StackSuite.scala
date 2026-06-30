package evm

import evm.core.Word256

class StackSuite extends munit.FunSuite {

  def w(n: BigInt): Word256 = Word256(n)

  def build(xs: BigInt*): Stack =
    xs.foldRight(Stack.empty)((x, s) => s.push(w(x)))

  test("empty stack has size zero") {
    assertEquals(Stack.empty.data.size, BigInt(0))
  }

  test("push increases size and places value on top") {
    val s = Stack.empty.push(w(5))
    assertEquals(s.data.size, BigInt(1))
    val (top, rest) = s.pop()
    assertEquals(top.value, BigInt(5))
    assertEquals(rest.data.size, BigInt(0))
  }

  test("pop returns the head and the tail") {
    val (top, rest) = build(1, 2, 3).pop()
    assertEquals(top.value, BigInt(1))
    assertEquals(rest.data.size, BigInt(2))
    assertEquals(rest.pop()._1.value, BigInt(2))
  }

  test("push then pop round-trips") {
    val s0 = build(7, 8)
    val (top, rest) = s0.push(w(9)).pop()
    assertEquals(top.value, BigInt(9))
    assertEquals(rest.data.size, s0.data.size)
  }
}
