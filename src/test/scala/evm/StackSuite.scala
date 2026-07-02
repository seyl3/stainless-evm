package evm

import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*
import evm.math.*

import evm.value.Word256

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

  test("peek reads by index from the top without popping") {
    val s = build(10, 20, 30)
    assertEquals(s.peek(0).value, BigInt(10))
    assertEquals(s.peek(1).value, BigInt(20))
    assertEquals(s.peek(2).value, BigInt(30))
    assertEquals(s.data.size, BigInt(3))
  }

  test("dup(n) clones the n-th item onto the top") {
    val s = build(10, 20, 30)
    val d1 = s.dup(1)
    assertEquals(d1.data.size, BigInt(4))
    assertEquals(d1.peek(0).value, BigInt(10))
    assertEquals(d1.peek(1).value, BigInt(10))
    val d3 = s.dup(3)
    assertEquals(d3.peek(0).value, BigInt(30))
    assertEquals(d3.peek(1).value, BigInt(10))
  }

  test("swap(n) swaps the top with the (n+1)-th item") {
    val s = build(10, 20, 30, 40)
    val s1 = s.swap(1)
    assertEquals(s1.peek(0).value, BigInt(20))
    assertEquals(s1.peek(1).value, BigInt(10))
    assertEquals(s1.peek(2).value, BigInt(30))
    val s3 = s.swap(3)
    assertEquals(s3.peek(0).value, BigInt(40))
    assertEquals(s3.peek(3).value, BigInt(10))
    assertEquals(s3.peek(1).value, BigInt(20))
    assertEquals(s3.data.size, BigInt(4))
  }
}
