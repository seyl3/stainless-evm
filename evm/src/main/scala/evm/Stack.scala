package evm

import stainless.collection.*
import stainless.lang.*
import stainless.proof.*
import evm.core.Word256

object ListLemmas {
  def updatedApplyOther[T](l: List[T], i: BigInt, j: BigInt, y: T): Boolean = {
    require(0 <= i && i < l.size && 0 <= j && j < l.size && i != j)
    decreases(l)
    (l.updated(i, y)(j) == l(j)) because {
      l match {
        case Nil() => true
        case Cons(x, xs) =>
          if (i == 0 || j == 0) true
          else updatedApplyOther(xs, i - 1, j - 1, y)
      }
    }
  }.holds
}

object Stack {
    val MAXIMUM_STACK_SIZE: BigInt = 1024

    def empty: Stack = Stack(Nil())
}

case class Stack(data: List[Word256]) {
    require(data.size <= Stack.MAXIMUM_STACK_SIZE)

    def push(value: Word256): Stack = {
        require(data.size < Stack.MAXIMUM_STACK_SIZE)
        Stack(Cons(value, data))
    }.ensuring(result =>
        result.data.size == data.size + 1
        && result.data.head == value
        && result.data.tail == data)

    def pop(): (Word256, Stack) = {
        require(data.nonEmpty)
        (data.head, Stack(data.tail))
    }.ensuring(result =>
        result._2.data.size == data.size - 1
        && result._1 == data.head
        && result._2.data == data.tail)

    def peek(i: BigInt): Word256 = {
        require(0 <= i && i < data.size)
        data(i)
    }.ensuring(result => result == data(i))

    def dup(n: BigInt): Stack = {
        require(n >= 1 && n <= data.size && data.size < Stack.MAXIMUM_STACK_SIZE)
        Stack(Cons(data(n - 1), data))
    }.ensuring(result =>
        result.data.size == data.size + 1
        && result.data.head == data(n - 1)
        && result.data.tail == data)

    def swap(n: BigInt): Stack = {
        require(n >= 1 && n < data.size)
        val top = data(0)
        val nth = data(n)
        val a = data.updated(0, nth)
        val swapped = a.updated(n, top)
        ListLemmas.updatedApplyOther(a, n, 0, top)
        Stack(swapped)
    }.ensuring(result =>
        result.data.size == data.size
        && result.data(0) == data(n)
        && result.data(n) == data(0))
}
