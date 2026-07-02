package evm

import stainless.collection.*
import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*
import evm.core.Word256
import evm.proofs.Collections

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
        Collections.updatedApplyOther(a, n, 0, top)
        Stack(swapped)
    }.ensuring(result =>
        result.data.size == data.size
        && result.data(0) == data(n)
        && result.data(n) == data(0))

    @ghost
    def swapPreservesOther(n: BigInt, k: BigInt): Boolean = {
        require(n >= 1 && n < data.size && 0 <= k && k < data.size && k != 0 && k != n)
        val nth = data(n)
        val top = data(0)
        val a = data.updated(0, nth)
        (swap(n).data(k) == data(k)) because {
            Collections.updatedApplyOther(a, n, k, top) &&
            Collections.updatedApplyOther(data, 0, k, nth)
        }
    }.holds
}
