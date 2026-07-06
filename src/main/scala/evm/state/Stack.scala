package evm.state

import stainless.collection.*
import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*
import evm.value.Word256
import evm.math.Collections

// The EVM operand stack: a list of 256-bit words, head = top, capped at 1024.
object Stack {
    val MAXIMUM_STACK_SIZE: BigInt = 1024

    def empty: Stack = Stack(Nil())
}

// The depth bound is a class invariant, so push carries a not-full precondition
// and every operation is proven to respect the 1024-item limit. Each op pins its
// exact effect (new head, preserved tail) rather than just the size.
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

    // SWAPn: exchange the top with the (n+1)th item via two list updates. The
    // Collections lemma proves the first update to index 0 survives the second.
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

    // A swap leaves every other position untouched (used to reason about the rest
    // of the stack after a SWAP).
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
