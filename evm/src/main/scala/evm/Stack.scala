package evm

import stainless.collection.*
import stainless.lang.*
import evm.core.Word256

object Stack {
    val MAXIMUM_STACK_SIZE: BigInt = 1024

    def empty: Stack = Stack(Nil())
}

case class Stack(data: List[Word256]) {
    require(data.size >= 0 && data.size <= Stack.MAXIMUM_STACK_SIZE)

    def push(value: Word256): Stack = {
        require(data.size < Stack.MAXIMUM_STACK_SIZE)

        Stack(Cons(value, data))

    }.ensuring(result => result.data.size == data.size + 1)

    def pop(): (Word256, Stack) = {
        require(data.nonEmpty)

        (data.head, Stack(data.tail))

    }.ensuring(result => result._2.data.size == data.size - 1)
}