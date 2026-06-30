package evm.proofs

import stainless.collection.*
import stainless.lang.*
import stainless.proof.*

object Collections {
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
