package evm

import evm.value.*
import evm.state.*
import evm.code.*
import evm.env.*
import evm.exec.*
import evm.math.*

import evm.math.Gas

class GasSuite extends munit.FunSuite {

  test("words rounds bytes up to 32-byte words") {
    assertEquals(Gas.words(0), BigInt(0))
    assertEquals(Gas.words(1), BigInt(1))
    assertEquals(Gas.words(32), BigInt(1))
    assertEquals(Gas.words(33), BigInt(2))
  }

  test("memoryCost is the linear plus quadratic word formula") {
    assertEquals(Gas.memoryCost(0), BigInt(0))
    assertEquals(Gas.memoryCost(1), BigInt(3))
    assertEquals(Gas.memoryCost(32), BigInt(98))
  }

  test("memoryExpansionCost is the cost difference and never negative") {
    assertEquals(Gas.memoryExpansionCost(0, 1), BigInt(3))
    assertEquals(Gas.memoryExpansionCost(0, 32), BigInt(98))
    assertEquals(Gas.memoryExpansionCost(5, 5), BigInt(0))
  }

  test("copyCost charges 3 per word") {
    assertEquals(Gas.copyCost(0), BigInt(0))
    assertEquals(Gas.copyCost(32), BigInt(3))
    assertEquals(Gas.copyCost(33), BigInt(6))
  }

  test("keccakCost is 30 plus 6 per word") {
    assertEquals(Gas.keccakCost(0), BigInt(30))
    assertEquals(Gas.keccakCost(32), BigInt(36))
  }

  test("expCost is 10 plus 50 per exponent byte") {
    assertEquals(Gas.expCost(0), BigInt(10))
    assertEquals(Gas.expCost(2), BigInt(110))
  }

  test("logCost charges base, data and topics") {
    assertEquals(Gas.logCost(0, 0), BigInt(375))
    assertEquals(Gas.logCost(10, 2), BigInt(1205))
  }

  test("accessCost distinguishes cold from warm") {
    assertEquals(Gas.accessCost(true), BigInt(2100))
    assertEquals(Gas.accessCost(false), BigInt(100))
  }

  test("sstoreCost follows the set, reset, no-op and cold cases") {
    assertEquals(Gas.sstoreCost(0, 0, 5, false), BigInt(20000))
    assertEquals(Gas.sstoreCost(0, 0, 5, true), BigInt(22100))
    assertEquals(Gas.sstoreCost(7, 7, 7, false), BigInt(100))
    assertEquals(Gas.sstoreCost(5, 5, 0, false), BigInt(2900))
    assertEquals(Gas.sstoreCost(5, 3, 0, false), BigInt(100))
  }
}
