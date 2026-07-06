package evm.env

import stainless.lang.*
import evm.value.Word256
import evm.code.Code
import evm.state.Storage

// An account: balance, code, storage, and nonce. The two-argument apply builds a
// fresh account (empty storage, zero nonce).
object Account:
  def apply(balance: Word256, code: Code): Account = Account(balance, code, Storage.empty, BigInt(0))

case class Account(balance: Word256, code: Code, storage: Storage, nonce: BigInt)

// The world state: a map from address to account, with default-zero lookups for
// absent accounts. Each `with*` updater proves it changes only its target field
// and preserves the other three, so callers can compose them without re-proving
// that a balance write left storage or nonce intact.
object WorldState:
  def empty: WorldState = WorldState(Map.empty[Address, Account])

case class WorldState(accounts: Map[Address, Account]):

  // The account at a, or a fresh empty account for an address never seen.
  def getOrEmpty(a: Address): Account = {
    if (accounts.contains(a)) accounts(a) else Account(Word256.Zero, Code.empty)
  }

  def balanceOf(a: Address): Word256 = {
    getOrEmpty(a).balance
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).balance else Word256.Zero))

  def codeOf(a: Address): Code = {
    getOrEmpty(a).code
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).code else Code.empty))

  def storageOf(a: Address): Storage = {
    getOrEmpty(a).storage
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).storage else Storage.empty))

  def nonceOf(a: Address): BigInt = {
    getOrEmpty(a).nonce
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).nonce else BigInt(0)))

  def withStorage(a: Address, s: Storage): WorldState = {
    WorldState(accounts.updated(a, getOrEmpty(a).copy(storage = s)))
  }.ensuring(r =>
    r.storageOf(a) == s && r.balanceOf(a) == balanceOf(a)
    && r.codeOf(a) == codeOf(a) && r.nonceOf(a) == nonceOf(a))

  def withBalance(a: Address, bal: Word256): WorldState = {
    WorldState(accounts.updated(a, getOrEmpty(a).copy(balance = bal)))
  }.ensuring(r =>
    r.balanceOf(a) == bal && r.storageOf(a) == storageOf(a)
    && r.codeOf(a) == codeOf(a) && r.nonceOf(a) == nonceOf(a))

  def withNonce(a: Address, n: BigInt): WorldState = {
    require(n >= 0)
    WorldState(accounts.updated(a, getOrEmpty(a).copy(nonce = n)))
  }.ensuring(r =>
    r.nonceOf(a) == n && r.balanceOf(a) == balanceOf(a)
    && r.codeOf(a) == codeOf(a) && r.storageOf(a) == storageOf(a))

  // Move value from one account to another. Sufficient balance is a precondition
  // (so the subtraction cannot wrap), pushing the obligation onto every caller.
  def transfer(from: Address, to: Address, value: Word256): WorldState = {
    require(balanceOf(from).value >= value.value)
    val w1 = withBalance(from, balanceOf(from) - value)
    w1.withBalance(to, w1.balanceOf(to) + value)
  }
