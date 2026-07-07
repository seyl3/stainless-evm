package evm.env

import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*
import evm.value.Word256
import evm.code.Code
import evm.state.Storage

// An account: balance, code, storage, and nonce. The two-argument apply builds a
// fresh account (empty storage, zero nonce).
object Account:
  def apply(balance: Word256, code: Code): Account = Account(balance, code, Storage.empty, BigInt(0))

case class Account(balance: Word256, code: Code, storage: Storage, nonce: BigInt):
  require(nonce >= 0)

  // Exposes the nonce bound (the class invariant) as an invokable fact, so an
  // updater copying this account can discharge the new account's invariant without
  // the solver re-deriving nonce >= 0 through the enclosing Map lookup.
  @ghost
  def nonceNonNeg: Boolean = { nonce >= 0 }.holds

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
    val acc = getOrEmpty(a)
    acc.nonceNonNeg
    acc.nonce
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).nonce else BigInt(0)) && r >= 0)

  def withStorage(a: Address, s: Storage): WorldState = {
    val acc = getOrEmpty(a)
    acc.nonceNonNeg
    WorldState(accounts.updated(a, acc.copy(storage = s)))
  }.ensuring(r =>
    r.storageOf(a) == s && r.balanceOf(a) == balanceOf(a)
    && r.codeOf(a) == codeOf(a) && r.nonceOf(a) == nonceOf(a))

  def withBalance(a: Address, bal: Word256): WorldState = {
    val acc = getOrEmpty(a)
    acc.nonceNonNeg
    WorldState(accounts.updated(a, acc.copy(balance = bal)))
  }.ensuring(r =>
    r.balanceOf(a) == bal && r.storageOf(a) == storageOf(a)
    && r.codeOf(a) == codeOf(a) && r.nonceOf(a) == nonceOf(a))

  def withNonce(a: Address, n: BigInt): WorldState = {
    require(n >= 0)
    WorldState(accounts.updated(a, getOrEmpty(a).copy(nonce = n)))
  }.ensuring(r =>
    r.nonceOf(a) == n && r.balanceOf(a) == balanceOf(a)
    && r.codeOf(a) == codeOf(a) && r.storageOf(a) == storageOf(a))

  def withCode(a: Address, c: Code): WorldState = {
    val acc = getOrEmpty(a)
    acc.nonceNonNeg
    WorldState(accounts.updated(a, acc.copy(code = c)))
  }.ensuring(r =>
    r.codeOf(a) == c && r.balanceOf(a) == balanceOf(a)
    && r.nonceOf(a) == nonceOf(a) && r.storageOf(a) == storageOf(a))

  // Clear an account to empty (EIP-6780 SELFDESTRUCT of a same-tx-created contract):
  // its code, storage, nonce, and balance are dropped. The balance must be moved
  // out first; whatever remains here is burned.
  def destroy(a: Address): WorldState = {
    WorldState(accounts.updated(a, Account(Word256.Zero, Code.empty)))
  }.ensuring(r => r.balanceOf(a) == Word256.Zero && r.codeOf(a).size == 0)

  // Move value from one account to another. Sufficient balance is a precondition
  // (so the subtraction cannot wrap), pushing the obligation onto every caller.
  def transfer(from: Address, to: Address, value: Word256): WorldState = {
    require(balanceOf(from).value >= value.value)
    val w1 = withBalance(from, balanceOf(from) - value)
    w1.withBalance(to, w1.balanceOf(to) + value)
  }
