package evm.env

import stainless.lang.*
import evm.value.Word256
import evm.code.Code
import evm.state.Storage

object Account:
  def apply(balance: Word256, code: Code): Account = Account(balance, code, Storage.empty)

case class Account(balance: Word256, code: Code, storage: Storage)

object WorldState:
  def empty: WorldState = WorldState(Map.empty[Address, Account])

case class WorldState(accounts: Map[Address, Account]):

  def balanceOf(a: Address): Word256 = {
    if (accounts.contains(a)) accounts(a).balance else Word256.Zero
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).balance else Word256.Zero))

  def codeOf(a: Address): Code = {
    if (accounts.contains(a)) accounts(a).code else Code.empty
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).code else Code.empty))

  def storageOf(a: Address): Storage = {
    if (accounts.contains(a)) accounts(a).storage else Storage.empty
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).storage else Storage.empty))

  def withStorage(a: Address, s: Storage): WorldState = {
    val acc = if (accounts.contains(a)) accounts(a) else Account(Word256.Zero, Code.empty, Storage.empty)
    WorldState(accounts.updated(a, acc.copy(storage = s)))
  }.ensuring(r => r.storageOf(a) == s)
