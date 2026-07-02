package evm.env

import stainless.lang.*
import evm.core.Word256
import evm.Code

case class Account(balance: Word256, code: Code)

object WorldState:
  def empty: WorldState = WorldState(Map.empty[Address, Account])

case class WorldState(accounts: Map[Address, Account]):

  def balanceOf(a: Address): Word256 = {
    if (accounts.contains(a)) accounts(a).balance else Word256.Zero
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).balance else Word256.Zero))

  def codeOf(a: Address): Code = {
    if (accounts.contains(a)) accounts(a).code else Code.empty
  }.ensuring(r => r == (if (accounts.contains(a)) accounts(a).code else Code.empty))
