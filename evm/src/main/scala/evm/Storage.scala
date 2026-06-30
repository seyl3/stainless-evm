package evm

import stainless.lang.*
import stainless.annotation.*
import stainless.proof.*
import evm.core.Word256

object Storage {
  def empty: Storage = Storage(Map.empty[Word256, Word256])
}

case class Storage(data: Map[Word256, Word256]) {

  def load(key: Word256): Word256 = {
    if (data.contains(key)) data(key) else Word256.Zero
  }.ensuring(r => r == (if (data.contains(key)) data(key) else Word256.Zero))

  def store(key: Word256, value: Word256): Storage = {
    Storage(data.updated(key, value))
  }.ensuring(r => r.load(key) == value)

  @ghost
  def storePreservesOther(key: Word256, value: Word256, other: Word256): Boolean = {
    require(other != key)
    store(key, value).load(other) == load(other)
  }.holds
}
