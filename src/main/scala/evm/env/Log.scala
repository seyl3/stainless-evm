package evm.env

import stainless.collection.*
import evm.value.Word256

case class Log(address: Address, topics: List[Word256], data: List[BigInt])
