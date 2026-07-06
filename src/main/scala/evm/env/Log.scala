package evm.env

import stainless.collection.*
import evm.value.Word256

// An emitted log record (from LOG0-4): the emitting account, its indexed topics,
// and the raw data bytes.
case class Log(address: Address, topics: List[Word256], data: List[BigInt])
