package evm.code

import stainless.lang.*

// The Osaka opcode set as an ADT (one case per instruction, each annotated with
// its meaning). The companion maps opcodes to and from their hex encoding, to
// their static base gas, and to the PUSH immediate width.
enum Opcode:
  case STOP // Halts execution
  case ADD // Addition operation
  case MUL // Multiplication operation
  case SUB // Subtraction operation
  case DIV // Integer division operation
  case SDIV // Signed integer division operation (truncated)
  case MOD // Modulo remainder operation
  case SMOD // Signed modulo remainder operation
  case ADDMOD // Modulo addition operation
  case MULMOD // Modulo multiplication operation
  case EXP // Exponential operation
  case SIGNEXTEND // Extend length of two's complement signed integer

  case LT // Less-than comparison
  case GT // Greater-than comparison
  case SLT // Signed less-than comparison
  case SGT // Signed greater-than comparison
  case EQ // Equality comparison
  case ISZERO // Is-zero comparison
  case AND // Bitwise AND operation
  case OR // Bitwise OR operation
  case XOR // Bitwise XOR operation
  case NOT // Bitwise NOT operation
  case BYTE // Retrieve single byte from word
  case SHL // Left shift operation
  case SHR // Logical right shift operation
  case SAR // Arithmetic (signed) right shift operation
  case CLZ // Count leading zero bits

  case KECCAK256 // Compute Keccak-256 hash

  case ADDRESS // Get address of currently executing account
  case BALANCE // Get balance of the given account
  case ORIGIN // Get execution origination address
  case CALLER // Get caller address
  case CALLVALUE // Get deposited value by the responsible execution
  case CALLDATALOAD // Get input data of current environment
  case CALLDATASIZE // Get size of input data in current environment
  case CALLDATACOPY // Copy input data in current environment to memory
  case CODESIZE // Get size of code running in current environment
  case CODECOPY // Copy code running in current environment to memory
  case GASPRICE // Get price of gas in current environment
  case EXTCODESIZE // Get size of an account's code
  case EXTCODECOPY // Copy an account's code to memory
  case RETURNDATASIZE // Get size of output data from the previous call
  case RETURNDATACOPY // 0x3E Copy output data from the previous call to memory
  case EXTCODEHASH  // 0x3F Get hash of an account's code

  case BLOCKHASH // Get the hash of one of the 256 most recent blocks
  case COINBASE // Get the block's beneficiary address
  case TIMESTAMP // Get the block's timestamp
  case NUMBER // Get the block's number
  case PREVRANDAO // Get the previous block's RANDAO mix
  case GASLIMIT // Get the block's gas limit
  case CHAINID // Get the chain ID
  case SELFBALANCE // Get balance of currently executing account
  case BASEFEE // Get the base fee
  case BLOBHASH // Get versioned hashes
  case BLOBBASEFEE // Get the blob base-fee of the current block

  case POP // Remove item from stack
  case MLOAD // Load word from memory
  case MSTORE // Save word to memory
  case MSTORE8 // Save byte to memory
  case SLOAD // Load word from storage
  case SSTORE // Save word to storage
  case JUMP // Alter the program counter
  case JUMPI // Conditionally alter the program counter
  case PC // Get the value of the program counter
  case MSIZE // Get the size of active memory in bytes
  case GAS // Get the amount of available gas
  case JUMPDEST // Mark a valid destination for jumps
  case TLOAD // Load word from transient storage
  case TSTORE // Save word to transient storage
  case MCOPY // Copy memory areas

  case PUSH0 // Place value 0 on stack
  case PUSH1 // Place 1 byte item on stack
  case PUSH2 // Place 2 byte item on stack
  case PUSH3 // Place 3 byte item on stack
  case PUSH4 // Place 4 byte item on stack
  case PUSH5 // Place 5 byte item on stack
  case PUSH6 // Place 6 byte item on stack
  case PUSH7 // Place 7 byte item on stack
  case PUSH8 // Place 8 byte item on stack
  case PUSH9 // Place 9 byte item on stack
  case PUSH10 // Place 10 byte item on stack
  case PUSH11 // Place 11 byte item on stack
  case PUSH12 // Place 12 byte item on stack
  case PUSH13 // Place 13 byte item on stack
  case PUSH14 // Place 14 byte item on stack
  case PUSH15 // Place 15 byte item on stack
  case PUSH16 // Place 16 byte item on stack
  case PUSH17 // Place 17 byte item on stack
  case PUSH18 // Place 18 byte item on stack
  case PUSH19 // Place 19 byte item on stack
  case PUSH20 // Place 20 byte item on stack
  case PUSH21 // 0x74 Place 21 byte item on stack
  case PUSH22 // 0x75 Place 22 byte item on stack
  case PUSH23 // 0x76 Place 23 byte item on stack
  case PUSH24 // 0x77 Place 24 byte item on stack
  case PUSH25 // 0x78 Place 25 byte item on stack
  case PUSH26 // 0x79 Place 26 byte item on stack
  case PUSH27 // 0x7A Place 27 byte item on stack
  case PUSH28 // 0x7B Place 28 byte item on stack
  case PUSH29 // 0x7C Place 29 byte item on stack
  case PUSH30 // 0x7D Place 30 byte item on stack
  case PUSH31 // 0x7E Place 31 byte item on stack
  case PUSH32 // 0x7F Place 32 byte item on stack

  case DUP1 // Duplicate 1st stack item
  case DUP2 // Duplicate 2nd stack item
  case DUP3 // Duplicate 3rd stack item
  case DUP4 // Duplicate 4th stack item
  case DUP5 // Duplicate 5th stack item
  case DUP6 // Duplicate 6th stack item
  case DUP7 // Duplicate 7th stack item
  case DUP8 // Duplicate 8th stack item
  case DUP9 // Duplicate 9th stack item
  case DUP10 // Duplicate 10th stack item
  case DUP11 // Duplicate 11th stack item
  case DUP12 // Duplicate 12th stack item
  case DUP13 // Duplicate 13th stack item
  case DUP14 // Duplicate 14th stack item
  case DUP15 // Duplicate 15th stack item
  case DUP16 // Duplicate 16th stack item

  case SWAP1 // Exchange 1st and 2nd stack items
  case SWAP2 // Exchange 1st and 3rd stack items
  case SWAP3 // Exchange 1st and 4th stack items
  case SWAP4 // Exchange 1st and 5th stack items
  case SWAP5 // Exchange 1st and 6th stack items
  case SWAP6 // Exchange 1st and 7th stack items
  case SWAP7 // Exchange 1st and 8th stack items
  case SWAP8 // Exchange 1st and 9th stack items
  case SWAP9 // Exchange 1st and 10th stack items
  case SWAP10 // Exchange 1st and 11th stack items
  case SWAP12 // Exchange 1st and 13th stack items
  case SWAP11 // Exchange 1st and 12th stack items
  case SWAP13 // Exchange 1st and 14th stack items
  case SWAP14 // Exchange 1st and 15th stack items
  case SWAP15 // Exchange 1st and 16th stack items
  case SWAP16 // Exchange 1st and 17th stack items

  case LOG0 // Append log record with no topics
  case LOG1 // Append log record with one topic
  case LOG2 // Append log record with two topics
  case LOG4 // 0xA4 Append log record with four topics
  case LOG3 // log record with three topics

  case CREATE // Create a new account with associated code
  case CALL // Message-call into an account
  case CALLCODE  // Message-call into this account with alternative account's code
  case RETURN // Halt execution returning output data
  case DELEGATECALL // Message-call with an alternative account's code, persisting sender and value
  case CREATE2 // Create a new account with associated code at a predictable address
  case STATICCALL // Static message-call into an account
  case REVERT // Halt execution reverting state changes but returning data and remaining gas
  case INVALID // Designated invalid instruction
  case SELFDESTRUCT // Halt execution and register account for later deletion

object Opcode:
  // Opcode to its byte encoding.
  def hex(op: Opcode): Int = op match
    case Opcode.STOP => 0x00
    case Opcode.ADD => 0x01
    case Opcode.MUL => 0x02
    case Opcode.SUB => 0x03
    case Opcode.DIV => 0x04
    case Opcode.SDIV => 0x05
    case Opcode.MOD => 0x06
    case Opcode.SMOD => 0x07
    case Opcode.ADDMOD => 0x08
    case Opcode.MULMOD => 0x09
    case Opcode.EXP => 0x0A
    case Opcode.SIGNEXTEND => 0x0B
    case Opcode.LT => 0x10
    case Opcode.GT => 0x11
    case Opcode.SLT => 0x12
    case Opcode.SGT => 0x13
    case Opcode.EQ => 0x14
    case Opcode.ISZERO => 0x15
    case Opcode.AND => 0x16
    case Opcode.OR => 0x17
    case Opcode.XOR => 0x18
    case Opcode.NOT => 0x19
    case Opcode.BYTE => 0x1A
    case Opcode.SHL => 0x1B
    case Opcode.SHR => 0x1C
    case Opcode.SAR => 0x1D
    case Opcode.CLZ => 0x1E
    case Opcode.KECCAK256 => 0x20
    case Opcode.ADDRESS => 0x30
    case Opcode.BALANCE => 0x31
    case Opcode.ORIGIN => 0x32
    case Opcode.CALLER => 0x33
    case Opcode.CALLVALUE => 0x34
    case Opcode.CALLDATALOAD => 0x35
    case Opcode.CALLDATASIZE => 0x36
    case Opcode.CALLDATACOPY => 0x37
    case Opcode.CODESIZE => 0x38
    case Opcode.CODECOPY => 0x39
    case Opcode.GASPRICE => 0x3A
    case Opcode.EXTCODESIZE => 0x3B
    case Opcode.EXTCODECOPY => 0x3C
    case Opcode.RETURNDATASIZE => 0x3D
    case Opcode.RETURNDATACOPY => 0x3E
    case Opcode.EXTCODEHASH => 0x3F
    case Opcode.BLOCKHASH => 0x40
    case Opcode.COINBASE => 0x41
    case Opcode.TIMESTAMP => 0x42
    case Opcode.NUMBER => 0x43
    case Opcode.PREVRANDAO => 0x44
    case Opcode.GASLIMIT => 0x45
    case Opcode.CHAINID => 0x46
    case Opcode.SELFBALANCE => 0x47
    case Opcode.BASEFEE => 0x48
    case Opcode.BLOBHASH => 0x49
    case Opcode.BLOBBASEFEE => 0x4A
    case Opcode.POP => 0x50
    case Opcode.MLOAD => 0x51
    case Opcode.MSTORE => 0x52
    case Opcode.MSTORE8 => 0x53
    case Opcode.SLOAD => 0x54
    case Opcode.SSTORE => 0x55
    case Opcode.JUMP => 0x56
    case Opcode.JUMPI => 0x57
    case Opcode.PC => 0x58
    case Opcode.MSIZE => 0x59
    case Opcode.GAS => 0x5A
    case Opcode.JUMPDEST => 0x5B
    case Opcode.TLOAD => 0x5C
    case Opcode.TSTORE => 0x5D
    case Opcode.MCOPY => 0x5E
    case Opcode.PUSH0 => 0x5F
    case Opcode.PUSH1 => 0x60
    case Opcode.PUSH2 => 0x61
    case Opcode.PUSH3 => 0x62
    case Opcode.PUSH4 => 0x63
    case Opcode.PUSH5 => 0x64
    case Opcode.PUSH6 => 0x65
    case Opcode.PUSH7 => 0x66
    case Opcode.PUSH8 => 0x67
    case Opcode.PUSH9 => 0x68
    case Opcode.PUSH10 => 0x69
    case Opcode.PUSH11 => 0x6A
    case Opcode.PUSH12 => 0x6B
    case Opcode.PUSH13 => 0x6C
    case Opcode.PUSH14 => 0x6D
    case Opcode.PUSH15 => 0x6E
    case Opcode.PUSH16 => 0x6F
    case Opcode.PUSH17 => 0x70
    case Opcode.PUSH18 => 0x71
    case Opcode.PUSH19 => 0x72
    case Opcode.PUSH20 => 0x73
    case Opcode.PUSH21 => 0x74
    case Opcode.PUSH22 => 0x75
    case Opcode.PUSH23 => 0x76
    case Opcode.PUSH24 => 0x77
    case Opcode.PUSH25 => 0x78
    case Opcode.PUSH26 => 0x79
    case Opcode.PUSH27 => 0x7A
    case Opcode.PUSH28 => 0x7B
    case Opcode.PUSH29 => 0x7C
    case Opcode.PUSH30 => 0x7D
    case Opcode.PUSH31 => 0x7E
    case Opcode.PUSH32 => 0x7F
    case Opcode.DUP1 => 0x80
    case Opcode.DUP2 => 0x81
    case Opcode.DUP3 => 0x82
    case Opcode.DUP4 => 0x83
    case Opcode.DUP5 => 0x84
    case Opcode.DUP6 => 0x85
    case Opcode.DUP7 => 0x86
    case Opcode.DUP8 => 0x87
    case Opcode.DUP9 => 0x88
    case Opcode.DUP10 => 0x89
    case Opcode.DUP11 => 0x8A
    case Opcode.DUP12 => 0x8B
    case Opcode.DUP13 => 0x8C
    case Opcode.DUP14 => 0x8D
    case Opcode.DUP15 => 0x8E
    case Opcode.DUP16 => 0x8F
    case Opcode.SWAP1 => 0x90
    case Opcode.SWAP2 => 0x91
    case Opcode.SWAP3 => 0x92
    case Opcode.SWAP4 => 0x93
    case Opcode.SWAP5 => 0x94
    case Opcode.SWAP6 => 0x95
    case Opcode.SWAP7 => 0x96
    case Opcode.SWAP8 => 0x97
    case Opcode.SWAP9 => 0x98
    case Opcode.SWAP10 => 0x99
    case Opcode.SWAP11 => 0x9A
    case Opcode.SWAP12 => 0x9B
    case Opcode.SWAP13 => 0x9C
    case Opcode.SWAP14 => 0x9D
    case Opcode.SWAP15 => 0x9E
    case Opcode.SWAP16 => 0x9F
    case Opcode.LOG0 => 0xA0
    case Opcode.LOG1 => 0xA1
    case Opcode.LOG2 => 0xA2
    case Opcode.LOG3 => 0xA3
    case Opcode.LOG4 => 0xA4
    case Opcode.CREATE => 0xF0
    case Opcode.CALL => 0xF1
    case Opcode.CALLCODE => 0xF2
    case Opcode.RETURN => 0xF3
    case Opcode.DELEGATECALL => 0xF4
    case Opcode.CREATE2 => 0xF5
    case Opcode.STATICCALL => 0xFA
    case Opcode.REVERT => 0xFD
    case Opcode.INVALID => 0xFE
    case Opcode.SELFDESTRUCT => 0xFF

  // Decode a code byte to its opcode, or None for an undefined byte.
  def decode(b: BigInt): Option[Opcode] =
    if (b == BigInt(0x00)) Some(Opcode.STOP)
    else if (b == BigInt(0x01)) Some(Opcode.ADD)
    else if (b == BigInt(0x02)) Some(Opcode.MUL)
    else if (b == BigInt(0x03)) Some(Opcode.SUB)
    else if (b == BigInt(0x04)) Some(Opcode.DIV)
    else if (b == BigInt(0x05)) Some(Opcode.SDIV)
    else if (b == BigInt(0x06)) Some(Opcode.MOD)
    else if (b == BigInt(0x07)) Some(Opcode.SMOD)
    else if (b == BigInt(0x08)) Some(Opcode.ADDMOD)
    else if (b == BigInt(0x09)) Some(Opcode.MULMOD)
    else if (b == BigInt(0x0A)) Some(Opcode.EXP)
    else if (b == BigInt(0x0B)) Some(Opcode.SIGNEXTEND)
    else if (b == BigInt(0x10)) Some(Opcode.LT)
    else if (b == BigInt(0x11)) Some(Opcode.GT)
    else if (b == BigInt(0x12)) Some(Opcode.SLT)
    else if (b == BigInt(0x13)) Some(Opcode.SGT)
    else if (b == BigInt(0x14)) Some(Opcode.EQ)
    else if (b == BigInt(0x15)) Some(Opcode.ISZERO)
    else if (b == BigInt(0x16)) Some(Opcode.AND)
    else if (b == BigInt(0x17)) Some(Opcode.OR)
    else if (b == BigInt(0x18)) Some(Opcode.XOR)
    else if (b == BigInt(0x19)) Some(Opcode.NOT)
    else if (b == BigInt(0x1A)) Some(Opcode.BYTE)
    else if (b == BigInt(0x1B)) Some(Opcode.SHL)
    else if (b == BigInt(0x1C)) Some(Opcode.SHR)
    else if (b == BigInt(0x1D)) Some(Opcode.SAR)
    else if (b == BigInt(0x1E)) Some(Opcode.CLZ)
    else if (b == BigInt(0x20)) Some(Opcode.KECCAK256)
    else if (b == BigInt(0x30)) Some(Opcode.ADDRESS)
    else if (b == BigInt(0x31)) Some(Opcode.BALANCE)
    else if (b == BigInt(0x32)) Some(Opcode.ORIGIN)
    else if (b == BigInt(0x33)) Some(Opcode.CALLER)
    else if (b == BigInt(0x34)) Some(Opcode.CALLVALUE)
    else if (b == BigInt(0x35)) Some(Opcode.CALLDATALOAD)
    else if (b == BigInt(0x36)) Some(Opcode.CALLDATASIZE)
    else if (b == BigInt(0x37)) Some(Opcode.CALLDATACOPY)
    else if (b == BigInt(0x38)) Some(Opcode.CODESIZE)
    else if (b == BigInt(0x39)) Some(Opcode.CODECOPY)
    else if (b == BigInt(0x3A)) Some(Opcode.GASPRICE)
    else if (b == BigInt(0x3B)) Some(Opcode.EXTCODESIZE)
    else if (b == BigInt(0x3C)) Some(Opcode.EXTCODECOPY)
    else if (b == BigInt(0x3D)) Some(Opcode.RETURNDATASIZE)
    else if (b == BigInt(0x3E)) Some(Opcode.RETURNDATACOPY)
    else if (b == BigInt(0x3F)) Some(Opcode.EXTCODEHASH)
    else if (b == BigInt(0x40)) Some(Opcode.BLOCKHASH)
    else if (b == BigInt(0x41)) Some(Opcode.COINBASE)
    else if (b == BigInt(0x42)) Some(Opcode.TIMESTAMP)
    else if (b == BigInt(0x43)) Some(Opcode.NUMBER)
    else if (b == BigInt(0x44)) Some(Opcode.PREVRANDAO)
    else if (b == BigInt(0x45)) Some(Opcode.GASLIMIT)
    else if (b == BigInt(0x46)) Some(Opcode.CHAINID)
    else if (b == BigInt(0x47)) Some(Opcode.SELFBALANCE)
    else if (b == BigInt(0x48)) Some(Opcode.BASEFEE)
    else if (b == BigInt(0x49)) Some(Opcode.BLOBHASH)
    else if (b == BigInt(0x4A)) Some(Opcode.BLOBBASEFEE)
    else if (b == BigInt(0x50)) Some(Opcode.POP)
    else if (b == BigInt(0x51)) Some(Opcode.MLOAD)
    else if (b == BigInt(0x52)) Some(Opcode.MSTORE)
    else if (b == BigInt(0x53)) Some(Opcode.MSTORE8)
    else if (b == BigInt(0x54)) Some(Opcode.SLOAD)
    else if (b == BigInt(0x55)) Some(Opcode.SSTORE)
    else if (b == BigInt(0x56)) Some(Opcode.JUMP)
    else if (b == BigInt(0x57)) Some(Opcode.JUMPI)
    else if (b == BigInt(0x58)) Some(Opcode.PC)
    else if (b == BigInt(0x59)) Some(Opcode.MSIZE)
    else if (b == BigInt(0x5A)) Some(Opcode.GAS)
    else if (b == BigInt(0x5B)) Some(Opcode.JUMPDEST)
    else if (b == BigInt(0x5C)) Some(Opcode.TLOAD)
    else if (b == BigInt(0x5D)) Some(Opcode.TSTORE)
    else if (b == BigInt(0x5E)) Some(Opcode.MCOPY)
    else if (b == BigInt(0x5F)) Some(Opcode.PUSH0)
    else if (b == BigInt(0x60)) Some(Opcode.PUSH1)
    else if (b == BigInt(0x61)) Some(Opcode.PUSH2)
    else if (b == BigInt(0x62)) Some(Opcode.PUSH3)
    else if (b == BigInt(0x63)) Some(Opcode.PUSH4)
    else if (b == BigInt(0x64)) Some(Opcode.PUSH5)
    else if (b == BigInt(0x65)) Some(Opcode.PUSH6)
    else if (b == BigInt(0x66)) Some(Opcode.PUSH7)
    else if (b == BigInt(0x67)) Some(Opcode.PUSH8)
    else if (b == BigInt(0x68)) Some(Opcode.PUSH9)
    else if (b == BigInt(0x69)) Some(Opcode.PUSH10)
    else if (b == BigInt(0x6A)) Some(Opcode.PUSH11)
    else if (b == BigInt(0x6B)) Some(Opcode.PUSH12)
    else if (b == BigInt(0x6C)) Some(Opcode.PUSH13)
    else if (b == BigInt(0x6D)) Some(Opcode.PUSH14)
    else if (b == BigInt(0x6E)) Some(Opcode.PUSH15)
    else if (b == BigInt(0x6F)) Some(Opcode.PUSH16)
    else if (b == BigInt(0x70)) Some(Opcode.PUSH17)
    else if (b == BigInt(0x71)) Some(Opcode.PUSH18)
    else if (b == BigInt(0x72)) Some(Opcode.PUSH19)
    else if (b == BigInt(0x73)) Some(Opcode.PUSH20)
    else if (b == BigInt(0x74)) Some(Opcode.PUSH21)
    else if (b == BigInt(0x75)) Some(Opcode.PUSH22)
    else if (b == BigInt(0x76)) Some(Opcode.PUSH23)
    else if (b == BigInt(0x77)) Some(Opcode.PUSH24)
    else if (b == BigInt(0x78)) Some(Opcode.PUSH25)
    else if (b == BigInt(0x79)) Some(Opcode.PUSH26)
    else if (b == BigInt(0x7A)) Some(Opcode.PUSH27)
    else if (b == BigInt(0x7B)) Some(Opcode.PUSH28)
    else if (b == BigInt(0x7C)) Some(Opcode.PUSH29)
    else if (b == BigInt(0x7D)) Some(Opcode.PUSH30)
    else if (b == BigInt(0x7E)) Some(Opcode.PUSH31)
    else if (b == BigInt(0x7F)) Some(Opcode.PUSH32)
    else if (b == BigInt(0x80)) Some(Opcode.DUP1)
    else if (b == BigInt(0x81)) Some(Opcode.DUP2)
    else if (b == BigInt(0x82)) Some(Opcode.DUP3)
    else if (b == BigInt(0x83)) Some(Opcode.DUP4)
    else if (b == BigInt(0x84)) Some(Opcode.DUP5)
    else if (b == BigInt(0x85)) Some(Opcode.DUP6)
    else if (b == BigInt(0x86)) Some(Opcode.DUP7)
    else if (b == BigInt(0x87)) Some(Opcode.DUP8)
    else if (b == BigInt(0x88)) Some(Opcode.DUP9)
    else if (b == BigInt(0x89)) Some(Opcode.DUP10)
    else if (b == BigInt(0x8A)) Some(Opcode.DUP11)
    else if (b == BigInt(0x8B)) Some(Opcode.DUP12)
    else if (b == BigInt(0x8C)) Some(Opcode.DUP13)
    else if (b == BigInt(0x8D)) Some(Opcode.DUP14)
    else if (b == BigInt(0x8E)) Some(Opcode.DUP15)
    else if (b == BigInt(0x8F)) Some(Opcode.DUP16)
    else if (b == BigInt(0x90)) Some(Opcode.SWAP1)
    else if (b == BigInt(0x91)) Some(Opcode.SWAP2)
    else if (b == BigInt(0x92)) Some(Opcode.SWAP3)
    else if (b == BigInt(0x93)) Some(Opcode.SWAP4)
    else if (b == BigInt(0x94)) Some(Opcode.SWAP5)
    else if (b == BigInt(0x95)) Some(Opcode.SWAP6)
    else if (b == BigInt(0x96)) Some(Opcode.SWAP7)
    else if (b == BigInt(0x97)) Some(Opcode.SWAP8)
    else if (b == BigInt(0x98)) Some(Opcode.SWAP9)
    else if (b == BigInt(0x99)) Some(Opcode.SWAP10)
    else if (b == BigInt(0x9A)) Some(Opcode.SWAP11)
    else if (b == BigInt(0x9B)) Some(Opcode.SWAP12)
    else if (b == BigInt(0x9C)) Some(Opcode.SWAP13)
    else if (b == BigInt(0x9D)) Some(Opcode.SWAP14)
    else if (b == BigInt(0x9E)) Some(Opcode.SWAP15)
    else if (b == BigInt(0x9F)) Some(Opcode.SWAP16)
    else if (b == BigInt(0xA0)) Some(Opcode.LOG0)
    else if (b == BigInt(0xA1)) Some(Opcode.LOG1)
    else if (b == BigInt(0xA2)) Some(Opcode.LOG2)
    else if (b == BigInt(0xA3)) Some(Opcode.LOG3)
    else if (b == BigInt(0xA4)) Some(Opcode.LOG4)
    else if (b == BigInt(0xF0)) Some(Opcode.CREATE)
    else if (b == BigInt(0xF1)) Some(Opcode.CALL)
    else if (b == BigInt(0xF2)) Some(Opcode.CALLCODE)
    else if (b == BigInt(0xF3)) Some(Opcode.RETURN)
    else if (b == BigInt(0xF4)) Some(Opcode.DELEGATECALL)
    else if (b == BigInt(0xF5)) Some(Opcode.CREATE2)
    else if (b == BigInt(0xFA)) Some(Opcode.STATICCALL)
    else if (b == BigInt(0xFD)) Some(Opcode.REVERT)
    else if (b == BigInt(0xFE)) Some(Opcode.INVALID)
    else if (b == BigInt(0xFF)) Some(Opcode.SELFDESTRUCT)
    else None()


  // Static base cost of an opcode. Dynamic costs (memory expansion, cold/warm
  // access, copy words, refunds) are added on top by the interpreter.
  def baseGas(op: Opcode): BigInt = { op match
    case Opcode.STOP => BigInt(0)
    case Opcode.ADD => BigInt(3)
    case Opcode.MUL => BigInt(5)
    case Opcode.SUB => BigInt(3)
    case Opcode.DIV => BigInt(5)
    case Opcode.SDIV => BigInt(5)
    case Opcode.MOD => BigInt(5)
    case Opcode.SMOD => BigInt(5)
    case Opcode.ADDMOD => BigInt(8)
    case Opcode.MULMOD => BigInt(8)
    case Opcode.EXP => BigInt(10)
    case Opcode.SIGNEXTEND => BigInt(5)
    case Opcode.LT => BigInt(3)
    case Opcode.GT => BigInt(3)
    case Opcode.SLT => BigInt(3)
    case Opcode.SGT => BigInt(3)
    case Opcode.EQ => BigInt(3)
    case Opcode.ISZERO => BigInt(3)
    case Opcode.AND => BigInt(3)
    case Opcode.OR => BigInt(3)
    case Opcode.XOR => BigInt(3)
    case Opcode.NOT => BigInt(3)
    case Opcode.BYTE => BigInt(3)
    case Opcode.SHL => BigInt(3)
    case Opcode.SHR => BigInt(3)
    case Opcode.SAR => BigInt(3)
    case Opcode.CLZ => BigInt(5)
    case Opcode.KECCAK256 => BigInt(30)
    case Opcode.ADDRESS => BigInt(2)
    case Opcode.BALANCE => BigInt(100)
    case Opcode.ORIGIN => BigInt(2)
    case Opcode.CALLER => BigInt(2)
    case Opcode.CALLVALUE => BigInt(2)
    case Opcode.CALLDATALOAD => BigInt(3)
    case Opcode.CALLDATASIZE => BigInt(2)
    case Opcode.CALLDATACOPY => BigInt(3)
    case Opcode.CODESIZE => BigInt(2)
    case Opcode.CODECOPY => BigInt(3)
    case Opcode.GASPRICE => BigInt(2)
    case Opcode.EXTCODESIZE => BigInt(100)
    case Opcode.EXTCODECOPY => BigInt(100)
    case Opcode.RETURNDATASIZE => BigInt(2)
    case Opcode.RETURNDATACOPY => BigInt(3)
    case Opcode.EXTCODEHASH => BigInt(100)
    case Opcode.BLOCKHASH => BigInt(20)
    case Opcode.COINBASE => BigInt(2)
    case Opcode.TIMESTAMP => BigInt(2)
    case Opcode.NUMBER => BigInt(2)
    case Opcode.PREVRANDAO => BigInt(2)
    case Opcode.GASLIMIT => BigInt(2)
    case Opcode.CHAINID => BigInt(2)
    case Opcode.SELFBALANCE => BigInt(5)
    case Opcode.BASEFEE => BigInt(2)
    case Opcode.BLOBHASH => BigInt(3)
    case Opcode.BLOBBASEFEE => BigInt(2)
    case Opcode.POP => BigInt(2)
    case Opcode.MLOAD => BigInt(3)
    case Opcode.MSTORE => BigInt(3)
    case Opcode.MSTORE8 => BigInt(3)
    case Opcode.SLOAD => BigInt(100)
    case Opcode.SSTORE => BigInt(100)
    case Opcode.JUMP => BigInt(8)
    case Opcode.JUMPI => BigInt(10)
    case Opcode.PC => BigInt(2)
    case Opcode.MSIZE => BigInt(2)
    case Opcode.GAS => BigInt(2)
    case Opcode.JUMPDEST => BigInt(1)
    case Opcode.TLOAD => BigInt(100)
    case Opcode.TSTORE => BigInt(100)
    case Opcode.MCOPY => BigInt(3)
    case Opcode.PUSH0 => BigInt(2)
    case Opcode.PUSH1 => BigInt(3)
    case Opcode.PUSH2 => BigInt(3)
    case Opcode.PUSH3 => BigInt(3)
    case Opcode.PUSH4 => BigInt(3)
    case Opcode.PUSH5 => BigInt(3)
    case Opcode.PUSH6 => BigInt(3)
    case Opcode.PUSH7 => BigInt(3)
    case Opcode.PUSH8 => BigInt(3)
    case Opcode.PUSH9 => BigInt(3)
    case Opcode.PUSH10 => BigInt(3)
    case Opcode.PUSH11 => BigInt(3)
    case Opcode.PUSH12 => BigInt(3)
    case Opcode.PUSH13 => BigInt(3)
    case Opcode.PUSH14 => BigInt(3)
    case Opcode.PUSH15 => BigInt(3)
    case Opcode.PUSH16 => BigInt(3)
    case Opcode.PUSH17 => BigInt(3)
    case Opcode.PUSH18 => BigInt(3)
    case Opcode.PUSH19 => BigInt(3)
    case Opcode.PUSH20 => BigInt(3)
    case Opcode.PUSH21 => BigInt(3)
    case Opcode.PUSH22 => BigInt(3)
    case Opcode.PUSH23 => BigInt(3)
    case Opcode.PUSH24 => BigInt(3)
    case Opcode.PUSH25 => BigInt(3)
    case Opcode.PUSH26 => BigInt(3)
    case Opcode.PUSH27 => BigInt(3)
    case Opcode.PUSH28 => BigInt(3)
    case Opcode.PUSH29 => BigInt(3)
    case Opcode.PUSH30 => BigInt(3)
    case Opcode.PUSH31 => BigInt(3)
    case Opcode.PUSH32 => BigInt(3)
    case Opcode.DUP1 => BigInt(3)
    case Opcode.DUP2 => BigInt(3)
    case Opcode.DUP3 => BigInt(3)
    case Opcode.DUP4 => BigInt(3)
    case Opcode.DUP5 => BigInt(3)
    case Opcode.DUP6 => BigInt(3)
    case Opcode.DUP7 => BigInt(3)
    case Opcode.DUP8 => BigInt(3)
    case Opcode.DUP9 => BigInt(3)
    case Opcode.DUP10 => BigInt(3)
    case Opcode.DUP11 => BigInt(3)
    case Opcode.DUP12 => BigInt(3)
    case Opcode.DUP13 => BigInt(3)
    case Opcode.DUP14 => BigInt(3)
    case Opcode.DUP15 => BigInt(3)
    case Opcode.DUP16 => BigInt(3)
    case Opcode.SWAP1 => BigInt(3)
    case Opcode.SWAP2 => BigInt(3)
    case Opcode.SWAP3 => BigInt(3)
    case Opcode.SWAP4 => BigInt(3)
    case Opcode.SWAP5 => BigInt(3)
    case Opcode.SWAP6 => BigInt(3)
    case Opcode.SWAP7 => BigInt(3)
    case Opcode.SWAP8 => BigInt(3)
    case Opcode.SWAP9 => BigInt(3)
    case Opcode.SWAP10 => BigInt(3)
    case Opcode.SWAP11 => BigInt(3)
    case Opcode.SWAP12 => BigInt(3)
    case Opcode.SWAP13 => BigInt(3)
    case Opcode.SWAP14 => BigInt(3)
    case Opcode.SWAP15 => BigInt(3)
    case Opcode.SWAP16 => BigInt(3)
    case Opcode.LOG0 => BigInt(375)
    case Opcode.LOG1 => BigInt(750)
    case Opcode.LOG2 => BigInt(1125)
    case Opcode.LOG3 => BigInt(1500)
    case Opcode.LOG4 => BigInt(1875)
    case Opcode.CREATE => BigInt(32000)
    case Opcode.CALL => BigInt(100)
    case Opcode.CALLCODE => BigInt(100)
    case Opcode.RETURN => BigInt(0)
    case Opcode.DELEGATECALL => BigInt(100)
    case Opcode.CREATE2 => BigInt(32000)
    case Opcode.STATICCALL => BigInt(100)
    case Opcode.REVERT => BigInt(0)
    case Opcode.INVALID => BigInt(0)
    case Opcode.SELFDESTRUCT => BigInt(5000)
  }.ensuring(g => g >= 0)

  // Immediate width in bytes: PUSHn carries n inline bytes (0 for PUSH0), which
  // the pc skips over. Every non-push opcode is 0. Used by JUMPDEST analysis and
  // pc advancement so immediates are never mistaken for opcodes.
  def pushWidth(op: Opcode): BigInt = {
    op match
      case Opcode.PUSH1 => BigInt(1)
      case Opcode.PUSH2 => BigInt(2)
      case Opcode.PUSH3 => BigInt(3)
      case Opcode.PUSH4 => BigInt(4)
      case Opcode.PUSH5 => BigInt(5)
      case Opcode.PUSH6 => BigInt(6)
      case Opcode.PUSH7 => BigInt(7)
      case Opcode.PUSH8 => BigInt(8)
      case Opcode.PUSH9 => BigInt(9)
      case Opcode.PUSH10 => BigInt(10)
      case Opcode.PUSH11 => BigInt(11)
      case Opcode.PUSH12 => BigInt(12)
      case Opcode.PUSH13 => BigInt(13)
      case Opcode.PUSH14 => BigInt(14)
      case Opcode.PUSH15 => BigInt(15)
      case Opcode.PUSH16 => BigInt(16)
      case Opcode.PUSH17 => BigInt(17)
      case Opcode.PUSH18 => BigInt(18)
      case Opcode.PUSH19 => BigInt(19)
      case Opcode.PUSH20 => BigInt(20)
      case Opcode.PUSH21 => BigInt(21)
      case Opcode.PUSH22 => BigInt(22)
      case Opcode.PUSH23 => BigInt(23)
      case Opcode.PUSH24 => BigInt(24)
      case Opcode.PUSH25 => BigInt(25)
      case Opcode.PUSH26 => BigInt(26)
      case Opcode.PUSH27 => BigInt(27)
      case Opcode.PUSH28 => BigInt(28)
      case Opcode.PUSH29 => BigInt(29)
      case Opcode.PUSH30 => BigInt(30)
      case Opcode.PUSH31 => BigInt(31)
      case Opcode.PUSH32 => BigInt(32)
      case _ => BigInt(0)
  }.ensuring(w => 0 <= w && w <= 32)
