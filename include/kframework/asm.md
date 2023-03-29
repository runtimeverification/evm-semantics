Ethereum Assembler
==================

This file contains an assembler from EVM opcodes to byte strings.

Note that due to the design of EVM, which depends on the binary representation of a smart contract, it is **not** the case that disassembling and then reassembling the same contract will yield the same sequence of bytes.
As a simple counterexample, consider the contract `0x60`.
Disassembling and then reassembling this contract will yield `0x6000`.

As such, assembly is not considered part of the semantics of EVM, but is provided merely as a sample implementation to ease readability and make it easier to write inputs to the KEVM semantics.

```k
module EVM-ASSEMBLY
    imports EVM

    syntax OpCode ::= PUSH(Int, Int) [klabel(PUSHAsm)]
 // --------------------------------------------------
```

### Program Structure

Cons-lists of opcodes form programs (using cons operator `_;_`).
Operator `#revOps` can be used to reverse a program.

```k
    syntax OpCodes ::= ".OpCodes" | OpCode ";" OpCodes
 // --------------------------------------------------

    syntax OpCodes ::= #revOps    ( OpCodes )           [function]
                     | #revOpsAux ( OpCodes , OpCodes ) [function]
 // --------------------------------------------------------------
    rule #revOps(OPS) => #revOpsAux(OPS, .OpCodes)

    rule #revOpsAux( .OpCodes , OPS' ) => OPS'
    rule #revOpsAux( OP ; OPS , OPS' ) => #revOpsAux( OPS , OP ; OPS' )
```

```k
    syntax Bytes ::= #asmOpCodes ( OpCodes ) [function]
 // ---------------------------------------------------
```

```k
    syntax Bytes ::= #asmOpCodes ( OpCodes, StringBuffer ) [function, klabel(#asmOpCodesAux)]
 // -----------------------------------------------------------------------------------------
    rule #asmOpCodes( OPS ) => #asmOpCodes(OPS, .StringBuffer)

    rule #asmOpCodes( PUSH(N, W) ; OCS, SB ) => #asmOpCodes(OCS, (SB +String chrChar(#asmOpCode(PUSH(N)))) +String Bytes2String(Int2Bytes(N, W, BE)))
    rule #asmOpCodes( OP ; OCS, SB ) => #asmOpCodes(OCS, SB +String chrChar(#asmOpCode(OP))) [owise]
    rule #asmOpCodes( .OpCodes, SB ) => String2Bytes(StringBuffer2String(SB))
```

```k
    syntax Int ::= #asmOpCode ( OpCode ) [function]
 // -----------------------------------------------
    rule #asmOpCode( STOP           ) =>   0
    rule #asmOpCode( ADD            ) =>   1
    rule #asmOpCode( MUL            ) =>   2
    rule #asmOpCode( SUB            ) =>   3
    rule #asmOpCode( DIV            ) =>   4
    rule #asmOpCode( SDIV           ) =>   5
    rule #asmOpCode( MOD            ) =>   6
    rule #asmOpCode( SMOD           ) =>   7
    rule #asmOpCode( ADDMOD         ) =>   8
    rule #asmOpCode( MULMOD         ) =>   9
    rule #asmOpCode( EXP            ) =>  10
    rule #asmOpCode( SIGNEXTEND     ) =>  11
    rule #asmOpCode( LT             ) =>  16
    rule #asmOpCode( GT             ) =>  17
    rule #asmOpCode( SLT            ) =>  18
    rule #asmOpCode( SGT            ) =>  19
    rule #asmOpCode( EQ             ) =>  20
    rule #asmOpCode( ISZERO         ) =>  21
    rule #asmOpCode( AND            ) =>  22
    rule #asmOpCode( EVMOR          ) =>  23
    rule #asmOpCode( XOR            ) =>  24
    rule #asmOpCode( NOT            ) =>  25
    rule #asmOpCode( BYTE           ) =>  26
    rule #asmOpCode( SHL            ) =>  27
    rule #asmOpCode( SHR            ) =>  28
    rule #asmOpCode( SAR            ) =>  29
    rule #asmOpCode( SHA3           ) =>  32
    rule #asmOpCode( ADDRESS        ) =>  48
    rule #asmOpCode( BALANCE        ) =>  49
    rule #asmOpCode( ORIGIN         ) =>  50
    rule #asmOpCode( CALLER         ) =>  51
    rule #asmOpCode( CALLVALUE      ) =>  52
    rule #asmOpCode( CALLDATALOAD   ) =>  53
    rule #asmOpCode( CALLDATASIZE   ) =>  54
    rule #asmOpCode( CALLDATACOPY   ) =>  55
    rule #asmOpCode( CODESIZE       ) =>  56
    rule #asmOpCode( CODECOPY       ) =>  57
    rule #asmOpCode( GASPRICE       ) =>  58
    rule #asmOpCode( EXTCODESIZE    ) =>  59
    rule #asmOpCode( EXTCODECOPY    ) =>  60
    rule #asmOpCode( RETURNDATASIZE ) =>  61
    rule #asmOpCode( RETURNDATACOPY ) =>  62
    rule #asmOpCode( EXTCODEHASH    ) =>  63
    rule #asmOpCode( BLOCKHASH      ) =>  64
    rule #asmOpCode( COINBASE       ) =>  65
    rule #asmOpCode( TIMESTAMP      ) =>  66
    rule #asmOpCode( NUMBER         ) =>  67
    rule #asmOpCode( DIFFICULTY     ) =>  68
    rule #asmOpCode( PREVRANDAO     ) =>  68
    rule #asmOpCode( GASLIMIT       ) =>  69
    rule #asmOpCode( CHAINID        ) =>  70
    rule #asmOpCode( SELFBALANCE    ) =>  71
    rule #asmOpCode( POP            ) =>  80
    rule #asmOpCode( MLOAD          ) =>  81
    rule #asmOpCode( MSTORE         ) =>  82
    rule #asmOpCode( MSTORE8        ) =>  83
    rule #asmOpCode( SLOAD          ) =>  84
    rule #asmOpCode( SSTORE         ) =>  85
    rule #asmOpCode( JUMP           ) =>  86
    rule #asmOpCode( JUMPI          ) =>  87
    rule #asmOpCode( PC             ) =>  88
    rule #asmOpCode( MSIZE          ) =>  89
    rule #asmOpCode( GAS            ) =>  90
    rule #asmOpCode( JUMPDEST       ) =>  91
    rule #asmOpCode( PUSH(1)        ) =>  96
    rule #asmOpCode( PUSH(2)        ) =>  97
    rule #asmOpCode( PUSH(3)        ) =>  98
    rule #asmOpCode( PUSH(4)        ) =>  99
    rule #asmOpCode( PUSH(5)        ) => 100
    rule #asmOpCode( PUSH(6)        ) => 101
    rule #asmOpCode( PUSH(7)        ) => 102
    rule #asmOpCode( PUSH(8)        ) => 103
    rule #asmOpCode( PUSH(9)        ) => 104
    rule #asmOpCode( PUSH(10)       ) => 105
    rule #asmOpCode( PUSH(11)       ) => 106
    rule #asmOpCode( PUSH(12)       ) => 107
    rule #asmOpCode( PUSH(13)       ) => 108
    rule #asmOpCode( PUSH(14)       ) => 109
    rule #asmOpCode( PUSH(15)       ) => 110
    rule #asmOpCode( PUSH(16)       ) => 111
    rule #asmOpCode( PUSH(17)       ) => 112
    rule #asmOpCode( PUSH(18)       ) => 113
    rule #asmOpCode( PUSH(19)       ) => 114
    rule #asmOpCode( PUSH(20)       ) => 115
    rule #asmOpCode( PUSH(21)       ) => 116
    rule #asmOpCode( PUSH(22)       ) => 117
    rule #asmOpCode( PUSH(23)       ) => 118
    rule #asmOpCode( PUSH(24)       ) => 119
    rule #asmOpCode( PUSH(25)       ) => 120
    rule #asmOpCode( PUSH(26)       ) => 121
    rule #asmOpCode( PUSH(27)       ) => 122
    rule #asmOpCode( PUSH(28)       ) => 123
    rule #asmOpCode( PUSH(29)       ) => 124
    rule #asmOpCode( PUSH(30)       ) => 125
    rule #asmOpCode( PUSH(31)       ) => 126
    rule #asmOpCode( PUSH(32)       ) => 127
    rule #asmOpCode( DUP(1)         ) => 128
    rule #asmOpCode( DUP(2)         ) => 129
    rule #asmOpCode( DUP(3)         ) => 130
    rule #asmOpCode( DUP(4)         ) => 131
    rule #asmOpCode( DUP(5)         ) => 132
    rule #asmOpCode( DUP(6)         ) => 133
    rule #asmOpCode( DUP(7)         ) => 134
    rule #asmOpCode( DUP(8)         ) => 135
    rule #asmOpCode( DUP(9)         ) => 136
    rule #asmOpCode( DUP(10)        ) => 137
    rule #asmOpCode( DUP(11)        ) => 138
    rule #asmOpCode( DUP(12)        ) => 139
    rule #asmOpCode( DUP(13)        ) => 140
    rule #asmOpCode( DUP(14)        ) => 141
    rule #asmOpCode( DUP(15)        ) => 142
    rule #asmOpCode( DUP(16)        ) => 143
    rule #asmOpCode( SWAP(1)        ) => 144
    rule #asmOpCode( SWAP(2)        ) => 145
    rule #asmOpCode( SWAP(3)        ) => 146
    rule #asmOpCode( SWAP(4)        ) => 147
    rule #asmOpCode( SWAP(5)        ) => 148
    rule #asmOpCode( SWAP(6)        ) => 149
    rule #asmOpCode( SWAP(7)        ) => 150
    rule #asmOpCode( SWAP(8)        ) => 151
    rule #asmOpCode( SWAP(9)        ) => 152
    rule #asmOpCode( SWAP(10)       ) => 153
    rule #asmOpCode( SWAP(11)       ) => 154
    rule #asmOpCode( SWAP(12)       ) => 155
    rule #asmOpCode( SWAP(13)       ) => 156
    rule #asmOpCode( SWAP(14)       ) => 157
    rule #asmOpCode( SWAP(15)       ) => 158
    rule #asmOpCode( SWAP(16)       ) => 159
    rule #asmOpCode( LOG(0)         ) => 160
    rule #asmOpCode( LOG(1)         ) => 161
    rule #asmOpCode( LOG(2)         ) => 162
    rule #asmOpCode( LOG(3)         ) => 163
    rule #asmOpCode( LOG(4)         ) => 164
    rule #asmOpCode( CREATE         ) => 240
    rule #asmOpCode( CALL           ) => 241
    rule #asmOpCode( CALLCODE       ) => 242
    rule #asmOpCode( RETURN         ) => 243
    rule #asmOpCode( DELEGATECALL   ) => 244
    rule #asmOpCode( CREATE2        ) => 245
    rule #asmOpCode( STATICCALL     ) => 250
    rule #asmOpCode( REVERT         ) => 253
    rule #asmOpCode( INVALID        ) => 254
    rule #asmOpCode( SELFDESTRUCT   ) => 255
    rule #asmOpCode( UNDEFINED(W)   ) =>   W

endmodule
```
