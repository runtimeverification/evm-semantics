requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
requires "lemmas/infinite-gas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports INFINITE-GAS
    imports EVM-OPTIMIZATIONS
endmodule

module LONG-PARSE-TIME-SPEC
    imports VERIFICATION

    claim [GEN-0-TO-MAX1000]: <kevm>
           <k>
             ( #execute => #next [ PUSH(1) ] )
             ...
           </k>
           <exit-code>
             ( _EXIT_CODE_CELL => ?_EXIT_CODE_CELL_0ce62d36 )
           </exit-code>
           <mode>
             ( NORMAL => ?_MODE_CELL_0ce62d36 )
           </mode>
           <schedule>
             ( ISTANBUL => ?_SCHEDULE_CELL_0ce62d36 )
           </schedule>
           <ethereum>
             <evm>
               <output>
                 ( _OUTPUT_CELL => ?_OUTPUT_CELL_0ce62d36 )
               </output>
               <statusCode>
                 ( _STATUSCODE_CELL => .StatusCode )
               </statusCode>
               <endPC>
                 ( _ENDPC_CELL => ?_ENDPC_CELL_0ce62d36 )
               </endPC>
               <callStack>
                 ( _CALLSTACK_CELL => ?_CALLSTACK_CELL_0ce62d36 )
               </callStack>
               <interimStates>
                 ( _INTERIMSTATES_CELL => ?_INTERIMSTATES_CELL_0ce62d36 )
               </interimStates>
               <touchedAccounts>
                 ( _TOUCHEDACCOUNTS_CELL => ?_TOUCHEDACCOUNTS_CELL_0ce62d36 )
               </touchedAccounts>
               <callState>
                 <program>
                   ( BYTES_32d123e7 => ?_PROGRAM_CELL_0ce62d36 )
                 </program>
                 <jumpDests>
                   ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( ( SetItem( 16 ) SetItem( 43 ) ) SetItem( 48 ) ) SetItem( 69 ) ) SetItem( 74 ) ) SetItem( 87 ) ) SetItem( 96 ) ) SetItem( 124 ) ) SetItem( 133 ) ) SetItem( 138 ) ) SetItem( 143 ) ) SetItem( 148 ) ) SetItem( 158 ) ) SetItem( 167 ) ) SetItem( 178 ) ) SetItem( 181 ) ) SetItem( 196 ) ) SetItem( 202 ) ) SetItem( 223 ) ) SetItem( 224 ) ) SetItem( 238 ) ) SetItem( 247 ) ) SetItem( 256 ) ) SetItem( 262 ) ) SetItem( 283 ) ) SetItem( 321 ) ) => ?_JUMPDESTS_CELL_0ce62d36 )
                 </jumpDests>
                 <id>
                   ( ACCT_ID => ?_ID_CELL_0ce62d36 )
                 </id>
                 <caller>
                   ( CALLER_ID => ?_CALLER_CELL_0ce62d36 )
                 </caller>
                 <callData>
                   ( _CALLDATA_CELL => ?_CALLDATA_CELL_0ce62d36 )
                 </callData>
                 <callValue>
                   ( _CALLVALUE_CELL => ?_CALLVALUE_CELL_0ce62d36 )
                 </callValue>
                 <wordStack>
                   ( .WordStack => ?_WORDSTACK_CELL_0ce62d36 )
                 </wordStack>
                 <localMem>
                   ( _LOCALMEM_CELL => ?_LOCALMEM_CELL_0ce62d36 )
                 </localMem>
                 <pc>
                   ( 0 => ?_PC_CELL_0ce62d36 )
                 </pc>
                 <gas>
                   ( #gas( _GAS_CELL ) => ?_GAS_CELL_0ce62d36 )
                 </gas>
                 <memoryUsed>
                   ( MEMORYUSED_CELL => ?_MEMORYUSED_CELL_0ce62d36 )
                 </memoryUsed>
                 <callGas>
                   ( _CALLGAS_CELL => ?_CALLGAS_CELL_0ce62d36 )
                 </callGas>
                 <static>
                   ( _STATIC_CELL => ?_STATIC_CELL_0ce62d36 )
                 </static>
                 <callDepth>
                   ( _CALLDEPTH_CELL => ?_CALLDEPTH_CELL_0ce62d36 )
                 </callDepth>
               </callState>
               <substate>
                 <selfDestruct>
                   ( _SELFDESTRUCT_CELL => ?_SELFDESTRUCT_CELL_0ce62d36 )
                 </selfDestruct>
                 <log>
                   ( _LOG_CELL => ?_LOG_CELL_0ce62d36 )
                 </log>
                 <refund>
                   ( _REFUND_CELL => ?_REFUND_CELL_0ce62d36 )
                 </refund>
                 <accessedAccounts>
                   ( _ACCESSEDACCOUNTS_CELL => ?_ACCESSEDACCOUNTS_CELL_0ce62d36 )
                 </accessedAccounts>
                 <accessedStorage>
                   ( _ACCESSEDSTORAGE_CELL => ?_ACCESSEDSTORAGE_CELL_0ce62d36 )
                 </accessedStorage>
               </substate>
               <gasPrice>
                 ( _GASPRICE_CELL => ?_GASPRICE_CELL_0ce62d36 )
               </gasPrice>
               <origin>
                 ( _ORIGIN_CELL => ?_ORIGIN_CELL_0ce62d36 )
               </origin>
               <blockhashes>
                 ( _BLOCKHASHES_CELL => ?_BLOCKHASHES_CELL_0ce62d36 )
               </blockhashes>
               <block>
                 <previousHash>
                   ( _PREVIOUSHASH_CELL => ?_PREVIOUSHASH_CELL_0ce62d36 )
                 </previousHash>
                 <ommersHash>
                   ( _OMMERSHASH_CELL => ?_OMMERSHASH_CELL_0ce62d36 )
                 </ommersHash>
                 <coinbase>
                   ( _COINBASE_CELL => ?_COINBASE_CELL_0ce62d36 )
                 </coinbase>
                 <stateRoot>
                   ( _STATEROOT_CELL => ?_STATEROOT_CELL_0ce62d36 )
                 </stateRoot>
                 <transactionsRoot>
                   ( _TRANSACTIONSROOT_CELL => ?_TRANSACTIONSROOT_CELL_0ce62d36 )
                 </transactionsRoot>
                 <receiptsRoot>
                   ( _RECEIPTSROOT_CELL => ?_RECEIPTSROOT_CELL_0ce62d36 )
                 </receiptsRoot>
                 <logsBloom>
                   ( _LOGSBLOOM_CELL => ?_LOGSBLOOM_CELL_0ce62d36 )
                 </logsBloom>
                 <difficulty>
                   ( _DIFFICULTY_CELL => ?_DIFFICULTY_CELL_0ce62d36 )
                 </difficulty>
                 <number>
                   ( _NUMBER_CELL => ?_NUMBER_CELL_0ce62d36 )
                 </number>
                 <gasLimit>
                   ( _GASLIMIT_CELL => ?_GASLIMIT_CELL_0ce62d36 )
                 </gasLimit>
                 <gasUsed>
                   ( _GASUSED_CELL => ?_GASUSED_CELL_0ce62d36 )
                 </gasUsed>
                 <timestamp>
                   ( _TIMESTAMP_CELL => ?_TIMESTAMP_CELL_0ce62d36 )
                 </timestamp>
                 <extraData>
                   ( _EXTRADATA_CELL => ?_EXTRADATA_CELL_0ce62d36 )
                 </extraData>
                 <mixHash>
                   ( _MIXHASH_CELL => ?_MIXHASH_CELL_0ce62d36 )
                 </mixHash>
                 <blockNonce>
                   ( _BLOCKNONCE_CELL => ?_BLOCKNONCE_CELL_0ce62d36 )
                 </blockNonce>
                 <ommerBlockHeaders>
                   ( _OMMERBLOCKHEADERS_CELL => ?_OMMERBLOCKHEADERS_CELL_0ce62d36 )
                 </ommerBlockHeaders>
               </block>
             </evm>
             <network>
               <chainID>
                 ( _CHAINID_CELL => ?_CHAINID_CELL_0ce62d36 )
               </chainID>
               <activeAccounts>
                 ( _ACTIVEACCOUNTS_CELL => ?_ACTIVEACCOUNTS_CELL_0ce62d36 )
               </activeAccounts>
               <accounts>
                 ( ( <account>
                   <acctID>
                     ACCT_ID
                   </acctID>
                   <balance>
                     ACCT_BALANCE
                   </balance>
                   <code>
                     _ACCT_CODE
                   </code>
                   <storage>
                     _ACCT_STORAGE
                   </storage>
                   <origStorage>
                     _ACCT_ORIGSTORAGE
                   </origStorage>
                   <nonce>
                     ACCT_NONCE
                   </nonce>
                 </account>
                 _ACCOUNTS ) => ?_ACCOUNTS_CELL_0ce62d36 )
               </accounts>
               <txOrder>
                 ( _TXORDER_CELL => ?_TXORDER_CELL_0ce62d36 )
               </txOrder>
               <txPending>
                 ( _TXPENDING_CELL => ?_TXPENDING_CELL_0ce62d36 )
               </txPending>
               <messages>
                 ( _MESSAGES_CELL => ?_MESSAGES_CELL_0ce62d36 )
               </messages>
             </network>
           </ethereum>
         </kevm>
      requires #rangeAddress( ACCT_ID )
       andBool #rangeAddress( CALLER_ID )
       andBool #rangeUInt( 256 , ACCT_BALANCE )
       andBool #rangeUInt( 256 , ACCT_NONCE )
       andBool BYTES_32d123e7 ==K String2Bytes( "`\x80`@R4\x80\x15a\x00\x10W`\x00\x80\xfd[P`\x046\x10a\x00+W`\x005`\xe0\x1c\x80c\xf8\xca\xc3B\x14a\x000W[`\x00\x80\xfd[a\x00J`\x04\x806\x03\x81\x01\x90a\x00E\x91\x90a\x00\xcaV[a\x00`V[`@Qa\x00W\x91\x90a\x01\x06V[`@Q\x80\x91\x03\x90\xf3[`\x00`\n\x82\x10\x15a\x00\x85W\x81`\n\x11a\x00|W`\x00\x90Pa\x00\x8aV[`\x01\x90Pa\x00\x8aV[`\x02\x90P[\x91\x90PV[`\x00\x80\xfd[`\x00\x81\x90P\x91\x90PV[a\x00\xa7\x81a\x00\x94V[\x81\x14a\x00\xb2W`\x00\x80\xfd[PV[`\x00\x815\x90Pa\x00\xc4\x81a\x00\x9eV[\x92\x91PPV[`\x00` \x82\x84\x03\x12\x15a\x00\xe0Wa\x00\xdfa\x00\x8fV[[`\x00a\x00\xee\x84\x82\x85\x01a\x00\xb5V[\x91PP\x92\x91PPV[a\x01\x00\x81a\x00\x94V[\x82RPPV[`\x00` \x82\x01\x90Pa\x01\x1b`\x00\x83\x01\x84a\x00\xf7V[\x92\x91PPV\xfe\xa2dipfsX\"\x12 \x9a0:oN7\xbf-\xe3\xf9\xed|\x83E~\x02\xc37\x99^\xd6[D\f\xd3:{\xeb\x1d_n!dsolcx(0.8.10-develop.2021.12.2+commit.fc410830\x00Y" )
       andBool #rangeUInt( 256 , MEMORYUSED_CELL )

      [label(GEN-0-TO-MAX1000)]
endmodule

