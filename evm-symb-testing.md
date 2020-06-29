Symbolic testing
====================

```k
requires "driver.md"
requires "edsl.md"

module EVM-SYMB-TESTING
    imports ETHEREUM-SIMULATION
    imports EDSL

    configuration
      <kevm-specs unused="true">
        <kevm/>
        <testerAcctId>   0          </testerAcctId>
        <testerBytecode> .ByteArray </testerBytecode>
        <erc20Bytecode>  .ByteArray </erc20Bytecode>
      </kevm-specs>

 // Basic framework
 // -------------------------------------------------------------

    syntax EthereumCommand ::= "#loadTesterBytecode"
                             | "#loadERC20Bytecode" Int
                             | "#loadBytecode" Int ByteArray
    rule <k> #loadTesterBytecode => #loadBytecode ?ACCT:Int CODE ...</k>
         <testerBytecode> CODE </testerBytecode>
         <testerAcctId> _ => ?ACCT </testerAcctId>

    rule <k> #loadERC20Bytecode ACCT => #loadBytecode ACCT CODE ...</k>
         <erc20Bytecode> CODE </erc20Bytecode>

    rule <k> #loadBytecode ACCT CODE => . ...</k>
         <schedule> SCHED </schedule>
         <activeAccounts> _:Set (.Set => SetItem(ACCT)) </activeAccounts>
         <accounts>
           ( .Bag
          => <account>
               <acctID> ACCT </acctID>
               <code> CODE </code>
               <storage> ?STORAGE </storage>
               <origStorage> ?STORAGE </origStorage>
               ...
             </account>
           )
           ...
         </accounts>
      ensures #rangeAddress(ACCT)
      andBool notBool ACCT in #precompiledAccounts(SCHED)

    syntax EthereumCommand ::= "#assume" Bool
 // ------------------------------------------------------------
    rule <k> #assume B => . ...</k>
      ensures B

    syntax EthereumCommand ::= "#runTestApprove"
                             | "#runTestApproveAux"
 // ------------------------------------------------------------
    rule <k> #runTestApprove => #loadTesterBytecode ~> #runTestApproveAux ~> #successOrRevert ...</k>
    rule <k> #runTestApproveAux => #mkCallShortcut TESTER_ACCT TESTER_ACCT #abiCallData("test_approve", .TypedArgs) ...</k>
         <testerAcctId> TESTER_ACCT </testerAcctId>

    //Shortcut for #mkCall and required setup
    syntax EthereumCommand ::= "#mkCallShortcut" Int Int ByteArray
    rule <k> #mkCallShortcut CALLER_ID ACCT_ID ARGS
          => #mkCall CALLER_ID ACCT_ID ACCT_ID PARSEDCODE 0 ARGS false
         ...
         </k>
        <acctID> ACCT_ID </acctID>
        <code> PARSEDCODE </code>

    syntax EthereumCommand ::= "#successOrRevert"
 // ------------------------------------------------------------
    rule <statusCode> STCODE </statusCode>
         <k> #halt ~> #successOrRevert => success ... </k>
      requires STCODE ==K EVMC_SUCCESS orBool STCODE ==K EVMC_REVERT 

    rule <statusCode> _:ExceptionalStatusCode </statusCode>
         <k> #halt ~> #successOrRevert => . ... </k>


 // Custom functions for symbolic testing
 // -------------------------------------------------------------

    //function new_ERC20_with_arbitrary_storage() external returns (ERC20)
    rule <k> CALL _ TESTER_ACCT 0 ARGSTART _ARGWIDTH RETSTART RETWIDTH
          //=> #assume notBool ?ACCT in ActiveAccts //Intended version. Doesn't work even after this fix: https://github.com/kframework/kore/issues/1183
          => #assume notBool ?ACCT in ActiveAccts
          ~> #loadERC20Bytecode ?ACCT
          ~> 1 ~> #push ~> #setLocalMem RETSTART RETWIDTH #buf(32, ?ACCT)
         ...
         </k>
         <output> _ => #buf(32, ?ACCT) </output>
         <localMem> LM </localMem>
         <testerAcctId> TESTER_ACCT </testerAcctId>
         <activeAccounts> ActiveAccts </activeAccounts>
      requires #range(LM, ARGSTART, 4) ==K #abiCallData("new_ERC20_with_arbitrary_storage", .TypedArgs)
      [priority(40)] //Higher than normal

    //function create_symbolic_address() external returns (address)
    rule <k> CALL _ TESTER_ACCT 0 ARGSTART _ARGWIDTH RETSTART RETWIDTH
          => #assume #rangeAddress(?ACCT:Int)
          ~> 1 ~> #push ~> #setLocalMem RETSTART RETWIDTH #buf(32, ?ACCT)
         ...
         </k>
         <output> _ => #buf(32, ?ACCT) </output>
         <localMem> LM </localMem>
         <testerAcctId> TESTER_ACCT </testerAcctId>
      requires #range(LM, ARGSTART, 4) ==K #abiCallData("create_symbolic_address", .TypedArgs)
      [priority(40)]

    //function create_symbolic_uint256() external returns (uint256)
    rule <k> CALL _ TESTER_ACCT 0 ARGSTART _ARGWIDTH RETSTART RETWIDTH
          => #assume #rangeUInt(256, ?SYMB_INT:Int)
          ~> 1 ~> #push ~> #setLocalMem RETSTART RETWIDTH #buf(32, ?SYMB_INT)
         ...
         </k>
         <output> _ => #buf(32, ?SYMB_INT) </output>
         <localMem> LM </localMem>
         <testerAcctId> TESTER_ACCT </testerAcctId>
      requires #range(LM, ARGSTART, 4) ==K #abiCallData("create_symbolic_uint256", .TypedArgs)
      [priority(40)]

    //function get_storage_at(address, uint256) external returns (uint256)
    //This version doesn't work because <acctID> LHS cannot be matched.
/*    rule <k> CALL _ TESTER_ACCT 0 ARGSTART ARGWIDTH RETSTART RETWIDTH
          => 1 ~> #push ~> #setLocalMem RETSTART RETWIDTH #buf(32, #lookup(STORAGE, #asWord(#range(LM, ARGSTART +Int 36, 32))))
         ...
         </k>
         <output> _ => #buf(32, #lookup(STORAGE, #asWord(#range(LM, ARGSTART +Int 36, 32)))) </output>
         <localMem> LM </localMem>
         <account>
           <acctID> #asWord(#range(LM, ARGSTART +Int 4, 32)) </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
         <testerAcctId> TESTER_ACCT </testerAcctId>
      requires #range(LM, ARGSTART, 4) ==K #signatureCallData("get_storage_at", #address(?_), #uint256(?_), .TypedArgs)
      [priority(40)]
*/

    rule <k> CALL _ TESTER_ACCT 0 ARGSTART _ARGWIDTH RETSTART RETWIDTH
          => #getStorageAt(#asWord(#range(LM, ARGSTART +Int 4, 32)), #asWord(#range(LM, ARGSTART +Int 36, 32)), RETSTART, RETWIDTH)
         ...
         </k>
         <localMem> LM </localMem>
         <testerAcctId> TESTER_ACCT </testerAcctId>
      requires #range(LM, ARGSTART, 4) ==K #signatureCallData("get_storage_at", #address(?_), #uint256(?_), .TypedArgs)
      [priority(40)]

    syntax KItem ::= #getStorageAt(Int, Int, Int, Int)
    rule <k> #getStorageAt(ADDR, LOC, RETSTART, RETWIDTH)
          => 1 ~> #push ~> #setLocalMem RETSTART RETWIDTH #buf(32, #lookup(STORAGE, LOC))
         ...
         </k>
         <output> _ => #buf(32, #lookup(STORAGE, LOC)) </output>
         <account>
           <acctID> ADDR </acctID>
           <storage> STORAGE </storage>
           ...
         </account>

    //function assume(bool) external
    rule <k> CALL _ TESTER_ACCT 0 ARGSTART _ARGWIDTH RETSTART RETWIDTH
              //argument value #buf(32, 1) means true
          => #assume #range(LM, ARGSTART +Int 4, 32) ==K #buf(32, 1)
          ~> 1 ~> #push ~> #setLocalMem RETSTART RETWIDTH #buf(32, 0)
         ...
         </k>
         <output> _ => #buf(32, 0) </output>
         <localMem> LM </localMem>
         <testerAcctId> TESTER_ACCT </testerAcctId>
      requires #range(LM, ARGSTART, 4) ==K #signatureCallData("assume", #bool(?_), .TypedArgs)
      [priority(40)]


 // Hacks of basic KEVM semantics
 // -------------------------------------------------------------

    //Hack to disable gas computation
    rule <k> #gas [ _OP , _AOP ] => . ...</k> [priority(40)]

    //Hack to disable <touchedAccounts> logic
    rule <k> #mkCall ACCTFROM ACCTTO ACCTCODE BYTES APPVALUE ARGS STATIC:Bool
          => #initVM ~> #precompiled?(ACCTCODE, SCHED) ~> #execute
         ...
         </k>
         <callDepth> CD => CD +Int 1 </callDepth>
         <callData> _ => ARGS </callData>
         <callValue> _ => APPVALUE </callValue>
         <id> _ => ACCTTO </id>
         <gas> _ => GCALL </gas>
         <callGas> GCALL => 0 </callGas>
         <caller> _ => ACCTFROM </caller>
         <program> _ => BYTES </program>
         <jumpDests> _ => #computeValidJumpDests(BYTES) </jumpDests>
         <static> OLDSTATIC:Bool => OLDSTATIC orBool STATIC </static>
         //todo symb-test workaround, Set operations limitations.
         //doesn't work as of 06/01/2020, function _Set_(?ACCT, ?ACCT) evaluates to bottom on step 5.
         //<touchedAccounts> ... .Set => SetItem(ACCTFROM) SetItem(ACCTTO) ... </touchedAccounts>
         <schedule> SCHED </schedule>
      [priority(40)]

endmodule
```
