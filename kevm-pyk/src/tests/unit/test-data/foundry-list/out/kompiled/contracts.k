requires "foundry.md"

module SCRIPT-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= ScriptContract
    
    syntax ScriptContract ::= "Script" [symbol(), klabel(contract_Script)]
    
    rule  ( #binRuntime ( Script ) => #parseByteStack ( "0x" ) )
      
    
    syntax Field ::= ScriptField
    
    syntax ScriptField ::= "IS_SCRIPT" [symbol(), klabel(field_Script_IS_SCRIPT)]
    
    rule  ( #loc ( Script . IS_SCRIPT ) => 0 )
      
    
    syntax Bytes ::= ScriptContract "." ScriptMethod [function(), symbol(), klabel(method_Script)]
    
    syntax ScriptMethod ::= "IS_SCRIPT" "(" ")" [symbol(), klabel(method_Script_IS_SCRIPT_)]
    
    syntax ScriptMethod ::= "vm" "(" ")" [symbol(), klabel(method_Script_vm_)]
    
    rule  ( Script . IS_SCRIPT ( ) => #abiCallData ( "IS_SCRIPT" , .TypedArgs ) )
      
    
    rule  ( Script . vm ( ) => #abiCallData ( "vm" , .TypedArgs ) )
      
    
    rule  ( selector ( "IS_SCRIPT()" ) => 4174167879 )
      
    
    rule  ( selector ( "vm()" ) => 980845667 )
      

endmodule

module ASSERTTEST-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= AssertTestContract
    
    syntax AssertTestContract ::= "AssertTest" [symbol(), klabel(contract_AssertTest)]
    
    rule  ( #binRuntime ( AssertTest ) => #parseByteStack ( "0x608060405234801561001057600080fd5b50600436106100935760003560e01c80635ddecbfd116100665780635ddecbfd146100d25780637aa9ccae146100d2578063ba414fa6146100da578063f8ccbf47146100f2578063fa7626d41461010557600080fd5b80630a9254e41461009857806318675d4214610098578063360da4d2146100985780633a7684631461009a575b600080fd5b005b6100b5737109709ecfa91a80626ff3989d68f67f5b1dd12d81565b6040516001600160a01b0390911681526020015b60405180910390f35b610098610114565b6100e261011c565b60405190151581526020016100c9565b6000546100e29062010000900460ff1681565b6000546100e29060ff1681565b565b610112610247565b60008054610100900460ff161561013c5750600054610100900460ff1690565b6000737109709ecfa91a80626ff3989d68f67f5b1dd12d3b156102425760408051737109709ecfa91a80626ff3989d68f67f5b1dd12d602082018190526519985a5b195960d21b828401528251808303840181526060830190935260009290916101ca917f667f9d70ca411d70ead50d8d5c22070dafc36ad75f3dcf5e7237b22ade9aecc491608001610298565b60408051601f19818403018152908290526101e4916102bc565b6000604051808303816000865af19150503d8060008114610221576040519150601f19603f3d011682016040523d82523d6000602084013e610226565b606091505b509150508080602001905181019061023e91906102cf565b9150505b919050565b634e487b7160e01b600052600160045260246000fd5b6000815160005b8181101561027e5760208185018101518683015201610264565b8181111561028d576000828601525b509290920192915050565b6001600160e01b03198316815260006102b4600483018461025d565b949350505050565b60006102c8828461025d565b9392505050565b6000602082840312156102e157600080fd5b815180151581146102c857600080fdfea264697066735822122078ea62940a85bea935ede718a69828832fdeb95b944ce2c3cd542711dab96ab964736f6c634300080d0033" ) )
      
    
    syntax Field ::= AssertTestField
    
    syntax AssertTestField ::= "IS_TEST" [symbol(), klabel(field_AssertTest_IS_TEST)]
    
    syntax AssertTestField ::= "_failed" [symbol(), klabel(field_AssertTest__failed)]
    
    syntax AssertTestField ::= "IS_SCRIPT" [symbol(), klabel(field_AssertTest_IS_SCRIPT)]
    
    syntax AssertTestField ::= "stdstore" [symbol(), klabel(field_AssertTest_stdstore)]
    
    rule  ( #loc ( AssertTest . IS_TEST ) => 0 )
      
    
    rule  ( #loc ( AssertTest . _failed ) => 0 )
      
    
    rule  ( #loc ( AssertTest . IS_SCRIPT ) => 0 )
      
    
    rule  ( #loc ( AssertTest . stdstore ) => 1 )
      
    
    syntax Bytes ::= AssertTestContract "." AssertTestMethod [function(), symbol(), klabel(method_AssertTest)]
    
    syntax AssertTestMethod ::= "IS_SCRIPT" "(" ")" [symbol(), klabel(method_AssertTest_IS_SCRIPT_)]
    
    syntax AssertTestMethod ::= "IS_TEST" "(" ")" [symbol(), klabel(method_AssertTest_IS_TEST_)]
    
    syntax AssertTestMethod ::= "failed" "(" ")" [symbol(), klabel(method_AssertTest_failed_)]
    
    syntax AssertTestMethod ::= "setUp" "(" ")" [symbol(), klabel(method_AssertTest_setUp_)]
    
    syntax AssertTestMethod ::= "testFail_assert_false" "(" ")" [symbol(), klabel(method_AssertTest_testFail_assert_false_)]
    
    syntax AssertTestMethod ::= "testFail_assert_true" "(" ")" [symbol(), klabel(method_AssertTest_testFail_assert_true_)]
    
    syntax AssertTestMethod ::= "test_assert_false" "(" ")" [symbol(), klabel(method_AssertTest_test_assert_false_)]
    
    syntax AssertTestMethod ::= "test_assert_true" "(" ")" [symbol(), klabel(method_AssertTest_test_assert_true_)]
    
    syntax AssertTestMethod ::= "vm" "(" ")" [symbol(), klabel(method_AssertTest_vm_)]
    
    rule  ( AssertTest . IS_SCRIPT ( ) => #abiCallData ( "IS_SCRIPT" , .TypedArgs ) )
      
    
    rule  ( AssertTest . IS_TEST ( ) => #abiCallData ( "IS_TEST" , .TypedArgs ) )
      
    
    rule  ( AssertTest . failed ( ) => #abiCallData ( "failed" , .TypedArgs ) )
      
    
    rule  ( AssertTest . setUp ( ) => #abiCallData ( "setUp" , .TypedArgs ) )
      
    
    rule  ( AssertTest . testFail_assert_false ( ) => #abiCallData ( "testFail_assert_false" , .TypedArgs ) )
      
    
    rule  ( AssertTest . testFail_assert_true ( ) => #abiCallData ( "testFail_assert_true" , .TypedArgs ) )
      
    
    rule  ( AssertTest . test_assert_false ( ) => #abiCallData ( "test_assert_false" , .TypedArgs ) )
      
    
    rule  ( AssertTest . test_assert_true ( ) => #abiCallData ( "test_assert_true" , .TypedArgs ) )
      
    
    rule  ( AssertTest . vm ( ) => #abiCallData ( "vm" , .TypedArgs ) )
      
    
    rule  ( selector ( "IS_SCRIPT()" ) => 4174167879 )
      
    
    rule  ( selector ( "IS_TEST()" ) => 4202047188 )
      
    
    rule  ( selector ( "failed()" ) => 3124842406 )
      
    
    rule  ( selector ( "setUp()" ) => 177362148 )
      
    
    rule  ( selector ( "testFail_assert_false()" ) => 2057948334 )
      
    
    rule  ( selector ( "testFail_assert_true()" ) => 409427266 )
      
    
    rule  ( selector ( "test_assert_false()" ) => 1574882301 )
      
    
    rule  ( selector ( "test_assert_true()" ) => 906863826 )
      
    
    rule  ( selector ( "vm()" ) => 980845667 )
      

endmodule

module TEST-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= TestContract
    
    syntax TestContract ::= "Test" [symbol(), klabel(contract_Test)]
    
    rule  ( #binRuntime ( Test ) => #parseByteStack ( "0x" ) )
      
    
    syntax Field ::= TestField
    
    syntax TestField ::= "IS_TEST" [symbol(), klabel(field_Test_IS_TEST)]
    
    syntax TestField ::= "_failed" [symbol(), klabel(field_Test__failed)]
    
    syntax TestField ::= "IS_SCRIPT" [symbol(), klabel(field_Test_IS_SCRIPT)]
    
    syntax TestField ::= "stdstore" [symbol(), klabel(field_Test_stdstore)]
    
    rule  ( #loc ( Test . IS_TEST ) => 0 )
      
    
    rule  ( #loc ( Test . _failed ) => 0 )
      
    
    rule  ( #loc ( Test . IS_SCRIPT ) => 0 )
      
    
    rule  ( #loc ( Test . stdstore ) => 1 )
      
    
    syntax Bytes ::= TestContract "." TestMethod [function(), symbol(), klabel(method_Test)]
    
    syntax TestMethod ::= "IS_SCRIPT" "(" ")" [symbol(), klabel(method_Test_IS_SCRIPT_)]
    
    syntax TestMethod ::= "IS_TEST" "(" ")" [symbol(), klabel(method_Test_IS_TEST_)]
    
    syntax TestMethod ::= "failed" "(" ")" [symbol(), klabel(method_Test_failed_)]
    
    syntax TestMethod ::= "vm" "(" ")" [symbol(), klabel(method_Test_vm_)]
    
    rule  ( Test . IS_SCRIPT ( ) => #abiCallData ( "IS_SCRIPT" , .TypedArgs ) )
      
    
    rule  ( Test . IS_TEST ( ) => #abiCallData ( "IS_TEST" , .TypedArgs ) )
      
    
    rule  ( Test . failed ( ) => #abiCallData ( "failed" , .TypedArgs ) )
      
    
    rule  ( Test . vm ( ) => #abiCallData ( "vm" , .TypedArgs ) )
      
    
    rule  ( selector ( "IS_SCRIPT()" ) => 4174167879 )
      
    
    rule  ( selector ( "IS_TEST()" ) => 4202047188 )
      
    
    rule  ( selector ( "failed()" ) => 3124842406 )
      
    
    rule  ( selector ( "vm()" ) => 980845667 )
      

endmodule

module STDERROR-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= StdErrorContract
    
    syntax StdErrorContract ::= "stdError" [symbol(), klabel(contract_stdError)]
    
    rule  ( #binRuntime ( stdError ) => #parseByteStack ( "0x73000000000000000000000000000000000000000030146080604052600436106100a85760003560e01c8063ac3d92c611610070578063ac3d92c6146100eb578063b22dc54d14610101578063b67689da14610109578063d160e4de14610111578063fa784a441461011957600080fd5b806305ee8612146100ad57806310332977146100cb5780631de45560146100d35780638995290f146100db578063986c5f68146100e3575b600080fd5b6100b5610121565b6040516100c291906101ec565b60405180910390f35b6100b561015c565b6100b561016e565b6100b5610180565b6100b5610192565b6100b56040518060200160405280600081525081565b6100b56101a4565b6100b56101b6565b6100b56101c8565b6100b56101da565b604051603260248201526044015b60408051601f198184030181529190526020810180516001600160e01b0316634e487b7160e01b17905281565b6040516001602482015260440161012f565b6040516021602482015260440161012f565b6040516011602482015260440161012f565b6040516041602482015260440161012f565b6040516031602482015260440161012f565b6040516051602482015260440161012f565b6040516022602482015260440161012f565b6040516012602482015260440161012f565b600060208083528351808285015260005b81811015610219578581018301518582016040015282016101fd565b8181111561022b576000604083870101525b50601f01601f191692909201604001939250505056fea2646970667358221220123df24b7f624e3eaa058d8ec30bc8fbc59f6b13d03026623d0f5787ad3dcb8264736f6c634300080d0033" ) )
      
    
    syntax Bytes ::= StdErrorContract "." StdErrorMethod [function(), symbol(), klabel(method_stdError)]
    
    syntax StdErrorMethod ::= "arithmeticError" "(" ")" [symbol(), klabel(method_stdError_arithmeticError_)]
    
    syntax StdErrorMethod ::= "assertionError" "(" ")" [symbol(), klabel(method_stdError_assertionError_)]
    
    syntax StdErrorMethod ::= "divisionError" "(" ")" [symbol(), klabel(method_stdError_divisionError_)]
    
    syntax StdErrorMethod ::= "encodeStorageError" "(" ")" [symbol(), klabel(method_stdError_encodeStorageError_)]
    
    syntax StdErrorMethod ::= "enumConversionError" "(" ")" [symbol(), klabel(method_stdError_enumConversionError_)]
    
    syntax StdErrorMethod ::= "indexOOBError" "(" ")" [symbol(), klabel(method_stdError_indexOOBError_)]
    
    syntax StdErrorMethod ::= "lowLevelError" "(" ")" [symbol(), klabel(method_stdError_lowLevelError_)]
    
    syntax StdErrorMethod ::= "memOverflowError" "(" ")" [symbol(), klabel(method_stdError_memOverflowError_)]
    
    syntax StdErrorMethod ::= "popError" "(" ")" [symbol(), klabel(method_stdError_popError_)]
    
    syntax StdErrorMethod ::= "zeroVarError" "(" ")" [symbol(), klabel(method_stdError_zeroVarError_)]
    
    rule  ( stdError . arithmeticError ( ) => #abiCallData ( "arithmeticError" , .TypedArgs ) )
      
    
    rule  ( stdError . assertionError ( ) => #abiCallData ( "assertionError" , .TypedArgs ) )
      
    
    rule  ( stdError . divisionError ( ) => #abiCallData ( "divisionError" , .TypedArgs ) )
      
    
    rule  ( stdError . encodeStorageError ( ) => #abiCallData ( "encodeStorageError" , .TypedArgs ) )
      
    
    rule  ( stdError . enumConversionError ( ) => #abiCallData ( "enumConversionError" , .TypedArgs ) )
      
    
    rule  ( stdError . indexOOBError ( ) => #abiCallData ( "indexOOBError" , .TypedArgs ) )
      
    
    rule  ( stdError . lowLevelError ( ) => #abiCallData ( "lowLevelError" , .TypedArgs ) )
      
    
    rule  ( stdError . memOverflowError ( ) => #abiCallData ( "memOverflowError" , .TypedArgs ) )
      
    
    rule  ( stdError . popError ( ) => #abiCallData ( "popError" , .TypedArgs ) )
      
    
    rule  ( stdError . zeroVarError ( ) => #abiCallData ( "zeroVarError" , .TypedArgs ) )
      
    
    rule  ( selector ( "arithmeticError()" ) => 2308253967 )
      
    
    rule  ( selector ( "assertionError()" ) => 271788407 )
      
    
    rule  ( selector ( "divisionError()" ) => 4202187332 )
      
    
    rule  ( selector ( "encodeStorageError()" ) => 3512788190 )
      
    
    rule  ( selector ( "enumConversionError()" ) => 501503328 )
      
    
    rule  ( selector ( "indexOOBError()" ) => 99517970 )
      
    
    rule  ( selector ( "lowLevelError()" ) => 2889716422 )
      
    
    rule  ( selector ( "memOverflowError()" ) => 2557239144 )
      
    
    rule  ( selector ( "popError()" ) => 2989344077 )
      
    
    rule  ( selector ( "zeroVarError()" ) => 3061221850 )
      

endmodule

module STDMATH-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= StdMathContract
    
    syntax StdMathContract ::= "stdMath" [symbol(), klabel(contract_stdMath)]
    
    rule  ( #binRuntime ( stdMath ) => #parseByteStack ( "0x73000000000000000000000000000000000000000030146080604052600080fdfea2646970667358221220ada2f27f44e724024917b604c512c1c20578588095600bf29d6557240faa52aa64736f6c634300080d0033" ) )
      

endmodule

module STDSTORAGE-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= StdStorageContract
    
    syntax StdStorageContract ::= "stdStorage" [symbol(), klabel(contract_stdStorage)]
    
    rule  ( #binRuntime ( stdStorage ) => #parseByteStack ( "0x73000000000000000000000000000000000000000030146080604052600436106100355760003560e01c8063535849391461003a575b600080fd5b61004d6100483660046100f2565b61005f565b60405190815260200160405180910390f35b60008060006020855111610074578451610077565b60205b905060005b818110156100d25761008f8160086101bd565b8661009a83886101dc565b815181106100aa576100aa6101f4565b01602001516001600160f81b031916901c9290921791806100ca8161020a565b91505061007c565b5090949350505050565b634e487b7160e01b600052604160045260246000fd5b6000806040838503121561010557600080fd5b823567ffffffffffffffff8082111561011d57600080fd5b818501915085601f83011261013157600080fd5b813581811115610143576101436100dc565b604051601f8201601f19908116603f0116810190838211818310171561016b5761016b6100dc565b8160405282815288602084870101111561018457600080fd5b826020860160208301376000602093820184015298969091013596505050505050565b634e487b7160e01b600052601160045260246000fd5b60008160001904831182151516156101d7576101d76101a7565b500290565b600082198211156101ef576101ef6101a7565b500190565b634e487b7160e01b600052603260045260246000fd5b60006001820161021c5761021c6101a7565b506001019056fea2646970667358221220c2c037d3f1567d69c4ec6d7bde1962f8553acec82c19078ccce7d877a7c99ff864736f6c634300080d0033" ) )
      
    
    syntax Bytes ::= StdStorageContract "." StdStorageMethod [function(), symbol(), klabel(method_stdStorage)]
    
    syntax StdStorageMethod ::= "bytesToBytes32" "(" Bytes ":" "bytes" "," Int ":" "uint256" ")" [symbol(), klabel(method_stdStorage_bytesToBytes32_bytes_uint256)]
    
    rule  ( stdStorage . bytesToBytes32 ( V0_b : bytes , V1_offset : uint256 ) => #abiCallData ( "bytesToBytes32" , #bytes ( V0_b ) , #uint256 ( V1_offset ) , .TypedArgs ) )
       ensures ( #rangeUInt ( 128 , lengthBytes ( V0_b ) )
       andBool ( #rangeUInt ( 256 , V1_offset )
               ))
      
    
    rule  ( selector ( "bytesToBytes32(bytes,uint256)" ) => 1398294841 )
      

endmodule

module VM-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= VmContract
    
    syntax VmContract ::= "Vm" [symbol(), klabel(contract_Vm)]
    
    rule  ( #binRuntime ( Vm ) => #parseByteStack ( "0x" ) )
      
    
    syntax Bytes ::= VmContract "." VmMethod [function(), symbol(), klabel(method_Vm)]
    
    syntax VmMethod ::= "accesses" "(" Int ":" "address" ")" [symbol(), klabel(method_Vm_accesses_address)]
    
    syntax VmMethod ::= "activeFork" "(" ")" [symbol(), klabel(method_Vm_activeFork_)]
    
    syntax VmMethod ::= "addr" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_addr_uint256)]
    
    syntax VmMethod ::= "assume" "(" Int ":" "bool" ")" [symbol(), klabel(method_Vm_assume_bool)]
    
    syntax VmMethod ::= "broadcast" "(" ")" [symbol(), klabel(method_Vm_broadcast_)]
    
    syntax VmMethod ::= "broadcast" "(" Int ":" "address" ")" [symbol(), klabel(method_Vm_broadcast_address)]
    
    syntax VmMethod ::= "chainId" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_chainId_uint256)]
    
    syntax VmMethod ::= "clearMockedCalls" "(" ")" [symbol(), klabel(method_Vm_clearMockedCalls_)]
    
    syntax VmMethod ::= "closeFile" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_closeFile_string)]
    
    syntax VmMethod ::= "coinbase" "(" Int ":" "address" ")" [symbol(), klabel(method_Vm_coinbase_address)]
    
    syntax VmMethod ::= "createFork" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_createFork_string)]
    
    syntax VmMethod ::= "createFork" "(" String ":" "string" "," Int ":" "uint256" ")" [symbol(), klabel(method_Vm_createFork_string_uint256)]
    
    syntax VmMethod ::= "createSelectFork" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_createSelectFork_string)]
    
    syntax VmMethod ::= "createSelectFork" "(" String ":" "string" "," Int ":" "uint256" ")" [symbol(), klabel(method_Vm_createSelectFork_string_uint256)]
    
    syntax VmMethod ::= "deal" "(" Int ":" "address" "," Int ":" "uint256" ")" [symbol(), klabel(method_Vm_deal_address_uint256)]
    
    syntax VmMethod ::= "deriveKey" "(" String ":" "string" "," String ":" "string" "," Int ":" "uint32" ")" [symbol(), klabel(method_Vm_deriveKey_string_string_uint32)]
    
    syntax VmMethod ::= "deriveKey" "(" String ":" "string" "," Int ":" "uint32" ")" [symbol(), klabel(method_Vm_deriveKey_string_uint32)]
    
    syntax VmMethod ::= "envAddress" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_envAddress_string)]
    
    syntax VmMethod ::= "envAddress" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_envAddress_string_string)]
    
    syntax VmMethod ::= "envBool" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_envBool_string)]
    
    syntax VmMethod ::= "envBool" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_envBool_string_string)]
    
    syntax VmMethod ::= "envBytes" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_envBytes_string)]
    
    syntax VmMethod ::= "envBytes" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_envBytes_string_string)]
    
    syntax VmMethod ::= "envBytes32" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_envBytes32_string)]
    
    syntax VmMethod ::= "envBytes32" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_envBytes32_string_string)]
    
    syntax VmMethod ::= "envInt" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_envInt_string)]
    
    syntax VmMethod ::= "envInt" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_envInt_string_string)]
    
    syntax VmMethod ::= "envString" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_envString_string)]
    
    syntax VmMethod ::= "envString" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_envString_string_string)]
    
    syntax VmMethod ::= "envUint" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_envUint_string)]
    
    syntax VmMethod ::= "envUint" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_envUint_string_string)]
    
    syntax VmMethod ::= "etch" "(" Int ":" "address" "," Bytes ":" "bytes" ")" [symbol(), klabel(method_Vm_etch_address_bytes)]
    
    syntax VmMethod ::= "expectCall" "(" Int ":" "address" "," Bytes ":" "bytes" ")" [symbol(), klabel(method_Vm_expectCall_address_bytes)]
    
    syntax VmMethod ::= "expectCall" "(" Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" ")" [symbol(), klabel(method_Vm_expectCall_address_uint256_bytes)]
    
    syntax VmMethod ::= "expectEmit" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" ")" [symbol(), klabel(method_Vm_expectEmit_bool_bool_bool_bool)]
    
    syntax VmMethod ::= "expectEmit" "(" Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "bool" "," Int ":" "address" ")" [symbol(), klabel(method_Vm_expectEmit_bool_bool_bool_bool_address)]
    
    syntax VmMethod ::= "expectRevert" "(" ")" [symbol(), klabel(method_Vm_expectRevert_)]
    
    syntax VmMethod ::= "expectRevert" "(" Bytes ":" "bytes" ")" [symbol(), klabel(method_Vm_expectRevert_bytes)]
    
    syntax VmMethod ::= "expectRevert" "(" Int ":" "bytes4" ")" [symbol(), klabel(method_Vm_expectRevert_bytes4)]
    
    syntax VmMethod ::= "fee" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_fee_uint256)]
    
    syntax VmMethod ::= "ffi" "(" K ":" "string[]" ")" [symbol(), klabel(method_Vm_ffi_string[])]
    
    syntax VmMethod ::= "getCode" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_getCode_string)]
    
    syntax VmMethod ::= "getNonce" "(" Int ":" "address" ")" [symbol(), klabel(method_Vm_getNonce_address)]
    
    syntax VmMethod ::= "getRecordedLogs" "(" ")" [symbol(), klabel(method_Vm_getRecordedLogs_)]
    
    syntax VmMethod ::= "label" "(" Int ":" "address" "," String ":" "string" ")" [symbol(), klabel(method_Vm_label_address_string)]
    
    syntax VmMethod ::= "load" "(" Int ":" "address" "," Int ":" "bytes32" ")" [symbol(), klabel(method_Vm_load_address_bytes32)]
    
    syntax VmMethod ::= "mockCall" "(" Int ":" "address" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol(), klabel(method_Vm_mockCall_address_bytes_bytes)]
    
    syntax VmMethod ::= "mockCall" "(" Int ":" "address" "," Int ":" "uint256" "," Bytes ":" "bytes" "," Bytes ":" "bytes" ")" [symbol(), klabel(method_Vm_mockCall_address_uint256_bytes_bytes)]
    
    syntax VmMethod ::= "prank" "(" Int ":" "address" ")" [symbol(), klabel(method_Vm_prank_address)]
    
    syntax VmMethod ::= "prank" "(" Int ":" "address" "," Int ":" "address" ")" [symbol(), klabel(method_Vm_prank_address_address)]
    
    syntax VmMethod ::= "readFile" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_readFile_string)]
    
    syntax VmMethod ::= "readLine" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_readLine_string)]
    
    syntax VmMethod ::= "record" "(" ")" [symbol(), klabel(method_Vm_record_)]
    
    syntax VmMethod ::= "recordLogs" "(" ")" [symbol(), klabel(method_Vm_recordLogs_)]
    
    syntax VmMethod ::= "removeFile" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_removeFile_string)]
    
    syntax VmMethod ::= "revertTo" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_revertTo_uint256)]
    
    syntax VmMethod ::= "roll" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_roll_uint256)]
    
    syntax VmMethod ::= "rollFork" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_rollFork_uint256)]
    
    syntax VmMethod ::= "rollFork" "(" Int ":" "uint256" "," Int ":" "uint256" ")" [symbol(), klabel(method_Vm_rollFork_uint256_uint256)]
    
    syntax VmMethod ::= "rpcUrl" "(" String ":" "string" ")" [symbol(), klabel(method_Vm_rpcUrl_string)]
    
    syntax VmMethod ::= "rpcUrls" "(" ")" [symbol(), klabel(method_Vm_rpcUrls_)]
    
    syntax VmMethod ::= "selectFork" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_selectFork_uint256)]
    
    syntax VmMethod ::= "setEnv" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_setEnv_string_string)]
    
    syntax VmMethod ::= "setNonce" "(" Int ":" "address" "," Int ":" "uint64" ")" [symbol(), klabel(method_Vm_setNonce_address_uint64)]
    
    syntax VmMethod ::= "sign" "(" Int ":" "uint256" "," Int ":" "bytes32" ")" [symbol(), klabel(method_Vm_sign_uint256_bytes32)]
    
    syntax VmMethod ::= "snapshot" "(" ")" [symbol(), klabel(method_Vm_snapshot_)]
    
    syntax VmMethod ::= "startBroadcast" "(" ")" [symbol(), klabel(method_Vm_startBroadcast_)]
    
    syntax VmMethod ::= "startBroadcast" "(" Int ":" "address" ")" [symbol(), klabel(method_Vm_startBroadcast_address)]
    
    syntax VmMethod ::= "startPrank" "(" Int ":" "address" ")" [symbol(), klabel(method_Vm_startPrank_address)]
    
    syntax VmMethod ::= "startPrank" "(" Int ":" "address" "," Int ":" "address" ")" [symbol(), klabel(method_Vm_startPrank_address_address)]
    
    syntax VmMethod ::= "stopBroadcast" "(" ")" [symbol(), klabel(method_Vm_stopBroadcast_)]
    
    syntax VmMethod ::= "stopPrank" "(" ")" [symbol(), klabel(method_Vm_stopPrank_)]
    
    syntax VmMethod ::= "store" "(" Int ":" "address" "," Int ":" "bytes32" "," Int ":" "bytes32" ")" [symbol(), klabel(method_Vm_store_address_bytes32_bytes32)]
    
    syntax VmMethod ::= "toString" "(" Int ":" "address" ")" [symbol(), klabel(method_Vm_toString_address)]
    
    syntax VmMethod ::= "toString" "(" Int ":" "bool" ")" [symbol(), klabel(method_Vm_toString_bool)]
    
    syntax VmMethod ::= "toString" "(" Bytes ":" "bytes" ")" [symbol(), klabel(method_Vm_toString_bytes)]
    
    syntax VmMethod ::= "toString" "(" Int ":" "bytes32" ")" [symbol(), klabel(method_Vm_toString_bytes32)]
    
    syntax VmMethod ::= "toString" "(" Int ":" "int256" ")" [symbol(), klabel(method_Vm_toString_int256)]
    
    syntax VmMethod ::= "toString" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_toString_uint256)]
    
    syntax VmMethod ::= "warp" "(" Int ":" "uint256" ")" [symbol(), klabel(method_Vm_warp_uint256)]
    
    syntax VmMethod ::= "writeFile" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_writeFile_string_string)]
    
    syntax VmMethod ::= "writeLine" "(" String ":" "string" "," String ":" "string" ")" [symbol(), klabel(method_Vm_writeLine_string_string)]
    
    rule  ( Vm . accesses ( V0_ : address ) => #abiCallData ( "accesses" , #address ( V0_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . activeFork ( ) => #abiCallData ( "activeFork" , .TypedArgs ) )
      
    
    rule  ( Vm . addr ( V0_ : uint256 ) => #abiCallData ( "addr" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . assume ( V0_ : bool ) => #abiCallData ( "assume" , #bool ( V0_ ) , .TypedArgs ) )
       ensures #rangeBool ( V0_ )
      
    
    rule  ( Vm . broadcast ( ) => #abiCallData ( "broadcast" , .TypedArgs ) )
      
    
    rule  ( Vm . broadcast ( V0_ : address ) => #abiCallData ( "broadcast" , #address ( V0_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . chainId ( V0_ : uint256 ) => #abiCallData ( "chainId" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . clearMockedCalls ( ) => #abiCallData ( "clearMockedCalls" , .TypedArgs ) )
      
    
    rule  ( Vm . closeFile ( V0_ : string ) => #abiCallData ( "closeFile" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . coinbase ( V0_ : address ) => #abiCallData ( "coinbase" , #address ( V0_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . createFork ( V0_ : string ) => #abiCallData ( "createFork" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . createFork ( V0_ : string , V1_ : uint256 ) => #abiCallData ( "createFork" , #string ( V0_ ) , #uint256 ( V1_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V1_ )
      
    
    rule  ( Vm . createSelectFork ( V0_ : string ) => #abiCallData ( "createSelectFork" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . createSelectFork ( V0_ : string , V1_ : uint256 ) => #abiCallData ( "createSelectFork" , #string ( V0_ ) , #uint256 ( V1_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V1_ )
      
    
    rule  ( Vm . deal ( V0_ : address , V1_ : uint256 ) => #abiCallData ( "deal" , #address ( V0_ ) , #uint256 ( V1_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 256 , V1_ )
               ))
      
    
    rule  ( Vm . deriveKey ( V0_ : string , V1_ : string , V2_ : uint32 ) => #abiCallData ( "deriveKey" , #string ( V0_ ) , #string ( V1_ ) , #uint32 ( V2_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 32 , V2_ )
      
    
    rule  ( Vm . deriveKey ( V0_ : string , V1_ : uint32 ) => #abiCallData ( "deriveKey" , #string ( V0_ ) , #uint32 ( V1_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 32 , V1_ )
      
    
    rule  ( Vm . envAddress ( V0_ : string ) => #abiCallData ( "envAddress" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envAddress ( V0_ : string , V1_ : string ) => #abiCallData ( "envAddress" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envBool ( V0_ : string ) => #abiCallData ( "envBool" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envBool ( V0_ : string , V1_ : string ) => #abiCallData ( "envBool" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envBytes ( V0_ : string ) => #abiCallData ( "envBytes" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envBytes ( V0_ : string , V1_ : string ) => #abiCallData ( "envBytes" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envBytes32 ( V0_ : string ) => #abiCallData ( "envBytes32" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envBytes32 ( V0_ : string , V1_ : string ) => #abiCallData ( "envBytes32" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envInt ( V0_ : string ) => #abiCallData ( "envInt" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envInt ( V0_ : string , V1_ : string ) => #abiCallData ( "envInt" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envString ( V0_ : string ) => #abiCallData ( "envString" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envString ( V0_ : string , V1_ : string ) => #abiCallData ( "envString" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envUint ( V0_ : string ) => #abiCallData ( "envUint" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . envUint ( V0_ : string , V1_ : string ) => #abiCallData ( "envUint" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . etch ( V0_ : address , V1_ : bytes ) => #abiCallData ( "etch" , #address ( V0_ ) , #bytes ( V1_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 128 , lengthBytes ( V1_ ) )
               ))
      
    
    rule  ( Vm . expectCall ( V0_ : address , V1_ : bytes ) => #abiCallData ( "expectCall" , #address ( V0_ ) , #bytes ( V1_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 128 , lengthBytes ( V1_ ) )
               ))
      
    
    rule  ( Vm . expectCall ( V0_ : address , V1_ : uint256 , V2_ : bytes ) => #abiCallData ( "expectCall" , #address ( V0_ ) , #uint256 ( V1_ ) , #bytes ( V2_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 256 , V1_ )
       andBool ( #rangeUInt ( 128 , lengthBytes ( V2_ ) )
               )))
      
    
    rule  ( Vm . expectEmit ( V0_ : bool , V1_ : bool , V2_ : bool , V3_ : bool ) => #abiCallData ( "expectEmit" , #bool ( V0_ ) , #bool ( V1_ ) , #bool ( V2_ ) , #bool ( V3_ ) , .TypedArgs ) )
       ensures ( #rangeBool ( V0_ )
       andBool ( #rangeBool ( V1_ )
       andBool ( #rangeBool ( V2_ )
       andBool ( #rangeBool ( V3_ )
               ))))
      
    
    rule  ( Vm . expectEmit ( V0_ : bool , V1_ : bool , V2_ : bool , V3_ : bool , V4_ : address ) => #abiCallData ( "expectEmit" , #bool ( V0_ ) , #bool ( V1_ ) , #bool ( V2_ ) , #bool ( V3_ ) , #address ( V4_ ) , .TypedArgs ) )
       ensures ( #rangeBool ( V0_ )
       andBool ( #rangeBool ( V1_ )
       andBool ( #rangeBool ( V2_ )
       andBool ( #rangeBool ( V3_ )
       andBool ( #rangeAddress ( V4_ )
               )))))
      
    
    rule  ( Vm . expectRevert ( ) => #abiCallData ( "expectRevert" , .TypedArgs ) )
      
    
    rule  ( Vm . expectRevert ( V0_ : bytes ) => #abiCallData ( "expectRevert" , #bytes ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 128 , lengthBytes ( V0_ ) )
      
    
    rule  ( Vm . expectRevert ( V0_ : bytes4 ) => #abiCallData ( "expectRevert" , #bytes4 ( V0_ ) , .TypedArgs ) )
       ensures #rangeBytes ( 4 , V0_ )
      
    
    rule  ( Vm . fee ( V0_ : uint256 ) => #abiCallData ( "fee" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . getCode ( V0_ : string ) => #abiCallData ( "getCode" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . getNonce ( V0_ : address ) => #abiCallData ( "getNonce" , #address ( V0_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . getRecordedLogs ( ) => #abiCallData ( "getRecordedLogs" , .TypedArgs ) )
      
    
    rule  ( Vm . label ( V0_ : address , V1_ : string ) => #abiCallData ( "label" , #address ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . load ( V0_ : address , V1_ : bytes32 ) => #abiCallData ( "load" , #address ( V0_ ) , #bytes32 ( V1_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 256 , V1_ )
               ))
      
    
    rule  ( Vm . mockCall ( V0_ : address , V1_ : bytes , V2_ : bytes ) => #abiCallData ( "mockCall" , #address ( V0_ ) , #bytes ( V1_ ) , #bytes ( V2_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 128 , lengthBytes ( V1_ ) )
       andBool ( #rangeUInt ( 128 , lengthBytes ( V2_ ) )
               )))
      
    
    rule  ( Vm . mockCall ( V0_ : address , V1_ : uint256 , V2_ : bytes , V3_ : bytes ) => #abiCallData ( "mockCall" , #address ( V0_ ) , #uint256 ( V1_ ) , #bytes ( V2_ ) , #bytes ( V3_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 256 , V1_ )
       andBool ( #rangeUInt ( 128 , lengthBytes ( V2_ ) )
       andBool ( #rangeUInt ( 128 , lengthBytes ( V3_ ) )
               ))))
      
    
    rule  ( Vm . prank ( V0_ : address ) => #abiCallData ( "prank" , #address ( V0_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . prank ( V0_ : address , V1_ : address ) => #abiCallData ( "prank" , #address ( V0_ ) , #address ( V1_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeAddress ( V1_ )
               ))
      
    
    rule  ( Vm . readFile ( V0_ : string ) => #abiCallData ( "readFile" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . readLine ( V0_ : string ) => #abiCallData ( "readLine" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . record ( ) => #abiCallData ( "record" , .TypedArgs ) )
      
    
    rule  ( Vm . recordLogs ( ) => #abiCallData ( "recordLogs" , .TypedArgs ) )
      
    
    rule  ( Vm . removeFile ( V0_ : string ) => #abiCallData ( "removeFile" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . revertTo ( V0_ : uint256 ) => #abiCallData ( "revertTo" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . roll ( V0_ : uint256 ) => #abiCallData ( "roll" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . rollFork ( V0_ : uint256 ) => #abiCallData ( "rollFork" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . rollFork ( V0_forkId : uint256 , V1_blockNumber : uint256 ) => #abiCallData ( "rollFork" , #uint256 ( V0_forkId ) , #uint256 ( V1_blockNumber ) , .TypedArgs ) )
       ensures ( #rangeUInt ( 256 , V0_forkId )
       andBool ( #rangeUInt ( 256 , V1_blockNumber )
               ))
      
    
    rule  ( Vm . rpcUrl ( V0_ : string ) => #abiCallData ( "rpcUrl" , #string ( V0_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . rpcUrls ( ) => #abiCallData ( "rpcUrls" , .TypedArgs ) )
      
    
    rule  ( Vm . selectFork ( V0_ : uint256 ) => #abiCallData ( "selectFork" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . setEnv ( V0_ : string , V1_ : string ) => #abiCallData ( "setEnv" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . setNonce ( V0_ : address , V1_ : uint64 ) => #abiCallData ( "setNonce" , #address ( V0_ ) , #uint64 ( V1_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 64 , V1_ )
               ))
      
    
    rule  ( Vm . sign ( V0_ : uint256 , V1_ : bytes32 ) => #abiCallData ( "sign" , #uint256 ( V0_ ) , #bytes32 ( V1_ ) , .TypedArgs ) )
       ensures ( #rangeUInt ( 256 , V0_ )
       andBool ( #rangeUInt ( 256 , V1_ )
               ))
      
    
    rule  ( Vm . snapshot ( ) => #abiCallData ( "snapshot" , .TypedArgs ) )
      
    
    rule  ( Vm . startBroadcast ( ) => #abiCallData ( "startBroadcast" , .TypedArgs ) )
      
    
    rule  ( Vm . startBroadcast ( V0_ : address ) => #abiCallData ( "startBroadcast" , #address ( V0_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . startPrank ( V0_ : address ) => #abiCallData ( "startPrank" , #address ( V0_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . startPrank ( V0_ : address , V1_ : address ) => #abiCallData ( "startPrank" , #address ( V0_ ) , #address ( V1_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeAddress ( V1_ )
               ))
      
    
    rule  ( Vm . stopBroadcast ( ) => #abiCallData ( "stopBroadcast" , .TypedArgs ) )
      
    
    rule  ( Vm . stopPrank ( ) => #abiCallData ( "stopPrank" , .TypedArgs ) )
      
    
    rule  ( Vm . store ( V0_ : address , V1_ : bytes32 , V2_ : bytes32 ) => #abiCallData ( "store" , #address ( V0_ ) , #bytes32 ( V1_ ) , #bytes32 ( V2_ ) , .TypedArgs ) )
       ensures ( #rangeAddress ( V0_ )
       andBool ( #rangeUInt ( 256 , V1_ )
       andBool ( #rangeUInt ( 256 , V2_ )
               )))
      
    
    rule  ( Vm . toString ( V0_ : address ) => #abiCallData ( "toString" , #address ( V0_ ) , .TypedArgs ) )
       ensures #rangeAddress ( V0_ )
      
    
    rule  ( Vm . toString ( V0_ : bool ) => #abiCallData ( "toString" , #bool ( V0_ ) , .TypedArgs ) )
       ensures #rangeBool ( V0_ )
      
    
    rule  ( Vm . toString ( V0_ : bytes ) => #abiCallData ( "toString" , #bytes ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 128 , lengthBytes ( V0_ ) )
      
    
    rule  ( Vm . toString ( V0_ : bytes32 ) => #abiCallData ( "toString" , #bytes32 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . toString ( V0_ : int256 ) => #abiCallData ( "toString" , #int256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeSInt ( 256 , V0_ )
      
    
    rule  ( Vm . toString ( V0_ : uint256 ) => #abiCallData ( "toString" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . warp ( V0_ : uint256 ) => #abiCallData ( "warp" , #uint256 ( V0_ ) , .TypedArgs ) )
       ensures #rangeUInt ( 256 , V0_ )
      
    
    rule  ( Vm . writeFile ( V0_ : string , V1_ : string ) => #abiCallData ( "writeFile" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( Vm . writeLine ( V0_ : string , V1_ : string ) => #abiCallData ( "writeLine" , #string ( V0_ ) , #string ( V1_ ) , .TypedArgs ) )
      
    
    rule  ( selector ( "accesses(address)" ) => 1706857601 )
      
    
    rule  ( selector ( "activeFork()" ) => 789593890 )
      
    
    rule  ( selector ( "addr(uint256)" ) => 4288775753 )
      
    
    rule  ( selector ( "assume(bool)" ) => 1281615202 )
      
    
    rule  ( selector ( "broadcast()" ) => 2949218368 )
      
    
    rule  ( selector ( "broadcast(address)" ) => 3868601563 )
      
    
    rule  ( selector ( "chainId(uint256)" ) => 1078582738 )
      
    
    rule  ( selector ( "clearMockedCalls()" ) => 1071599125 )
      
    
    rule  ( selector ( "closeFile(string)" ) => 1220748319 )
      
    
    rule  ( selector ( "coinbase(address)" ) => 4282924116 )
      
    
    rule  ( selector ( "createFork(string)" ) => 834286744 )
      
    
    rule  ( selector ( "createFork(string,uint256)" ) => 1805892139 )
      
    
    rule  ( selector ( "createSelectFork(string)" ) => 2556952628 )
      
    
    rule  ( selector ( "createSelectFork(string,uint256)" ) => 1911440973 )
      
    
    rule  ( selector ( "deal(address,uint256)" ) => 3364511341 )
      
    
    rule  ( selector ( "deriveKey(string,string,uint32)" ) => 1808477211 )
      
    
    rule  ( selector ( "deriveKey(string,uint32)" ) => 1646872971 )
      
    
    rule  ( selector ( "envAddress(string)" ) => 890066623 )
      
    
    rule  ( selector ( "envAddress(string,string)" ) => 2905717242 )
      
    
    rule  ( selector ( "envBool(string)" ) => 2127686781 )
      
    
    rule  ( selector ( "envBool(string,string)" ) => 2863521455 )
      
    
    rule  ( selector ( "envBytes(string)" ) => 1299951366 )
      
    
    rule  ( selector ( "envBytes(string,string)" ) => 3720504603 )
      
    
    rule  ( selector ( "envBytes32(string)" ) => 2543095874 )
      
    
    rule  ( selector ( "envBytes32(string,string)" ) => 1525821889 )
      
    
    rule  ( selector ( "envInt(string)" ) => 2301234273 )
      
    
    rule  ( selector ( "envInt(string,string)" ) => 1108873552 )
      
    
    rule  ( selector ( "envString(string)" ) => 4168600345 )
      
    
    rule  ( selector ( "envString(string,string)" ) => 347089865 )
      
    
    rule  ( selector ( "envUint(string)" ) => 3247934751 )
      
    
    rule  ( selector ( "envUint(string,string)" ) => 4091461785 )
      
    
    rule  ( selector ( "etch(address,bytes)" ) => 3033974658 )
      
    
    rule  ( selector ( "expectCall(address,bytes)" ) => 3177903156 )
      
    
    rule  ( selector ( "expectCall(address,uint256,bytes)" ) => 4077681571 )
      
    
    rule  ( selector ( "expectEmit(bool,bool,bool,bool)" ) => 1226622914 )
      
    
    rule  ( selector ( "expectEmit(bool,bool,bool,bool,address)" ) => 2176505587 )
      
    
    rule  ( selector ( "expectRevert()" ) => 4102309908 )
      
    
    rule  ( selector ( "expectRevert(bytes)" ) => 4069379763 )
      
    
    rule  ( selector ( "expectRevert(bytes4)" ) => 3273568480 )
      
    
    rule  ( selector ( "fee(uint256)" ) => 968063664 )
      
    
    rule  ( selector ( "ffi(string[])" ) => 2299921511 )
      
    
    rule  ( selector ( "getCode(string)" ) => 2367473957 )
      
    
    rule  ( selector ( "getNonce(address)" ) => 755185067 )
      
    
    rule  ( selector ( "getRecordedLogs()" ) => 420828068 )
      
    
    rule  ( selector ( "label(address,string)" ) => 3327641368 )
      
    
    rule  ( selector ( "load(address,bytes32)" ) => 1719639408 )
      
    
    rule  ( selector ( "mockCall(address,bytes,bytes)" ) => 3110212580 )
      
    
    rule  ( selector ( "mockCall(address,uint256,bytes,bytes)" ) => 2168494993 )
      
    
    rule  ( selector ( "prank(address)" ) => 3395723175 )
      
    
    rule  ( selector ( "prank(address,address)" ) => 1206193358 )
      
    
    rule  ( selector ( "readFile(string)" ) => 1626979089 )
      
    
    rule  ( selector ( "readLine(string)" ) => 1895126824 )
      
    
    rule  ( selector ( "record()" ) => 644673801 )
      
    
    rule  ( selector ( "recordLogs()" ) => 1101999954 )
      
    
    rule  ( selector ( "removeFile(string)" ) => 4054835277 )
      
    
    rule  ( selector ( "revertTo(uint256)" ) => 1155002532 )
      
    
    rule  ( selector ( "roll(uint256)" ) => 528174896 )
      
    
    rule  ( selector ( "rollFork(uint256)" ) => 3652973473 )
      
    
    rule  ( selector ( "rollFork(uint256,uint256)" ) => 3612115876 )
      
    
    rule  ( selector ( "rpcUrl(string)" ) => 2539285737 )
      
    
    rule  ( selector ( "rpcUrls()" ) => 2824504344 )
      
    
    rule  ( selector ( "selectFork(uint256)" ) => 2663344167 )
      
    
    rule  ( selector ( "setEnv(string,string)" ) => 1029252078 )
      
    
    rule  ( selector ( "setNonce(address,uint64)" ) => 4175530839 )
      
    
    rule  ( selector ( "sign(uint256,bytes32)" ) => 3812747940 )
      
    
    rule  ( selector ( "snapshot()" ) => 2534502746 )
      
    
    rule  ( selector ( "startBroadcast()" ) => 2142579071 )
      
    
    rule  ( selector ( "startBroadcast(address)" ) => 2146183821 )
      
    
    rule  ( selector ( "startPrank(address)" ) => 105151830 )
      
    
    rule  ( selector ( "startPrank(address,address)" ) => 1169514616 )
      
    
    rule  ( selector ( "stopBroadcast()" ) => 1995103542 )
      
    
    rule  ( selector ( "stopPrank()" ) => 2428830011 )
      
    
    rule  ( selector ( "store(address,bytes32,bytes32)" ) => 1892290747 )
      
    
    rule  ( selector ( "toString(address)" ) => 1456103998 )
      
    
    rule  ( selector ( "toString(bool)" ) => 1910302682 )
      
    
    rule  ( selector ( "toString(bytes)" ) => 1907020045 )
      
    
    rule  ( selector ( "toString(bytes32)" ) => 2971277800 )
      
    
    rule  ( selector ( "toString(int256)" ) => 2736964622 )
      
    
    rule  ( selector ( "toString(uint256)" ) => 1761649582 )
      
    
    rule  ( selector ( "warp(uint256)" ) => 3856056066 )
      
    
    rule  ( selector ( "writeFile(string,string)" ) => 2306738839 )
      
    
    rule  ( selector ( "writeLine(string,string)" ) => 1637714303 )
      

endmodule

module CONSOLE-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= ConsoleContract
    
    syntax ConsoleContract ::= "console" [symbol(), klabel(contract_console)]
    
    rule  ( #binRuntime ( console ) => #parseByteStack ( "0x73000000000000000000000000000000000000000030146080604052600080fdfea264697066735822122055cb7f21d69d5a68626bed666b69adc58fdc46d700fc111b3a1cc03e01c56ffd64736f6c634300080d0033" ) )
      

endmodule

module CONSOLE2-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= Console2Contract
    
    syntax Console2Contract ::= "console2" [symbol(), klabel(contract_console2)]
    
    rule  ( #binRuntime ( console2 ) => #parseByteStack ( "0x73000000000000000000000000000000000000000030146080604052600080fdfea264697066735822122017af94728e4fd8592ef4392559b9c941d0bf92d7928b48a70203c5ea8bb219ad64736f6c634300080d0033" ) )
      

endmodule

module DSTEST-CONTRACT
    imports public FOUNDRY
    
    syntax Contract ::= DSTestContract
    
    syntax DSTestContract ::= "DSTest" [symbol(), klabel(contract_DSTest)]
    
    rule  ( #binRuntime ( DSTest ) => #parseByteStack ( "0x608060405234801561001057600080fd5b50600436106100365760003560e01c8063ba414fa61461003b578063fa7626d414610057575b600080fd5b610043610064565b604051901515815260200160405180910390f35b6000546100439060ff1681565b60008054610100900460ff16156100845750600054610100900460ff1690565b6000737109709ecfa91a80626ff3989d68f67f5b1dd12d3b1561018a5760408051737109709ecfa91a80626ff3989d68f67f5b1dd12d602082018190526519985a5b195960d21b82840152825180830384018152606083019093526000929091610112917f667f9d70ca411d70ead50d8d5c22070dafc36ad75f3dcf5e7237b22ade9aecc4916080016101ca565b60408051601f198184030181529082905261012c916101ee565b6000604051808303816000865af19150503d8060008114610169576040519150601f19603f3d011682016040523d82523d6000602084013e61016e565b606091505b50915050808060200190518101906101869190610201565b9150505b919050565b6000815160005b818110156101b05760208185018101518683015201610196565b818111156101bf576000828601525b509290920192915050565b6001600160e01b03198316815260006101e6600483018461018f565b949350505050565b60006101fa828461018f565b9392505050565b60006020828403121561021357600080fd5b815180151581146101fa57600080fdfea2646970667358221220a4c5a2ff7302bc039072f8279bb8bf78dbe36fdac7375a2648b1bb0aac1261e264736f6c634300080d0033" ) )
      
    
    syntax Field ::= DSTestField
    
    syntax DSTestField ::= "IS_TEST" [symbol(), klabel(field_DSTest_IS_TEST)]
    
    syntax DSTestField ::= "_failed" [symbol(), klabel(field_DSTest__failed)]
    
    rule  ( #loc ( DSTest . IS_TEST ) => 0 )
      
    
    rule  ( #loc ( DSTest . _failed ) => 0 )
      
    
    syntax Bytes ::= DSTestContract "." DSTestMethod [function(), symbol(), klabel(method_DSTest)]
    
    syntax DSTestMethod ::= "IS_TEST" "(" ")" [symbol(), klabel(method_DSTest_IS_TEST_)]
    
    syntax DSTestMethod ::= "failed" "(" ")" [symbol(), klabel(method_DSTest_failed_)]
    
    rule  ( DSTest . IS_TEST ( ) => #abiCallData ( "IS_TEST" , .TypedArgs ) )
      
    
    rule  ( DSTest . failed ( ) => #abiCallData ( "failed" , .TypedArgs ) )
      
    
    rule  ( selector ( "IS_TEST()" ) => 4202047188 )
      
    
    rule  ( selector ( "failed()" ) => 3124842406 )
      

endmodule
