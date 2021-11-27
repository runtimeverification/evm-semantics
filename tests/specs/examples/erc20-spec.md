ERC20-ish Verification
======================

```k
requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
requires "lemmas/infinite-gas.k"
```

Solidity Code
-------------

File `test.sol` contains some code snippets we want to verify the functional correctness of:

```sol
// SPDX-License-Identifier: Just something to remove the warning

pragma solidity >=0.6.0;

contract ERC20 {

    mapping(address => uint256)                     private _balances;
    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;
    uint8 private _decimals;
    string private _name;
    string private _symbol;

    constructor (
        string memory name
      , string memory symbol
      , address initAccount
      , uint256 initSupply
      , uint8 decimals
      ) public {
        _name = name;
        _symbol = symbol;
        _decimals = decimals;
        _mint(initAccount, initSupply);
    }

    function name()        public view returns (string memory) { return _name;        }
    function symbol()      public view returns (string memory) { return _symbol;      }
    function decimals()    public view returns (uint256)       { return _decimals;    }
    function totalSupply() public view returns (uint256)       { return _totalSupply; }

    function balanceOf(address account) external view returns (uint256) {
        return _balances[account];
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        _transfer(msg.sender, to, amount);
        return true;
    }

    function allowance(address owner, address spender) external view returns (uint256) {
        return _allowances[owner][spender];
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        _approve(msg.sender, spender, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        _transfer(from, to, amount);

        uint256 currentAllowance = _allowances[from][msg.sender];
        require(currentAllowance >= amount, "ERC20: transfer amount exceeds allowance");
        _approve(from, msg.sender, currentAllowance - amount);

        return true;
    }

    function _transfer(address from, address to, uint256 amount) internal {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");
        uint256 toBalance   = _balances[to];
        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        uint256 fromBalanceUpdated = fromBalance - amount;
        uint256 toBalanceUpdated   = toBalance   + amount;
        _balances[from] = fromBalanceUpdated;
        _balances[to]   = toBalanceUpdated;
    }

    function _approve(address owner, address spender, uint256 amount) internal {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
    }

    function _mint(address account, uint256 amount) internal {
        require(account != address(0), "ERC20: mint to the zero address");
        require(_totalSupply <= _totalSupply + amount);//check overflow on totalSupply
        _totalSupply = _totalSupply + amount;
        _balances[account] = _balances[account] + amount;
    }

    function _burn(address account, uint256 amount) internal {
        require(account != address(0), "ERC20: burn from the zero address");
        require(_balances[account] >= _balances[account] - amount);//check underflow on balances
        _totalSupply = _totalSupply - amount;
        _balances[account] = _balances[account] - amount;
    }
}
```

Run `solc test.sol --bin-runtime`:

```evm
======= tests/specs/examples/ERC20.sol:ERC20 =======
Binary of the runtime part:
608060405234801561001057600080fd5b50600436106100935760003560e01c8063313ce56711610066578063313ce5671461022557806370a082311461024357806395d89b411461029b578063a9059cbb1461031e578063dd62ed3e1461038457610093565b806306fdde0314610098578063095ea7b31461011b57806318160ddd1461018157806323b872dd1461019f575b600080fd5b6100a06103fc565b6040518080602001828103825283818151815260200191508051906020019080838360005b838110156100e05780820151818401526020810190506100c5565b50505050905090810190601f16801561010d5780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b6101676004803603604081101561013157600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff1690602001909291908035906020019092919050505061049e565b604051808215151515815260200191505060405180910390f35b6101896104b5565b6040518082815260200191505060405180910390f35b61020b600480360360608110156101b557600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190803573ffffffffffffffffffffffffffffffffffffffff169060200190929190803590602001909291905050506104bf565b604051808215151515815260200191505060405180910390f35b61022d6105bf565b6040518082815260200191505060405180910390f35b6102856004803603602081101561025957600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff1690602001909291905050506105d9565b6040518082815260200191505060405180910390f35b6102a3610621565b6040518080602001828103825283818151815260200191508051906020019080838360005b838110156102e35780820151818401526020810190506102c8565b50505050905090810190601f1680156103105780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b61036a6004803603604081101561033457600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190803590602001909291905050506106c3565b604051808215151515815260200191505060405180910390f35b6103e66004803603604081101561039a57600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190803573ffffffffffffffffffffffffffffffffffffffff1690602001909291905050506106da565b6040518082815260200191505060405180910390f35b606060048054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156104945780601f1061046957610100808354040283529160200191610494565b820191906000526020600020905b81548152906001019060200180831161047757829003601f168201915b5050505050905090565b60006104ab338484610761565b6001905092915050565b6000600254905090565b60006104cc8484846108f3565b6000600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050828110156105a6576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526028815260200180610be76028913960400191505060405180910390fd5b6105b38533858403610761565b60019150509392505050565b6000600360009054906101000a900460ff1660ff16905090565b60008060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050919050565b606060058054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156106b95780601f1061068e576101008083540402835291602001916106b9565b820191906000526020600020905b81548152906001019060200180831161069c57829003601f168201915b5050505050905090565b60006106d03384846108f3565b6001905092915050565b6000600160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054905092915050565b600073ffffffffffffffffffffffffffffffffffffffff168373ffffffffffffffffffffffffffffffffffffffff1614156107e7576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526024815260200180610c346024913960400191505060405180910390fd5b600073ffffffffffffffffffffffffffffffffffffffff168273ffffffffffffffffffffffffffffffffffffffff16141561086d576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526022815260200180610b9f6022913960400191505060405180910390fd5b80600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550505050565b600073ffffffffffffffffffffffffffffffffffffffff168373ffffffffffffffffffffffffffffffffffffffff161415610979576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526025815260200180610c0f6025913960400191505060405180910390fd5b600073ffffffffffffffffffffffffffffffffffffffff168273ffffffffffffffffffffffffffffffffffffffff1614156109ff576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526023815260200180610b7c6023913960400191505060405180910390fd5b60008060008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054905060008060008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054905082811015610ade576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526026815260200180610bc16026913960400191505060405180910390fd5b6000838203905060008484019050816000808973ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550806000808873ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505050505050505056fe45524332303a207472616e7366657220746f20746865207a65726f206164647265737345524332303a20617070726f766520746f20746865207a65726f206164647265737345524332303a207472616e7366657220616d6f756e7420657863656564732062616c616e636545524332303a207472616e7366657220616d6f756e74206578636565647320616c6c6f77616e636545524332303a207472616e736665722066726f6d20746865207a65726f206164647265737345524332303a20617070726f76652066726f6d20746865207a65726f2061646472657373a2646970667358221220d9dbe8fd9e7d5689c52fd8b9b4de4db7247eaa892108b2173084639672f6bc1564736f6c63430006070033
```

Verification Module
-------------------

Helper module for verification tasks.

-   Define `#binRuntime()` as the compiled bytecode.
-   Add any lemmas needed for our proofs.
-   Import a large body of existing lemmas from KEVM.

```k
module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports INFINITE-GAS
    imports EVM-OPTIMIZATIONS

    syntax Step ::= ByteArray | Int
    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax ByteArray ::= #binRuntime() [macro]
 // ------------------------------------------
    rule #binRuntime() => #parseByteStack("0x608060405234801561001057600080fd5b50600436106100935760003560e01c8063313ce56711610066578063313ce5671461022557806370a082311461024357806395d89b411461029b578063a9059cbb1461031e578063dd62ed3e1461038457610093565b806306fdde0314610098578063095ea7b31461011b57806318160ddd1461018157806323b872dd1461019f575b600080fd5b6100a06103fc565b6040518080602001828103825283818151815260200191508051906020019080838360005b838110156100e05780820151818401526020810190506100c5565b50505050905090810190601f16801561010d5780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b6101676004803603604081101561013157600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff1690602001909291908035906020019092919050505061049e565b604051808215151515815260200191505060405180910390f35b6101896104b5565b6040518082815260200191505060405180910390f35b61020b600480360360608110156101b557600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190803573ffffffffffffffffffffffffffffffffffffffff169060200190929190803590602001909291905050506104bf565b604051808215151515815260200191505060405180910390f35b61022d6105bf565b6040518082815260200191505060405180910390f35b6102856004803603602081101561025957600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff1690602001909291905050506105d9565b6040518082815260200191505060405180910390f35b6102a3610621565b6040518080602001828103825283818151815260200191508051906020019080838360005b838110156102e35780820151818401526020810190506102c8565b50505050905090810190601f1680156103105780820380516001836020036101000a031916815260200191505b509250505060405180910390f35b61036a6004803603604081101561033457600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190803590602001909291905050506106c3565b604051808215151515815260200191505060405180910390f35b6103e66004803603604081101561039a57600080fd5b81019080803573ffffffffffffffffffffffffffffffffffffffff169060200190929190803573ffffffffffffffffffffffffffffffffffffffff1690602001909291905050506106da565b6040518082815260200191505060405180910390f35b606060048054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156104945780601f1061046957610100808354040283529160200191610494565b820191906000526020600020905b81548152906001019060200180831161047757829003601f168201915b5050505050905090565b60006104ab338484610761565b6001905092915050565b6000600254905090565b60006104cc8484846108f3565b6000600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050828110156105a6576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526028815260200180610be76028913960400191505060405180910390fd5b6105b38533858403610761565b60019150509392505050565b6000600360009054906101000a900460ff1660ff16905090565b60008060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020549050919050565b606060058054600181600116156101000203166002900480601f0160208091040260200160405190810160405280929190818152602001828054600181600116156101000203166002900480156106b95780601f1061068e576101008083540402835291602001916106b9565b820191906000526020600020905b81548152906001019060200180831161069c57829003601f168201915b5050505050905090565b60006106d03384846108f3565b6001905092915050565b6000600160008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054905092915050565b600073ffffffffffffffffffffffffffffffffffffffff168373ffffffffffffffffffffffffffffffffffffffff1614156107e7576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526024815260200180610c346024913960400191505060405180910390fd5b600073ffffffffffffffffffffffffffffffffffffffff168273ffffffffffffffffffffffffffffffffffffffff16141561086d576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526022815260200180610b9f6022913960400191505060405180910390fd5b80600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550505050565b600073ffffffffffffffffffffffffffffffffffffffff168373ffffffffffffffffffffffffffffffffffffffff161415610979576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526025815260200180610c0f6025913960400191505060405180910390fd5b600073ffffffffffffffffffffffffffffffffffffffff168273ffffffffffffffffffffffffffffffffffffffff1614156109ff576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526023815260200180610b7c6023913960400191505060405180910390fd5b60008060008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054905060008060008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054905082811015610ade576040517f08c379a0000000000000000000000000000000000000000000000000000000008152600401808060200182810382526026815260200180610bc16026913960400191505060405180910390fd5b6000838203905060008484019050816000808973ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002081905550806000808873ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055505050505050505056fe45524332303a207472616e7366657220746f20746865207a65726f206164647265737345524332303a20617070726f766520746f20746865207a65726f206164647265737345524332303a207472616e7366657220616d6f756e7420657863656564732062616c616e636545524332303a207472616e7366657220616d6f756e74206578636565647320616c6c6f77616e636545524332303a207472616e736665722066726f6d20746865207a65726f206164647265737345524332303a20617070726f76652066726f6d20746865207a65726f2061646472657373a2646970667358221220d9dbe8fd9e7d5689c52fd8b9b4de4db7247eaa892108b2173084639672f6bc1564736f6c63430006070033")

 // deposit lemmas
 // --------------

    rule         255 &Int X <Int 256 => true requires 0 <=Int X [simplification, smt-lemma]
    rule 0 <=Int 255 &Int X          => true requires 0 <=Int X [simplification, smt-lemma]

endmodule
```

K Specifications
----------------

Formal specifications (using KEVM) of the correctness properties for our Solidity code.

```k
module ERC20-SPEC
    imports VERIFICATION
```

### Calling decimals() works

-   Everything from `<mode>` to `<callValue>` is boilerplate.
-   We are setting `<callData>` to `decimals()`.
-   We ask the prover to show that in all cases, we will end in `EVMC_SUCCESS` (rollback) when this happens.
-   The `<output>` cell specifies that we correctly lookup the `DECIMALS` value from the account storage.

```
    claim [decimals]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("decimals", .TypedArgs) </callData>
          <k>          #execute   => #halt ...            </k>
          <output>     .ByteArray => #buf(32, DECIMALS)   </output>
          <statusCode> _          => EVMC_SUCCESS         </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires DECIMALS ==Int 255 &Int #lookup(ACCT_STORAGE,  #hashedLocation("Solidity", 3, .IntList))
```

### Calling totalSupply() works

-   Everything from `<mode>` to `<callValue>` is boilerplate.
-   We are setting `<callData>` to `totalSupply()`.
-   We ask the prover to show that in all cases, we will end in `EVMC_SUCCESS` (rollback) when this happens.
-   The `<output>` cell specifies that we correctly lookup the `TS` value from the account storage.


```
    claim [totalSupply]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData> #abiCallData("totalSupply", .TypedArgs) </callData>
          <k>          #execute   => #halt ...            </k>
          <output>     .ByteArray => #buf(32, TS)         </output>
          <statusCode> _          => EVMC_SUCCESS         </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires TS ==Int #lookup(ACCT_STORAGE,  #hashedLocation("Solidity", 2, .IntList))
```

### Calling Approve works

-   Everything from `<mode>` to `<substate>` is boilerplate.
-   We are setting `<callData>` to `approve(SPENDER, AMOUNT)`.
-   We ask the prover to show that in all cases, we will end in `EVMC_SUCCESS` (rollback) when SENDER or OWNER is not address(0), and that we will end in `EVMC_REVERT` when either one of them is.
-   We take the OWNER from the `<caller>` cell, which is the `msg.sender`.
-   The `<output>` should be `#buf(32, bool2Word(True))` if the function does not revert.
-   The storage locations for Allowance should be updated accordingly.

```
    claim [approve.success]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>
          <static>    false                                 </static>

          <id>         ACCTID      => ?_ </id>
          <caller>     OWNER       => ?_ </caller>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <substate> _             => ?_ </substate>


          <callData> #abiCallData("approve", #address(SPENDER), #uint256(AMOUNT)) </callData>
          <k>          #execute   => #halt ...            </k>
          <output>     .ByteArray => #buf(32, 1)          </output>
          <statusCode> _          => EVMC_SUCCESS         </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE
                   => ACCT_STORAGE [ALLOWANCE_KEY <- AMOUNT]
            </storage>
            ...
          </account>

       requires ALLOWANCE_KEY ==Int #hashedLocation("Solidity", 1, OWNER SPENDER .IntList)
        andBool #rangeAddress(OWNER)
        andBool #rangeAddress(SPENDER)
        andBool #rangeUInt(256, AMOUNT)
        andBool OWNER =/=Int 0
        andBool SPENDER =/=Int 0
```

```
    claim [approve.revert]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                 </callStack>
          <program>   #binRuntime()                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime()) </jumpDests>
          <static>    false                                 </static>

          <id>         ACCTID      => ?_ </id>
          <caller>     OWNER       => ?_ </caller>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <substate> _             => ?_ </substate>

          <callData> #abiCallData("approve", #address(SPENDER), #uint256(AMOUNT)) </callData>
          <k>          #execute   => #halt ...   </k>
          <output>     _          => ?_          </output>
          <statusCode> _          => EVMC_REVERT </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> _ACCT_STORAGE </storage>
            ...
          </account>

       requires #rangeAddress(OWNER)
        andBool #rangeAddress(SPENDER)
        andBool #rangeUInt(256, AMOUNT)
        andBool (OWNER ==Int 0 orBool SPENDER ==Int 0)
```


Tests for deposit lemmas:

```
    claim <k> runLemma( #range (_:ByteArray [ 128 := #padToWidth ( 32 , #asByteStack ( 255 &Int #lookup ( ACCT_STORAGE , 3 ) ) ) ] , 128 , 32 ))
           => doneLemma(#padToWidth ( 32 , #asByteStack ( 255 &Int #lookup ( ACCT_STORAGE , 3 ) ) )) ... </k>
```

```k
endmodule
```
