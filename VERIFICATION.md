Verification Instructions for KEVM
==================================

Assuming that KEVM is successfully installed.


example 1: sum-to-n.k
---------------------

```
kevm kompile sum-to-n-spec.k --pyk --backend haskell --syntax-module VERIFICATION --main-module VERIFICATION --definition sum-to-n-spec/haskell
kevm prove sum-to-n-spec.k --backend haskell --definition sum-to-n-spec/haskell
```

example 2: erc20-spec.md
------------------------
```
kevm solc-to-k tests/specs/examples/ERC20.sol ERC20 --pyk --main-module ERC20-VERIFICATION > erc20-bin-runtime.k 
```

- `solc-to-k` will parse a Solidity contract and generate a helper K module.
    -`--main-module` is used to set the name of the module.

```
kevm kompile erc20-spec.md --pyk --backend haskell --main-module VERIFICATION --definition erc20-spec/haskell

kevm prove erc20-spec.md --backend haskell  --definition erc20-spec/haskell --pyk --claim ERC20-SPEC.decimals
```
