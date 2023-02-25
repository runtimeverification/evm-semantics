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
kevm solc-to-k tests/specs/examples/ERC20.sol ERC20 --pyk --verbose --definition .build/usr/lib/kevm/haskell --main-module ERC20-VERIFICATION > tests/specs/
examples/erc20-bin-runtime.k 
```

Look at the bottom of the generated helper `erc20-bin-runtime.k` file.
If the second module has a different name than `ERC20-VERIFICATION` then replace the import `imports ERC20-VERIFICATION` in `erc20-spec.md` with the generated module.

```
kevm kompile erc20-spec.md --pyk --backend haskell --main-module VERIFICATION --definition erc20-spec/haskell

kevm prove erc20-spec.md --backend haskell  --definition erc20-spec/haskell --pyk --claim ERC20-SPEC.decimals
```