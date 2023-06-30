#!/usr/bin/env bash

set -xueo pipefail

which kevm
kevm help
kevm version

kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json --backend llvm \
    --mode VMTESTS --schedule DEFAULT --chainid 1                                                          \
    > tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.llvm-out          \
    || git --no-pager diff --no-index --ignore-all-space -R tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.llvm-out tests/templates/output-success-llvm.json
rm -rf tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.llvm-out

kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmSystemOperations/TestNameRegistrator.json \
    --backend llvm --mode VMTESTS --schedule DEFAULT --chainid 1 --pyk

kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmSystemOperations/TestNameRegistrator.json \
    --backend haskell-standalone --mode VMTESTS --schedule DEFAULT --chainid 1 --pyk

kevm kast tests/interactive/log3_MaxTopic_d0g0v0.json --pyk --backend llvm > tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out
git --no-pager diff --no-index --ignore-all-space -R tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out tests/interactive/log3_MaxTopic_d0g0v0.json.parse-expected
rm tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out

# This test currently segfaults on M1 Macs
if ! ${APPLE_SILICON:-false}; then
    kevm run tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json --backend llvm \
        --mode NORMAL --schedule BERLIN --chainid 1                                               \
        > tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out          \
        || git --no-pager diff --no-index --ignore-all-space -R tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.expected
    rm -rf tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out
fi


kevm solc-to-k tests/specs/examples/ERC20.sol ERC20 --main-module ERC20-VERIFICATION > tests/specs/examples/erc20-bin-runtime.k
kevm kompile tests/specs/examples/erc20-spec.md                 \
    --target haskell                                            \
    --output-definition tests/specs/examples/erc20-spec/haskell \
    --main-module VERIFICATION                                  \
    --syntax-module VERIFICATION                                \
    --verbose
# This test is probably too long for public Github runner and currently seems broken
if ! ${NIX:-false}; then
kevm prove tests/specs/examples/erc20-spec.md --backend haskell --format-failures  \
    --definition tests/specs/examples/erc20-spec/haskell
fi
