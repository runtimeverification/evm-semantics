#!/usr/bin/env bash

set -xueo pipefail

which kevm
kevm --help
kevm version

kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json --target llvm \
    --mode VMTESTS --schedule DEFAULT --chainid 1                                                         \
    > tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.llvm-out         \
    || git --no-pager diff --no-index --ignore-all-space -R tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.llvm-out tests/templates/output-success-llvm.json
rm -rf tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.llvm-out

kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmSystemOperations/TestNameRegistrator.json \
    --target llvm --mode VMTESTS --schedule DEFAULT --chainid 1

kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmSystemOperations/TestNameRegistrator.json \
    --target haskell-standalone --mode VMTESTS --schedule DEFAULT --chainid 1

kevm kast tests/interactive/log3_MaxTopic_d0g0v0.json --target llvm > tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out
git --no-pager diff --no-index --ignore-all-space -R tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out tests/interactive/log3_MaxTopic_d0g0v0.json.parse-expected
rm tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out

# This test currently segfaults on M1 Macs
if ! ${APPLE_SILICON:-false}; then
    kevm run tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json --target llvm \
        --mode NORMAL --schedule BERLIN --chainid 1                                              \
        > tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out         \
        || git --no-pager diff --no-index --ignore-all-space -R tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.expected
    rm -rf tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out
fi


kontrol solc-to-k tests/specs/examples/ERC20.sol ERC20 --target haskell --main-module ERC20-VERIFICATION > tests/specs/examples/erc20-bin-runtime.k
kevm kompile tests/specs/examples/erc20-spec.md                 \
    --target haskell                                            \
    --output-definition tests/specs/examples/erc20-spec/haskell \
    --main-module VERIFICATION                                  \
    --syntax-module VERIFICATION                                \
    --verbose
kevm prove tests/specs/examples/erc20-spec.md --definition tests/specs/examples/erc20-spec/haskell

# Commented because of https://github.com/foundry-rs/foundry/issues/545, and we can't install solc 0.8.13
# forge build --root tests/foundry --no-auto-detect
# kevm foundry-kompile --foundry-project-root tests/foundry --verbose
# kevm foundry-prove --foundry-project-root tests/foundry --verbose --test AssertTest.test_assert_true_branch
