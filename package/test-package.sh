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

kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json --backend haskell \
    --mode VMTESTS --schedule DEFAULT --chainid 1                                                             \
    > tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.haskell-out          \
    || git --no-pager diff --no-index --ignore-all-space -R tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.haskell-out tests/templates/output-success-haskell.json
rm -rf tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json.haskell-out

kevm kast tests/interactive/log3_MaxTopic_d0g0v0.json kast  --backend llvm > tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out
git --no-pager diff --no-index --ignore-all-space -R tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out tests/interactive/log3_MaxTopic_d0g0v0.json.parse-expected
rm -rf tests/interactive/log3_MaxTopic_d0g0v0.json.parse-out

kevm run tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json --backend llvm \
    --mode NORMAL --schedule BERLIN --chainid 1                                               \
    > tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out          \
    || git --no-pager diff --no-index --ignore-all-space -R tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.expected
rm -rf tests/failing/static_callcodecallcodecall_110_OOGMAfter_2_d0g0v0.json.llvm-out

kevm solc tests/specs/examples/ERC20.sol ERC20 > tests/specs/examples/erc20-bin-runtime.k
kevm kompile --backend haskell tests/specs/examples/erc20-spec.md \
    --directory tests/specs/examples/erc20-spec/haskell           \
    --main-module VERIFICATION                                    \
    --syntax-module VERIFICATION                                  \
    --concrete-rules-file tests/specs/examples/concrete-rules.txt \
    --verbose
kevm prove tests/specs/examples/erc20-spec.md --backend haskell --format-failures  \
    --directory tests/specs/examples/erc20-spec/haskell

kevm kompile --backend java tests/specs/erc20/verification.k   \
    --directory tests/specs/erc20/verification/java            \
    --main-module VERIFICATION                                 \
    --syntax-module VERIFICATION                               \
    --concrete-rules-file tests/specs/erc20/concrete-rules.txt \
    --debug
kevm prove tests/specs/erc20/ds/transfer-failure-1-a-spec.k --backend java --format-failures --debugger \
    --directory tests/specs/erc20/verification/java

kevm search tests/interactive/search/branching-invalid.evm "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>"  --backend haskell > tests/interactive/search/branching-invalid.evm.search-out
git --no-pager diff --no-index --ignore-all-space -R tests/interactive/search/branching-invalid.evm.search-out tests/interactive/search/branching-invalid.evm.search-expected
rm -rf tests/interactive/search/branching-invalid.evm.search-out
