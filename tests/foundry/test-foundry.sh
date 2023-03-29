#!/usr/bin/env bash

set -xueo pipefail

forge build                                                                                         >&2
kevm foundry-kompile --foundry-project-root tests/foundry                                           >&2
kevm foundry-prove --foundry-project-root tests/foundry --test UintTypeTest.test_uint256 --depth 40 >&2 || true

kevm foundry-list --foundry-project-root tests/foundry
kevm foundry-show --foundry-project-root tests/foundry UintTypeTest.test_uint256 --node '151838..8b4053' \
    --to-module --omit-unstable-output --frontier --stuck                                            \
    grep --invert-match -e 'rule \[BASIC-BLOCK-' -e '\[priority(.*), label(BASIC-BLOCK-'
