#!/usr/bin/env bash

set -xueo pipefail

foundry_args=(--foundry-project-root tests/foundry --verbose)
test=UintTypeTest.test_uint256

( cd tests/foundry && forge build ; )                             >&2
kevm foundry-kompile "${foundry_args[@]}"                         >&2
kevm foundry-prove "${foundry_args[@]}" --test ${test} --depth 40 >&2 || true

kevm foundry-list "${foundry_args[@]}"
kevm foundry-show "${foundry_args[@]}" ${test} --node '151838..8b4053' \
    --to-module --omit-unstable-output --frontier --stuck              \
    grep --invert-match -e 'rule \[BASIC-BLOCK-' -e '\[priority(.*), label(BASIC-BLOCK-'
