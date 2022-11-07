#!/usr/bin/env bash

set -xueo pipefail

forge build                                                        >&2
kevm foundry-kompile out                                           >&2
kevm foundry-prove out --test UintTypeTest.test_uint256 --depth 40 >&2

kevm foundry-list out
kevm foundry-show out UintTypeTest.test_uint256
