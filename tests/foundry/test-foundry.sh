#!/usr/bin/env bash

set -xueo pipefail

forge build
kevm foundry-kompile out
kevm foundry-prove out --test UintTypeTest.test_uint256 --depth 40
kevm foundry-list out
kevm foundry-show out UintTypeTest.test_uint256 &> cfg.out
cp cfg.out cfg.expected
