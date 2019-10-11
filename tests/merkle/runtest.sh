#!/usr/bin/env bash

set -euo pipefail

K_BIN=./deps/k/k-distribution/bin
MERKLE_DIR=./.build/defn/merkle

input_file="$1"  ; shift
output_file="$1" ; shift

$K_BIN/krun --directory "$MERKLE_DIR" "$input_file" > "$output_file"
