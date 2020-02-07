#!/usr/bin/env bash

set -euo pipefail

folder_path="$1" ; shift

cat "$folder_path"/ERC20.json | jq '[.abi[] | {name:.name, type: .type, inputs:[.inputs[]]}]'
