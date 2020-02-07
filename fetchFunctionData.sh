#!/usr/bin/env bash

set -euo pipefail

folder_path="$1" ; shift

cat "$folder_path"/ERC20.json | jq '{contractName: .contractName, functionData: [.abi[] | select(.type == "function") | {name: .name, input:[ .inputs[] |{name: .name, type:.type}], output:[.outputs[] |{name: .name, type:.type} ]}]}'
