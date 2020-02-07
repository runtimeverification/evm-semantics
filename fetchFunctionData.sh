#!/usr/bin/env bash

set -euo pipefail

 # folder_path represents the absolute path to the compiled contracts folder
folder_path="$1" ; shift

data_format='{contractName: .contractName, functionData: [.abi[] | select(.type == "function") | {name: .name, input:[ .inputs[] |{name: .name, type:.type}], output:[.outputs[] |{name: .name, type:.type} ]}]}'
result='['
for filename in "$folder_path"/*.json ; do
    result+=$(cat "$filename" | jq "$data_format")
    result+=','
done
result=${result%?}
result+=']'
echo "$result" | jq '.'
