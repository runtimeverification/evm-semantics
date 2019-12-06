#!/usr/bin/env bash

set -euo pipefail

input_file="$1"  ; shift
output_file="$1" ; shift

# Start Firefly
PORT=$(tests/web3/get_port.py)
./kevm web3 "$PORT" "$@" &
kevm_client_pid="$!"
while ! netcat -z 127.0.0.1 "$PORT"; do sleep 0.1; done

# Feed input in, store output in supplied file
#[TODO]
curl -i -X POST 127.0.0.1:"$PORT" --data @"$input_file" | jq . > "$output_file"

./kevm web3-send "$PORT" 'firefly_shutdown'
echo
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
pkill -P "$kevm_client_pid" kevm-client              || true
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
