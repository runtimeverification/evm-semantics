#!/usr/bin/env bash

set -euo pipefail

input_file="$1"  ; shift
output_file="$1" ; shift

get_port() {
    python3 -c """
import socket

s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
s.bind(('', 0))
addr = s.getsockname()
print(str(addr[1]))
s.close()
"""
}

# Start Firefly
PORT=$(get_port)
./kevm web3 -p "$PORT" "$@" &
kevm_client_pid="$!"
while (! netcat -z 127.0.0.1 "$PORT") ; do sleep 0.1; done

# Feed input in, store output in supplied file
./kevm web3-send -p "$PORT" "$input_file" | jq . > "$output_file"
./kevm web3-send -p "$PORT" 'firefly_shutdown'

echo
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
pkill -P "$kevm_client_pid" kevm-client              || true
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
