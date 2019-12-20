#!/usr/bin/env bash

set -euo pipefail

test_dir="$1" ; shift

# launch test-runner
PORT=8485
./kevm web3-ganache "$PORT" --shutdownable &
kevm_client_pid="$!"

while (! netcat -z 127.0.0.1 "$PORT") ; do sleep 0.1; done

pushd "$test_dir"
npx run truffle test
popd

# close test-runner
./kevm web3-send "$PORT" 'firefly_shutdown'
echo
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
pkill -P "$kevm_client_pid" kevm-client              || true
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
