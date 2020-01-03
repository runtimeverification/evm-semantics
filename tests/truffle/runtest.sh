#!/usr/bin/env bash

set -euo pipefail

test_dir="$1" ; shift
# launch test-runner
PORT=$(cat "$test_dir"truffle-config.js | grep 'port:' | cut --delimiter ':' --field '2' | cut --delimiter ',' --field '1' || echo "8545" )

./kevm web3-ganache "$PORT" --shutdownable &
kevm_client_pid="$!"

while (! netcat -z 127.0.0.1 "$PORT") ; do sleep 0.1; done

pushd "$test_dir"
npm install || true
node_modules/.bin/truffle test
popd

# close test-runner
./kevm web3-send "$PORT" 'firefly_shutdown'
echo
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
pkill -P "$kevm_client_pid" kevm-client              || true
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
