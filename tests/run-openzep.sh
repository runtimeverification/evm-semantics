#!/usr/bin/env bash

set -euo pipefail

test_dir="tests/openzeppelin-contracts/"
test_file="$1" ; shift
# launch test-runner
PORT=8545

while (netcat -z 127.0.0.1 "$PORT") ; do sleep 0.1; done

./kevm web3-ganache "$PORT" --shutdownable &
kevm_client_pid="$!"

while (! netcat -z 127.0.0.1 "$PORT") ; do sleep 0.1; done

pushd "$test_dir"
node_modules/.bin/truffle test "$test_file"
popd

# close test-runner
./kevm web3-send "$PORT" 'firefly_shutdown'
echo
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || \
pkill -P "$kevm_client_pid" kevm-client              || \
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
