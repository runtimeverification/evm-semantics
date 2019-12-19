#!/usr/bin/env bash

set -euo pipefail

# install openzeppelin-contracts
echo $(pwd)
cd deps
git clone 'https://github.com/OpenZeppelin/openzeppelin-contracts'
cd openzeppelin-contracts
git checkout fbddf5ba5b76bba8638bb811e7183c1eba8e6ed3
npm install
node_modules/.bin/truffle compile
cd ../..

# launch test-runner
PORT=8545
./kevm web3-ganache "$PORT" --shutdownable &
kevm_client_pid="$!"

# run OpenZeppelin tests
cd deps/openzeppelin-contracts
while (! netcat -z 127.0.0.1 "$PORT") ; do sleep 0.1; done
node_modules/.bin/truffle test test/token/ERC20/ERC20Detailed.test.js
cd ../..

# close test-runner
./kevm web3-send "$PORT" 'firefly_shutdown'
echo
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
pkill -P "$kevm_client_pid" kevm-client              || true
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true