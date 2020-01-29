#!/usr/bin/env bash

set -euo pipefail

test_dir="tests/synthetix/"
test_file="$1" ; shift
# launch test-runner
PORT=8546

while (netcat -z 127.0.0.1 "$PORT") ; do sleep 0.1; done

./kevm web3 "$PORT" --shutdownable --respond-to-notifications &
kevm_client_pid="$!"

while (! netcat -z 127.0.0.1 "$PORT") ; do sleep 0.1; done

./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501200", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501201", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501202", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501203", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501204", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501205", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501206", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501207", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501208", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_addAccount '{"key":"0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501209", "balance":"0x56BC75E2D63100000"}'
./kevm web3-send "$PORT" firefly_setGasLimit '"0x7A1200"'
./kevm web3-send "$PORT" evm_increaseTime '1579773024'
./kevm web3-send "$PORT" firefly_genesisBlock

pushd "$test_dir"
node_modules/.bin/truffle test "$test_file"
popd

# close test-runner
./kevm web3-send "$PORT" 'firefly_shutdown'
echo
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || \
pkill -P "$kevm_client_pid" kevm-client              || \
timeout 8 tail --pid="$kevm_client_pid" -f /dev/null || true
