#!/usr/bin/env bash

set -xeuo pipefail

open_zeppelin_commit="b8c8308"
kevm_vm_port="8545"

npx kevm-ganache-cli --gasLimit 0xfffffffffff --port "$kevm_vm_port"                                       \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501200,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501201,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501202,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501203,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501204,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501205,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501206,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501207,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501208,1000000000000000000000000 \
    --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501209,1000000000000000000000000 \
    &

tmp_testing_dir="$(mktemp -d tests/firefly-node.XXXXXX)"
trap "rm -rf $tmp_testing_dir" INT TERM EXIT
cd "$tmp_testing_dir"

git clone 'https://github.com/openzeppelin/openzeppelin-solidity'
cd openzeppelin-solidity
git checkout "$open_zeppelin_commit"

npm install

# Wait for kevm-vm to start up
while ! netcat -z localhost "$kevm_vm_port"; do
    sleep 1
done

node_modules/.bin/truffle test
