#!/usr/bin/env bash

set -euxo pipefail

submodule_version="$1" ; shift
kevm_pyk_version="$(cat kevm_pyk/setup.cfg | grep 'pyk @ git' | cut --delimiter='@' --field=3 | cut --delimiter='#' --field=1)"

[[ "${submodule_version}" == "${kevm_pyk_version}" ]]
