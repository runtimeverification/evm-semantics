#!/usr/bin/env bash

set -euxo pipefail

submodule_version="$1" ; shift
cat kevm_pyk/setup.cfg.tmpl | sed 's/\${K_COMMIT}/'"${submodule_version}"'/' > kevm_pyk/setup.cfg
