#!/usr/bin/env bash

set -euxo pipefail

K_COMMIT="$(cd deps/k && git tag --points-at HEAD | cut --characters=2-)"
cat kevm_pyk/setup.cfg.tmpl | sed 's/\${K_COMMIT}/'"${K_COMMIT}"'/' > kevm_pyk/setup.cfg
git add kevm_pyk/setup.cfg
! git commit -m "kevm_pyk/setup.cfg: update version to ${K_COMMIT}" || git push
