#!/usr/bin/env bash

#echo 'Kompiling'
kevm-pyk kompile --read-only-kompiled-directory --target haskell --definition /nix/store/92vnpsq4aq2p9idmrw0gb2rvlbycjpnj-kevm-71ab7861f509061bbf72b9c6f8baeca6f2b9ecda/lib/kevm/haskell --syntax-module VERIFICATION-SYNTAX --main-module VERIFICATION ./tests/specs/mcd/vat-frob-diff-zero-dart-pass-rough-reuse-spec.k -o frob-out.d

echo 'Proving'
kevm-pyk prove --max-iterations 1 --verbose --workers 4 --definition frob-out.d/ -I include/kframework/ -I /nix/store/92vnpsq4aq2p9idmrw0gb2rvlbycjpnj-kevm-71ab7861f509061bbf72b9c6f8baeca6f2b9ecda/lib/kevm/include/kframework/ ./tests/specs/mcd/vat-frob-diff-zero-dart-pass-rough-reuse-spec.k --save-directory ./frob-save.d
