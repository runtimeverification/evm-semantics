#!/usr/bin/env bash

KEVM_PREFIX=/nix/store/z30l75z7l3m2nynf52n13cwqz2586rb1-kevm-8ed6754edb8e7e8cadbcaa1fa08f255241dd34b6/
echo 'Kompiling'
kevm-pyk kompile --read-only-kompiled-directory --target haskell --definition "$KEVM_PREFIX/lib/kevm/haskell" --syntax-module VERIFICATION-SYNTAX --main-module VERIFICATION ./tests/specs/mcd/vat-frob-diff-zero-dart-pass-rough-reuse-spec.k -o frob-out.d


echo 'Proving'
kevm-pyk prove --verbose --workers 4 --definition frob-out.d/ -I include/kframework/ -I "$KEVM_PREFIX/lib/kevm/include/kframework/" ./tests/specs/mcd/vat-frob-diff-zero-dart-pass-rough-reuse-spec.k --save-directory ./frob-save.d
