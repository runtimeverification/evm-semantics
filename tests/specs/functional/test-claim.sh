#!/bin/bash

spec=lemmas-spec
main_module=VERIFICATION
spec_module=LEMMAS-SPEC
claim=${spec_module}.range-01

rm applied-rules.log
rm -rf ${spec}/haskell
kevm kompile --pyk --backend haskell ${spec}.k \
    --definition ${spec}/haskell \
    --main-module ${main_module} \
    --syntax-module ${main_module} \
    -I /usr/lib/kevm/include/kframework
KORE_EXEC_OPTS='--log applied.log --log-format oneline --log-entries DebugAppliedRewriteRules,DebugApplyEquation' kevm prove --verbose ${spec}.k --claims ${claim} --definition ${spec}/haskell --spec-module ${spec_module}