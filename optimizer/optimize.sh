#!/usr/bin/env bash

set -euo pipefail

export PATH=$(pwd)/.build/usr/bin:$PATH
export PYTHONPATH=$(pwd)/.build/usr/lib/kevm/kframework/lib/kframework

kevm_json_defn=$(pwd)/.build/usr/lib/kevm/llvm/driver-kompiled/compiled.json

notif() { echo "$@" >&2 ; }

buildWordStack() {
    local number wordstack i

    number="$1" ; shift

    wordstack="WS"
    for i in $(seq 0 $((number - 1)) | tac); do
        wordstack="W${i} : ${wordstack}"
    done
    echo "${wordstack}"
}

buildSpec() {
    local opcode wordstack_number wordstack module extra_requires

    opcode="$1"           ; shift
    wordstack_number="$1" ; shift

    wordstack="$(buildWordStack ${wordstack_number})"
    module="$(echo ${opcode} | tr -d '()')"

    extra_requires=''
    while [[ "$#" -gt '0' ]]; do
        extra_requires="${extra_requires} andBool ( ${1} )"
        shift
    done

    cat optimizer/optimize-spec.k.tmpl                 \
        | sed "s/{EXTRA_REQUIRES}/${extra_requires}/g" \
        | sed "s/{MODULE}/${module}/g"                 \
        | sed "s/{OPCODE}/${opcode}/g"                 \
        | sed "s/{WORD_STACK}/${wordstack}/g"
}

inject_optimization() {
    local search_string contents_file

    contents_file="$1" ; shift

    search_string='// {OPTIMIZATIONS}'
    (   IFS=''
        while read line; do
            if [[ "${line}" == "${search_string}" ]]; then
                cat "${contents_file}"
                echo "${line}"
            else
                echo "${line}"
            fi
        done
    )
}

runProve() {
    local spec

    spec="$1" ; shift

    kevm prove --backend haskell ${spec} OPTIMIZE --concrete-rules-file tests/specs/mcd/concrete-rules.txt "$@"
}

doOptimization() {
    local opcode wordstack_number depth opcode_lower spec_file json_out claim_file rule_file optimize_file

    opcode="$1"           ; shift
    wordstack_number="$1" ; shift
    depth="$1"            ; shift
    priority="$1"         ; shift

    opcode_lower="$(echo ${opcode} | tr '[:upper:]' '[:lower:]' | tr -d '()')"
    spec_file="optimizer/${opcode_lower}-spec.k"
    json_out="optimizer/${opcode_lower}.out.json"
    claim_file="optimizer/${opcode_lower}-claim.k"
    rule_file="optimizer/${opcode_lower}.k"
    optimize_file="optimizer/optimize-spec.k"

    make build-haskell build-lemmas -j8

    notif "Building: ${spec_file}"
    buildSpec "${opcode}" "${wordstack_number}" "$@" > "${spec_file}"

    notif "Building: ${json_out}"
    runProve "${spec_file}" --depth "${depth}" --output json | jq . > "${json_out}" || true

    notif "Building: ${claim_file}"
    ./optimizer/build-spec.py "${kevm_json_defn}" "${opcode}" "${wordstack_number}" "${json_out}" "$@" > "${claim_file}"

    notif "Building: ${rule_file}"
    cat "${claim_file}" | sed 's/^claim /rule /g' | sed '/^[[:space:]]*$/d'  > "${rule_file}"
    echo "    [priority(${priority})]"                                      >> "${rule_file}"
    echo                                                                    >> "${rule_file}"
    echo                                                                    >> "${rule_file}"

    notif "Building: ${optimize_file}"
    echo 'requires "lemmas/mcd/verification.k"'  > "${optimize_file}"
    echo ''                                     >> "${optimize_file}"
    echo 'module OPTIMIZE'                      >> "${optimize_file}"
    echo '    imports INT'                      >> "${optimize_file}"
    echo '    imports LEMMAS-MCD'               >> "${optimize_file}"
    echo '    imports EVM'                      >> "${optimize_file}"
    echo 'endmodule'                            >> "${optimize_file}"
    echo ''                                     >> "${optimize_file}"
    echo "module OPTIMIZE-SPEC"                 >> "${optimize_file}"
    echo '    imports OPTIMIZE'                 >> "${optimize_file}"
    echo ''                                     >> "${optimize_file}"
    cat "${claim_file}"                         >> "${optimize_file}"
    echo ''                                     >> "${optimize_file}"
    echo 'endmodule'                            >> "${optimize_file}"

    if runProve "${optimize_file}"; then
        notif "Claim passed: ${opcode}"
        cat optimizations.md | inject_optimization "${rule_file}" > optimizations.md.tmp
        cp optimizations.md.tmp optimizations.md
        git add optimizations.md
        git commit -m "optimizations: optimize ${opcode} ${priority}"
    else
        notif "Claim failed: ${opcode}"
    fi
}

cp optimizer/optimizations.md optimizations.md
git add optimizations.md
git commit -m 'optimizations: clear optimizations' || true

# score: (number with speedup >7%) - (number with slowdown >7%)
doOptimization "PUSH(N)"  0 10 40                                                       # 73
doOptimization "DUP(N)"   0 10 40 '#stackNeeded(DUP(N)) <=Int #sizeWordStack(WS)'       # 14
doOptimization "SWAP(N)"  1 10 40 '#stackNeeded(SWAP(N)) <=Int #sizeWordStack(W0 : WS)' # 14
doOptimization ADD        2 10 40                                                       # 8
doOptimization LT         2 10 40                                                       # 7
doOptimization POP        1 10 40                                                       # 5
doOptimization MULMOD     3 10 40                                                       # 1

doOptimization MSTORE8    2 14 40                                                       #  0
doOptimization SIGNEXTEND 2 10 40                                                       #  0
doOptimization SGT        2 10 40                                                       #  ?
doOptimization SLT        2 10 40                                                       #  ?
doOptimization GT         2 10 40                                                       #  ?
doOptimization EVMOR      2 10 40                                                       #  ?
doOptimization MOD        2 10 40                                                       #  ?
doOptimization SUB        2 10 40                                                       #  ?
doOptimization DIV        2 10 40                                                       #  ?
doOptimization AND        2 10 40                                                       #  ?
doOptimization ADDMOD     3 10 40                                                       # -1
doOptimization EQ         2 10 40                                                       # -1
doOptimization MUL        2 10 40                                                       # -1
doOptimization ISZERO     1 10 40                                                       # -3
doOptimization NOT        1 10 40                                                       # -4
doOptimization XOR        2 10 40                                                       # -9
doOptimization MLOAD      1 14 40                                                       # -9
doOptimization MSTORE     2 14 40                                                       # -18

# spec requires multiple branches
# doOptimization EXP 2 10

# could not prove the generated rule (involve non-total functions)
# doOptimization SDIV  2 10
# doOptimization SMOD  2 10
# doOptimization SHL   2 10
# doOptimization SHR   2 10
# doOptimization SAR   2 10
# doOptimization BYTE  2 10
# doOptimization SHA3  2 10

# could not prove the generated rule (involve cells that are not mentioned)
# doOptimization JUMP  1 10
# doOptimization JUMPI 2 10
