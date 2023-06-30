run_kompile() {
    kevm foundry-kompile --verbose      \
         --require ${lemmas}            \
         --regen                        \
         --module-import ${module}      \
         --syntax-module ${base_module}
}

run_claim() {
    kevm prove ${lemmas}                     \
        --claim ${base_module}-SPEC.${claim} \
        --definition out/kompiled            \
        --spec-module ${base_module}-SPEC    \
        --verbose
}

lemmas=claims.k
base_module=RUN-LEMMA
module=AssumeTest:${base_module}
claim=should-pass

run_kompile
run_claim
