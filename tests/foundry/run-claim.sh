kevm foundry-kompile --verbose --regen --with-llvm-library --require lemmas1.k --module-import ArrayTest:LEMMAS1
kevm prove lemmas1.k --claim LEMMAS1-SPEC.lookup-equals-3 --definition out/kompiled --spec-module LEMMAS1-SPEC
