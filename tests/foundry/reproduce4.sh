forge build
kevm foundry-kompile --verbose --regen --with-llvm-library --require lemmas4.k --module-import ArrayTest:LEMMAS4
# note: --simplify-after-exec is not needed
kevm foundry-prove --reinit --test ArrayTest.testArrayInitialization --kore-rpc-command "kore-rpc-booster --llvm-backend-library out/kompiled-llvm/interpreter.so" --verbose --bug-report
