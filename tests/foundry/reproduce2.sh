forge build
kevm foundry-kompile --verbose --regen --with-llvm-library --require lemmas2.k --module-import ArrayTest:LEMMAS2
kevm foundry-prove --test ArrayTest.testArrayInitialization --verbose --reinit --kore-rpc-command "kore-rpc-booster --simplify-after-exec --llvm-backend-library out/kompiled-llvm/interpreter.so" --bug-report
