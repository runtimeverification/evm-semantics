forge build
kevm foundry-kompile --verbose --regen --with-llvm-library --require lemmas1.k --module-import ArrayTest:LEMMAS1
kevm foundry-prove --test ArrayTest.testArrayInitialization --verbose --reinit --kore-rpc-command "kore-rpc-booster --simplify-after-exec --llvm-backend-library out/kompiled-llvm/interpreter.so" --bug-report

