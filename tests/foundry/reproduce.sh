kevm foundry-kompile --verbose --require normalization-lemmas.k --module-import FreshIntTest:NORMALIZATION-LEMMAS --regen --with-llvm-library
kevm foundry-prove --test FreshIntTest.test_uint256 --verbose --reinit --kore-rpc-command "kore-rpc-booster --simplify-after-exec --llvm-backend-library out/kompiled-llvm/interpreter.so"
