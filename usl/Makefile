DEF_KOMPILED=$(shell poetry -C ../kevm-pyk run kdist which evm-semantics.llvm)
LLVM_KOMPILE=llvm-kompile

USL_LIB_NAME=libuslkevm.so
$(USL_LIB_NAME): usl_kevm.cpp usl_kevm.h
	$(LLVM_KOMPILE) $(DEF_KOMPILED)/definition.kore $(DEF_KOMPILED)/dt c -- -o $@ $<

clean:
	rm -rf $(USL_LIB_NAME)
