.PHONY: proof-test-all proof-test split-proof-tests

erc20_files:=totalSupply-spec.k \
             balanceOf-spec.k \
             allowance-spec.k \
             approve-spec.k \
             transfer-success-1-spec.k \
             transfer-success-2-spec.k \
             transfer-failure-1-spec.k \
             transfer-failure-2-spec.k \
             transferFrom-success-1-spec.k \
             transferFrom-success-2-spec.k \
             transferFrom-failure-1-spec.k \
             transferFrom-failure-2-spec.k

hobby_erc20_files:=totalSupply-spec.k \
                   balanceOf-spec.k \
                   allowance-spec.k \
                   approve-success-spec.k \
                   approve-failure-spec.k \
                   transfer-success-1-spec.k \
                   transfer-success-2-spec.k \
                   transfer-failure-1-spec.k \
                   transfer-failure-2-spec.k \
                   transferFrom-success-1-spec.k \
                   transferFrom-success-2-spec.k \
                   transferFrom-failure-1-spec.k \
                   transferFrom-failure-2-spec.k

proof_dir:=tests
proof_tests:=$(proof_dir)/sum-to-n-spec.k \
			 $(patsubst %, $(proof_dir)/erc20/viper/%, $(erc20_files)) \
			 $(patsubst %, $(proof_dir)/erc20/zeppelin/%, $(erc20_files)) \
			 $(patsubst %, $(proof_dir)/erc20/hkg/%, $(erc20_files)) \
			 $(patsubst %, $(proof_dir)/erc20/hobby/%, $(hobby_erc20_files))

proof-test-all: proof-test
proof-test: $(proof_tests:=.test)

tests/%.test: tests/%
	$(TEST) $<

split-proof-tests: $(proof_tests)

# #### Sum to N
tests/sum-to-n-spec.k: sum-to-n.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(tangler)" --metadata="code:.sum-to-n" $< > $@

# #### ERC20
tests/erc20/viper/%-spec.k: erc20/tmpl.k erc20/viper/spec-viper.ini erc20/viper/pgm-viper.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 gen-spec.py $^ $* > $@

tests/erc20/zeppelin/%-spec.k: erc20/tmpl.k erc20/zeppelin/spec-zeppelin.ini erc20/zeppelin/pgm-zeppelin.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 gen-spec.py $^ $* > $@

tests/erc20/hkg/%-spec.k: erc20/tmpl.k erc20/hkg/spec-hkg.ini erc20/hkg/pgm-hkg.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 gen-spec.py $^ $* > $@

tests/erc20/hobby/%-spec.k: erc20/tmpl.k erc20/hobby/spec-hobby.ini erc20/hobby/pgm-hobby.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 gen-spec.py $^ $* > $@
