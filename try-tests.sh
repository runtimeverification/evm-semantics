make -j8 -k TEST_SYMBOLIC_BACKEND=haskell                       \
    tests/specs/functional/merkle-spec.k.prove                  \
    tests/specs/functional/lemmas-no-smt-spec.k.prove           \
    tests/specs/functional/infinite-gas-spec.k.prove            \
    tests/specs/benchmarks/functional-spec.k.prove              \
    tests/specs/functional/lemmas-spec.k.prove                  \
    tests/specs/functional/storageRoot-spec.k.prove             \
    tests/specs/evm-optimizations-spec.mk.prove                 \
    tests/specs/examples/sum-to-n-spec.k.prove                  \
    tests/specs/erc20/hkg/totalSupply-spec.k.prove              \
    tests/specs/benchmarks/storagevar03-spec.k.prove            \
    tests/specs/benchmarks/storagevar00-spec.k.prove            \
    tests/specs/benchmarks/requires01-a0le0-spec.k.prove        \
    tests/specs/benchmarks/storagevar01-spec.k.prove            \
    tests/specs/benchmarks/storagevar02-overflow-spec.k.prove   \
    tests/specs/benchmarks/address00-spec.k.prove               \
    tests/specs/benchmarks/overflow00-overflow-spec.k.prove     \
    tests/specs/benchmarks/overflow00-nooverflow-spec.k.prove   \
    tests/specs/benchmarks/storagevar02-nooverflow-spec.k.prove \
    tests/specs/benchmarks/requires01-a0gt0-spec.k.prove        \
    tests/specs/benchmarks/encodepacked-keccak01-spec.k.prove   \
    tests/specs/benchmarks/staticarray00-spec.k.prove           \
    tests/specs/benchmarks/staticloop00-a0lt10-spec.k.prove     \
    tests/specs/erc20/ds/approve-failure-spec.k.prove           \
    tests/specs/benchmarks/encode-keccak00-spec.k.prove         \
    tests/specs/erc20/ds/totalSupply-spec.k.prove               \
    tests/specs/benchmarks/keccak00-spec.k.prove                \
    tests/specs/benchmarks/bytes00-spec.k.prove