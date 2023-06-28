KEVM: Semantics of EVM in K
===========================

In this repository, we provide a model of the EVM in K.

Fast Installation
-----------------

-   `bash <(curl https://kframework.org/install)`: install [kup package manager].
-   `kup install kevm`: install KEVM.
-   `kup list kevm`: list available KEVM versions.
-   `kup update kevm`: update to latest KEVM version.

**NOTE**: The first run will take longer to fetch all the libraries and compile sources. (30m to 1h)

Documentation/Support
---------------------

These may be useful for learning KEVM and K (newest to oldest):

-   [K, KEVM and Foundry Integration overview](https://www.youtube.com/watch?v=9PLnQStkiUo)
-   [Jello Paper], a nice presentation of this repository.
-   [20 minute tour of the semantics](https://www.youtube.com/watch?v=tIq_xECoicQNov) at [2017 Devcon3].
-   [KEVM 1.0 technical report](http://hdl.handle.net/2142/97207), especially sections 3 and 5.
-   [KEVM Paper at CSF'18/FLoC](https://fsl.cs.illinois.edu/publications/hildenbrandt-saxena-zhu-rodrigues-daian-guth-moore-zhang-park-rosu-2018-csf).

To get support for KEVM, please join our [Discord Channel](https://discord.com/invite/CurfmXNtbN).

If you want to start proving with KEVM, refer to [VERIFICATION.md].

Repository Structure
--------------------

The following files constitute the KEVM semantics:

-   [network.md](include/kframework/network.md) provides the status codes reported to an Ethereum client on execution exceptions.
-   [json-rpc.md](include/kframework/json-rpc.md) is an implementation of JSON RPC in K.
-   [evm-types.md](include/kframework/evm-types.md) provides the (functional) data of EVM (256-bit words, wordstacks, etc...).
-   [serialization.md](include/kframework/serialization.md) provides helpers for parsing and unparsing data (hex strings, recursive-length prefix, Merkle trees, etc.).
-   [evm.md](include/kframework/evm.md) is the main KEVM semantics, containing EVM’s configuration and transition rules.
-   [gas.md](include/kframework/gas.md) contains all information relevant to gas.
-   [schedule.md](include/kframework/schedule.md) contains all information relevant to EVM schedules.

These additional files extend the semantics to make the repository more useful:

-   [buf.md](include/kframework/buf.md) defines the `#buf` byte-buffer abstraction for use during symbolic execution.
-   [abi.md](include/kframework/abi.md) defines the [Contract ABI Specification](https://docs.soliditylang.org/en/v0.8.1/abi-spec.html) for use in proofs and easy contract/function specification.
-   [hashed-locations.md](include/kframework/hashed-locations.md) defines the `#hashedLocation` abstraction used to specify Solidity-generated storage layouts.
-   [edsl.md](include/kframework/edsl.md) combines the previous three abstractions for ease-of-use.
-   [foundry.md](include/kframework/foundry.md) adds Foundry capabilities to KEVM.

These files are used for testing the semantics itself:

-   [state-utils.md](include/kframework/state-utils.md) provides functionality for EVM initialization, setup, and querying.
-   [driver.md](include/kframework/driver.md) is an execution harness for KEVM, providing a simple language for describing tests/programs.

Building from source
--------------------

There are two backends of K available: LLVM for concrete execution and Haskell for symbolic execution.
This repository generates the build-products for each backend in `.build/usr/lib/kevm`.

### System Dependencies

First install the following tools:

-   [git](https://git-scm.com/)
-   GNU [Bison](https://www.gnu.org/software/bison/), [Flex](https://github.com/westes/flex), and [Autoconf](http://www.gnu.org/software/autoconf/).
-   GNU [libmpfr](https://www.mpfr.org/) and [libtool](https://www.gnu.org/software/libtool/).
-   [Z3](https://github.com/Z3Prover/z3) version 4.12.1

#### Installing Z3

KEVM requires Z3 version 4.12.1, which you may need to install from a source build if your package manager supplies a different version.
To do so, follow the instructions [here](https://github.com/Z3Prover/z3#building-z3-using-make-and-gccclang) after checking out the correct tag in the Z3 repository:

```sh
git clone https://github.com/Z3Prover/z3.git
cd z3
git checkout z3-4.12.1
python scripts/mk_make.py
cd build
make
sudo make install
```

On macOS, it is easiest to install Z3 from Homebrew.
If you wish to install from the source, install it to an appropriate prefix (e.g. `/usr/local` on Intel machines).

#### Ubuntu

On Ubuntu >= 22.04 (for example):

```sh
sudo apt-get install --yes                                                             \
            autoconf bison clang-12 cmake curl flex gcc jq libboost-test-dev           \
            libcrypto++-dev libffi-dev libgflags-dev libjemalloc-dev libmpfr-dev       \
            libprocps-dev libsecp256k1-dev libssl-dev libtool libyaml-dev lld-12       \
            llvm-12-tools make maven netcat-openbsd openjdk-11-jdk pkg-config          \
            protobuf-compiler python3 python3-dev python3-pip rapidjson-dev time       \
            zlib1g-dev libfmt-dev
```

On Ubuntu < 18.04, you'll need to skip `libsecp256k1-dev` and instead build it from source (via our `Makefile`):

```sh
make libsecp256k1
```

#### Arch Linux

On ArchLinux:

```sh
sudo pacman -S                                               \
    base base-devel boost clang cmake crypto++ curl git gmp  \
    gflags jdk-openjdk jemalloc libsecp256k1 lld llvm maven  \
    mpfr protobuf poetry python stack yaml-cpp zlib
```

#### macOS

After installing the Command Line Tools, [Homebrew](https://brew.sh/), and getting the [blockchain plugin](#blockchain-plugin), run:

```sh
brew tap kframework/k
brew install java automake libtool gmp mpfr pkg-config maven libffi llvm@14 openssl protobuf python bash kframework/k/cryptopp@8.6.0 poetry solidity
make libsecp256k1
```

**NOTE**: It is recommended to use the homebrew version of `flex` and XCode.

If you are building on an Apple Silicon machine, ensure that your `PATH` is set up correctly before running `make deps` or `make k-deps`.
You can do so using [`direnv`](https://direnv.net/) by copying `macos-envrc` to `.envrc`, then running `direnv allow`.

If the build on macOS still fails, you can also try adding the following lines to the top of your `Makefile` under `UNAME_S`:

```sh
ifeq ($(UNAME_S), Darwin)
SHELL := /usr/local/bin/bash
PATH := $(pwd)/.build/usr/bin:$(PATH)
endif
```

#### Haskell Stack (all platforms)

-   [Haskell Stack](https://docs.haskellstack.org/en/stable/install_and_upgrade/#installupgrade).
    Note that the version of the `stack` tool provided by your package manager might not be recent enough.
    Please follow installation instructions from the Haskell Stack website linked above.

To upgrade `stack` (if needed):

```sh
stack upgrade
export PATH=$HOME/.local/bin:$PATH
```

### Build Dependencies

#### K Framework

The `Makefile` and `kevm` will work with either a (i) globally installed K or a (ii) K submodule included in this repository.
For contributing to `kevm`, it is highly recommended to go with (ii) because some of the build scripts might not work otherwise.
Follow these instructions to get and build the K submodule:

```sh
git submodule update --init --recursive -- deps/k
make k-deps
```

If you don't need either the LLVM or Haskell backend, there are flags to skip them:

```sh
make k-deps SKIP_LLVM=true SKIP_HASKELL=true
```

On an Apple Silicon machine, an additional flag to `make` is required to correctly build the Haskell backend:

```sh
make k-deps APPLE_SILICON=true
```

#### Blockchain Plugin

You also need to get the blockchain plugin submodule and install it.

```sh
git submodule update --init --recursive -- deps/plugin
make plugin-deps
```

### Building

You need to set up a virtual environment using Poetry with the prerequisites `python 3.8.*`, `pip >= 20.0.2`, `poetry >= 1.3.2`:

```sh
make poetry
```

Finally, you can build the semantics.

```sh
make build
```

You can build specific targets using `build-llvm`, `build-Haskell`, or `build-foundry`.
For more information, refer to the [Makefile].

Running Tests
-------------

To execute tests from the [Ethereum Test Set], the submodule needs to be fetched first.

```sh
git submodule update --init --recursive  -- tests/ethereum-tests
```

The tests are run using the supplied `Makefile`.
Run `make build-prove` to generate tests from the markdown files.

The following subsume all other tests:

-   `make test`: All of the quick tests.
-   `make test-all`: All of the quick and slow tests.

These are the individual test-suites (all of these can be suffixed with `-all` to also run slow tests):

-   `make test-vm`: VMTests from the [Ethereum Test Set].
-   `make test-bchain`: Subset of BlockchainTests from the [Ethereum Test Set].
-   `make test-proof`: Proofs from the [Verified Smart Contracts].
-   `make test-interactive`: Tests of the `kevm` command.

When running tests with the `Makefile`, you can specify the `TEST_CONCRETE_BACKEND` (for concrete tests), or `TEST_SYMBOLIC_BACKEND` (for proofs).

For Developers
--------------

If built from the source, the `kevm` executable will be in the `.build/usr/bin` directory.
To make sure you are using the correct `kevm`, add this directory to your `PATH`:

```sh
export PATH=$(pwd)/.build/usr/bin:$PATH
```

Alternatively, if you work on multiple checkouts of `evm-semantics` or other semantics, you could add the relative path `.build/usr/bin` to your `PATH`.
Do note, however, that this is a security concern.

You can call `kevm help` to get a quick summary of how to use the script.

Run the file `tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json`:

```sh
kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json --schedule DEFAULT --mode VMTESTS
```

To enable the debug symbols for the llvm backend, build using this command:

```sh
make build-llvm KEVM_OPTS=--enable-llvm-debug
```

To debug a conformance test, add the `--debugger` flag to the command:

```sh
kevm interpret tests/ethereum-tests/BlockchainTests/GeneralStateTests/stExample/add11.json --backend llvm --mode NORMAL --schedule MERGE --chainid 1 --debugger
```

### Keeping in mind while developing

Always have your build up-to-date.

- If using the kup package manager, run `kup install kevm --version .` to install the local version.
- If building from source:
    -   `make poetry` needs to be re-run if you touch any of the `kevm-pyk` code.
    -   `make build` needs to be re-run if you touch any of this repos files.
    -   `make deps` needs to be re-run if there is an update of the K submodule (you did `git submodule update --init --recursive -- deps/k` and it actually did something).
    -   If both `deps` and `build` need to be re-run, you need to do `deps` first.
    -   `make clean` is a safe way to remove the `.build` directory, but then you need to re-run `make deps` (should be quick this time) and `make build`.

### Building with Nix

We now support building KEVM using [nix flakes](https://nixos.wiki/wiki/Flakes).
To set up nix flakes you will need to be on `nix` 2.4 or higher and follow the instructions [here](https://nixos.wiki/wiki/Flakes).

For example, if you are on a standard Linux distribution, such as Ubuntu, first [install nix](https://nixos.org/download.html#download-nix)
and then enable flakes by editing either `~/.config/nix/nix.conf` or `/etc/nix/nix.conf` and adding:

```
experimental-features = nix-command flakes
```

This is needed to expose the Nix 2.0 CLI and flakes support that are hidden behind feature-flags.

By default, Nix will build the project and its transitive dependencies from source, which can take up to an hour.
We recommend setting up [the binary cache](https://app.cachix.org/cache/kore) to speed up the build process significantly.

To build KEVM, run:

```sh
nix build .#kevm
```

This will build all of KEVM and K and put a link to the resulting binaries in the `result/` folder.


**NOTE**: Mac users, especially those running M1/M2 Macs may find nix segfaulting on occasion. If this happens, try running the nix command like this: `GC_DONT_GC=1 nix build .`

If you want to temporarily add the `kevm` binary to the current shell, run

```sh
nix shell .#kevm
```

### Profiling with Nix

Nix can also be used to quickly profile different versions of the Haskell backend. Simply run:

```sh
nix build github:runtimeverification/evm-semantics#profile \
  --override-input k-framework/haskell-backend github:runtimeverification/haskell-backend/<HASH> \
  -o prof-<HASH>
```

replacing `<HASH>` with the commit you want to run profiling against.

If you want to profile against a working version of the Haskell backend repository, simply `cd` into the root of the repo and run:

```sh
nix build github:runtimeverification/evm-semantics#profile \
  --override-input k-framework/haskell-backend $(pwd) \
  -o prof-my-feature
```

To compare profiles, you can use:

```sh
nix run github:runtimeverification/evm-semantics#compare-profiles -- prof-my-feature prof-<HASH>
```

This will produce a nice table with the times for both versions of the haskell-backend.
Note that `#profile` pre-pends the output of `kore-exec --version` to the profile run, which is then used as a tag by the `#compare-profiles` script.
Therefore, any profiled local checkout of the haskell-backend will report as `dirty-ghc8107` in the resulting table.

Media
-----

This repository can build two pieces of documentation for you, the [Jello Paper] and the [2017 Devcon3] presentation.

### System Dependencies

For the presentations in the `media` directory, you'll need `pdflatex`, commonly provided with `texlive-full`, and `pandoc`.

```sh
sudo apt install texlive-full pandoc
```

### Building

To build all the PDFs (presentations and reports) available in the `media/` directory, use:

```sh
make media
```

Resources
=========

-   [EVM Yellowpaper](https://github.com/ethereum/yellowpaper): Original specification of EVM.
-   [LEM Semantics of EVM](https://github.com/pirapira/eth-isabelle)
-   [EVM Opcode Interactive Reference](https://www.evm.codes/?fork=merge)
-   [Solidity ABI Encoding](https://docs.soliditylang.org/en/v0.8.19/abi-spec.html)

For more information about [The K Framework](https://kframework.org), refer to these sources:

-   [The K Tutorial](https://github.com/runtimeverification/k/tree/master/k-distribution/k-tutorial)
-   [Semantics-Based Program Verifiers for All Languages](https://fsl.cs.illinois.edu/publications/stefanescu-park-yuwen-li-rosu-2016-oopsla)
-   [Reachability Logic Resources](http://fsl.cs.illinois.edu/index.php/Reachability_Logic_in_K)
-   [Matching Logic Resources](http://www.matching-logic.org/)
-   [Logical Frameworks](https://dl.acm.org/doi/10.5555/208683.208700): Discussion of logical frameworks.

[Jello Paper]: <https://jellopaper.org>
[2017 Devcon3]: <https://archive.devcon.org/archive/watch?edition=3&order=desc&sort=edition>
[K Reachability Logic Prover]: <http://fsl.cs.illinois.edu/FSL/papers/2016/stefanescu-park-yuwen-li-rosu-2016-oopsla/stefanescu-park-yuwen-li-rosu-2016-oopsla-public.pdf>
[K Editor Support]: <https://github.com/kframework/k-editor-support>
[Ethereum Test Set]: <https://github.com/ethereum/tests>
[Verified Smart Contracts]: <https://github.com/runtimeverification/verified-smart-contracts>
[eDSL]: <https://github.com/runtimeverification/verified-smart-contracts/blob/master/resources/edsl.md>
[kup package manager]: <https://github.com/runtimeverification/kup>
[Makefile]: <./Makefile>
[VERIFICATION.md]: <./VERIFICATION.md>
