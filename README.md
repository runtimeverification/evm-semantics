KEVM: Semantics of EVM in K
===========================

In this repository we provide a model of the EVM in K.

Documentation/Support
---------------------

These may be useful for learning KEVM and K (newest to oldest):

-   [Jello Paper], a nice presentation of this repository.
-   [20 minute tour of the semantics](https://www.youtube.com/watch?v=tIq_xECoicQNov) at [2017 Devcon3].
-   [KEVM 1.0 technical report](http://hdl.handle.net/2142/97207), especially sections 3 and 5.
-   [KEVM Paper at CSF'18/FLoC](https://fsl.cs.illinois.edu/publications/hildenbrandt-saxena-zhu-rodrigues-daian-guth-moore-zhang-park-rosu-2018-csf).

To get support for KEVM, please join our [Discord Channel](https://discord.gg/EZtNj7gt).

Repository Structure
--------------------

The following files constitute the KEVM semantics:

-   [network.md](include/kframework/network.md) provides the status codes which are reported to an Ethereum client on execution exceptions.
-   [json-rpc.md](include/kframework/json-rpc.md) is an implementation of JSON RPC in K.
-   [evm-types.md](include/kframework/evm-types.md) provides the (functional) data of EVM (256 bit words, wordstacks, etc...).
-   [serialization.md](include/kframework/serialization.md) provides helpers for parsing and unparsing data (hex strings, recursive-length prefix, merkle trees, etc.).
-   [evm.md](include/kframework/evm.md) is the main KEVM semantics, containing the configuration and transition rules of EVM.

These additional files extend the semantics to make the repository more useful:

-   [buf.md](include/kframework/buf.md) defines the `#buf` byte-buffer abstraction for use during symbolic execution.
-   [abi.md](include/kframework/abi.md) defines the [Contract ABI Specification](https://docs.soliditylang.org/en/v0.8.1/abi-spec.html) for use in proofs and easy contract/function specification.
-   [hashed-locations.md](include/kframework/hashed-locations.md) defines the `#hashedLocation` abstraction which makes it easier to specify Solidity-generate storage layouts.
-   [edsl.md](include/kframework/edsl.md) combines the previous three abstractions for ease-of-use.
-   [foundry.md](include/kframework/foundry.md) adds Foundry capabilities to KEVM.

These files are used for testing the semantics itself:

-   [state-utils.md](include/kframework/state-utils.md) provides functionality for EVM initialization, setup, and querying.
-   [driver.md](include/kframework/driver.md) is an execution harness for KEVM, providing a simple language for describing tests/programs.

Installing/Building
-------------------

### K Backends

There are two backends of K available: LLVM for concrete execution and Haskell for symbolic execution.
This repository generates the build-products for each backend in `.build/usr/lib/kevm`.

### System Dependencies

The following are needed for building/running KEVM:

-   [git](https://git-scm.com/)
-   GNU [Bison](https://www.gnu.org/software/bison/), [Flex](https://github.com/westes/flex), and [Autoconf](http://www.gnu.org/software/autoconf/).
-   GNU [libmpfr](https://www.mpfr.org/) and [libtool](https://www.gnu.org/software/libtool/).
-   Java 8 JDK (eg. [OpenJDK](http://openjdk.java.net/))
-   [Z3](https://github.com/Z3Prover/z3) version 4.8.15

For the exact dependencies check the Dockerfile.

#### Installing Z3

KEVM requires Z3 version 4.8.15, which you may need to install from a source
build if your package manager supplies a different version. To do so, follow the
instructions
[here](https://github.com/Z3Prover/z3#building-z3-using-make-and-gccclang) after
checking out the correct tag in the Z3 repository:

```sh
git clone https://github.com/Z3Prover/z3.git
cd z3
git checkout z3-4.8.15
python scripts/mk_make.py
cd build
make
sudo make install
```

On macOS, it is easiest to install Z3 from Homebrew. If you do wish to install
from source, make sure to install it to an appropriate prefix (e.g. `/usr/local`
on Intel machines).

#### Ubuntu

On Ubuntu >= 18.04 (for example):

```sh
sudo apt-get install --yes                                                             \
            autoconf bison clang-10 cmake curl flex gcc jq libboost-test-dev           \
            libcrypto++-dev libffi-dev libgflags-dev libjemalloc-dev libmpfr-dev       \
            libprocps-dev libsecp256k1-dev libssl-dev libtool libyaml-dev lld-10       \
            llvm-10-tools make maven netcat-openbsd openjdk-11-jdk pkg-config          \
            protobuf-compiler python3 python3-dev python3-pip rapidjson-dev time      \
            zlib1g-dev
pip3 install poetry
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
    mpfr protobuf python stack yaml-cpp zlib
```

#### macOS

After installing the Command Line Tools, [Homebrew](https://brew.sh/), and getting the [blockchain plugin](#blockchain-plugin), run:

```sh
brew tap kframework/k
brew install java automake libtool gmp mpfr pkg-config maven libffi llvm@14 openssl protobuf python bash kframework/k/cryptopp@8.6.0 poetry solidity
make libsecp256k1
```

**NOTE**: Previous versions of these instructions required the user to use either the homebrew version of `flex` or the xcode command line tools version, with the wrong option giving an error.
The current recommendation is to use the homebrew version.

If you are building on an Apple Silicon machine, ensure that your `PATH` is set
up correctly before running `make deps` or `make k-deps`. You can do so using
[`direnv`](https://direnv.net/) by copying `macos-envrc` to `.envrc`, then
running `direnv allow`.

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

The `Makefile` and `kevm` will work with either a (i) globally installed K, or (ii) a K submodule included in this repository.
For contributing to `kevm`, it is highly recommended to go with (ii) because otherwise some of the build scripts might not work.
Follow these instructions to get and build the K submodule:

```sh
git submodule update --init --recursive -- deps/k
make k-deps
```

If you don't need either the LLVM or Haskell backend, there are flags to skip them:

```sh
make k-deps SKIP_LLVM=true SKIP_HASKELL=true
```

On an Apple Silicon machine, an additional flag to `make` is required to
correctly build the Haskell backend:

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

You need to set up a virtual environment using Poetry:

```sh
make poetry
```

Finally, you can build the semantics.

```sh
make build
```

Running Tests
-------------

The tests are run using the supplied `Makefile`.
First, run `make build-prove` to generate some of the tests from the markdown files.

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
-------------

After building, the `kevm` executable will be located in the `.build/usr/bin` directory.
The one in the project root is a build artifact, don't use it.
To make sure you are using the correct `kevm`, add this directory to your `PATH`:

```sh
export PATH=$(pwd)/.build/usr/bin:$PATH
```

Alternatively, if you work on multiple checkouts of `evm-semantics`, or other semantics, you could add the relative path `.build/usr/bin` to your `PATH`.
Do note, however, that this is a security concern.

You can call `kevm help` to get a quick summary of how to use the script.

Run the file `tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json`:

```sh
kevm run tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json --schedule DEFAULT --mode VMTESTS
```

To run proofs, you can similarly use `kevm`.
For example, to prove one of the specifications:

```sh
kevm prove tests/specs/erc20/ds/transfer-failure-1-a-spec.k --verif-module VERIFICATION
```

You can also debug proofs interactively:

```sh
kevm prove tests/specs/erc20/ds/transfer-failure-1-a-spec.k --verif-module VERIFICATION --debugger --debug-script kscript --backend haskell
```

Here, `kscript` is a file containing `kore-repl` commands.
For example, we advise to put an alias for outputting the current configuration as a pretty-printed term (as opposed to raw `kore` term):

```sh
alias konfig = config | kast -i kore -o pretty -d .build/usr/lib/kevm/haskell /dev/stdin
```

### Building with Nix

We now support building KEVM using [nix flakes](https://nixos.wiki/wiki/Flakes).
To set up nix flakes you will need to be on `nix` 2.4 or higher and follow the instructions [here](https://nixos.wiki/wiki/Flakes).

For example, if you are on a standard Linux distribution, such as Ubuntu, first [install nix](https://nixos.org/download.html#download-nix)
and then enable flakes by editing either `~/.config/nix/nix.conf` or `/etc/nix/nix.conf` and adding:

```
experimental-features = nix-command flakes
```

This is needed to expose the Nix 2.0 CLI and flakes support that are hidden behind feature-flags.


By default, Nix will build the project and its transitive dependencies from
source, which can take up to an hour. We recommend setting up
[the binary cache](https://app.cachix.org/cache/kore) to speed up the build
process significantly. You will also need to add the following sections to `/etc/nix/nix.conf` or, if you are a trusted user, `~/.config/nix/nix.conf` (if you don't know what a "trusted user" is, you probably want to do the former):

```
trusted-public-keys = ... hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=
substituters = ... https://cache.iog.io
```

i.e. if the file was originally

```
substituters = https://cache.nixos.org
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY=
```

it will now read

```
substituters = https://cache.nixos.org https://cache.iog.io
trusted-public-keys = cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=
```

To build KEVM, run:

```bash
nix build .#kevm
```

This will build all of KEVM and K and put a link to the resulting binaries in the `result/` folder.


_Note: Mac users, especially those running M1/M2 Macs may find nix segfaulting on occasion. If this happens, try running the nix command like this: `GC_DONT_GC=1 nix build .`_


If you want to temporarily add the `kevm` binary to the current shell, run

```bash
nix shell .#kevm
```

### Profiling with Nix

Nix can also be used to quickly profile different versions of the haskell backend. Simply run

```
nix build github:runtimeverification/evm-semantics#profile \
  --override-input k-framework/haskell-backend github:runtimeverification/haskell-backend/<HASH> \
  -o prof-<HASH>
```

replacing `<HASH>` with the commit you want to run profiling against.

If you want to profile against a working version of the haskell backend repo, simply `cd` into the root of the repo and run

```
nix build github:runtimeverification/evm-semantics#profile \
  --override-input k-framework/haskell-backend $(pwd) \
  -o prof-my-feature
```

To compare profiles, you can use

```
nix run github:runtimeverification/evm-semantics#compare-profiles -- prof-my-feature prof-<HASH>
```

This will produce a nice table with the times for both versions of haskell-backend.
Noe that `#profile` pre-pends the output of `kore-exec --version` to the profile run, which is then used as a tag by the `#compare-profiles` script.
Therefore, any profiled local checkout of haskell-backend will report as `dirty-ghc8107` in the resulting table.

### Keeping `.build` up-to-date while developing

-   `make build` needs to be re-run if you touch any of this repos files.
-   `make deps` needs to be re-run if there is an update of the K submodule (you did `git submodule update --init --recursive -- deps/k` and it actually did something).
-   If both `deps` and `build` need to be re-run, you need to do `deps` first.
-   `make clean` is a safe way to remove the `.build` directory, but then you need to re-run `make deps` (should be quick this time) and `make build`.

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

For more information about [The K Framework](https://kframework.org), refer to these sources:

-   [The K Tutorial](https://kframework.org/k-distribution/pl-tutorial/)
-   [Semantics-Based Program Verifiers for All Languages](https://fsl.cs.illinois.edu/publications/stefanescu-park-yuwen-li-rosu-2016-oopsla)
-   [Reachability Logic Resources](http://fsl.cs.illinois.edu/index.php/Reachability_Logic_in_K)
-   [Matching Logic Resources](http://www.matching-logic.org/)
-   [Logical Frameworks](https://dl.acm.org/doi/10.5555/208683.208700): Discussion of logical frameworks.

[Jello Paper]: <https://jellopaper.org>
[2017 Devcon3]: <https://ethereumfoundation.org/devcon3/>
[K Reachability Logic Prover]: <http://fsl.cs.illinois.edu/FSL/papers/2016/stefanescu-park-yuwen-li-rosu-2016-oopsla/stefanescu-park-yuwen-li-rosu-2016-oopsla-public.pdf>
[K Editor Support]: <https://github.com/kframework/k-editor-support>
[Ethereum Test Set]: <https://github.com/ethereum/tests>
[Verified Smart Contracts]: <https://github.com/runtimeverification/verified-smart-contracts>
[eDSL]: <https://github.com/runtimeverification/verified-smart-contracts/blob/master/resources/edsl.md>
