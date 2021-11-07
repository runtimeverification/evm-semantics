Installing KEVM
===============

We currently provide these ways to install KEVM:

-   Ubuntu packages,
-   Docker images, and
-   Building from source.

The provided packages ship with their own version of K, to ensure that you get exactly the correct version to use.

Downloading Packages
--------------------

Download the appropriate packages from the [GitHub Releases Page](https://github.com/kframework/evm-semantics/releases).
Releases are generated as often as possible from the `master` branch, and are tagged with their version and git commit.

Installing Packages
-------------------

### Ubuntu

Download the `kevm_X.Y.Z_amd64_focal.deb` package from GitHub releases.
Install it with the following command:

```sh
sudo apt-get install ./kevm_X.Y.Z_amd64_focal.deb
```

### Docker Images

Docker images with KEVM pre-installed are available at the [runtimeverification/kframework-evm-semantics Docker Hub repository](https://hub.docker.com/repository/docker/runtimeverificationinc/kframework-evm-semantics).

Each release at `COMMIT_ID` has an image associated with it at `runtimeverificationinc/kframework-k:ubuntu-focal-COMMIT_ID`.
The latest `master` build Docker image can be accessed with `COMMIT_ID` set to `master`.

To run the image directly:

```sh
docker run -it runtimeverificationinc/kframework-evm-semantics:ubuntu-focal-COMMIT_ID
```

and to make a Docker Image based on it, use the following line in your `Dockerfile`:

```Dockerfile
FROM runtimeverificationinc/kframework-evm-semantics:ubuntu-focal-COMMIT_ID
```

### Nix

#### Prerequisites

It is safe to skip any of these dependencies that are already installed.

Follow the instructions below.
Perform all steps as your normal (non-root) user.
You may find the same instructions and our public key at <https://runtimeverification.cachix.org>.
To follow this instructions, you will need `curl` installed on your system <https://curl.haxx.se/download.html>.

#### Nix

Please pay careful attention to any additional instructions printed by the installer.
Install Nix:

```.sh
# Linux and macOS < 10.15
bash <(curl -L https://nixos.org/nix/install)

# macOS 10.15 (See note below)
bash <(curl -L https://nixos.org/nix/install) --darwin-use-unencrypted-nix-store-volume
```

For macOS 10.15, please refer to the [Nix manual](https://nixos.org/manual/nix/stable/#sect-macos-installation) for more information.

#### Cachix

Install Cachix and start using the binary cache:

```.sh
nix-env -iA cachix -f https://cachix.org/api/v1/install
cachix use runtimeverification
```

#### Install with Nix

```.sh
git clone https://github.com/kframework/evm-semantics
cd evm-semantics
git submodule update --init --recursive deps
make nix-install
```

### From Source Build

Follow the instructions in the [README file](https://github.com/kframework/evm-semantics) for building KEVM from source.

### Dependencies

Note that KEVM requires version 4.8.11 of the Z3 solver to be installed; follow
the instructions in the [README
file](https://github.com/kframework/evm-semantics) to do so.
