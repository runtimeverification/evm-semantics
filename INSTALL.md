Installing KEVM
===============

We currently provide two ways to install KEVM:

-   An Ubuntu Bionic package.
-   Building from source.

The provided packages ship with their own version of K, to ensure that you get exactly the correct version to use.

Downloading Packages
--------------------

Download the appropriate packages from the [GitHub Releases Page](https://github.com/kframework/evm-semantics/releases).
Releases are generated as often as possible from the `master` branch, and are tagged with their version and git commit.

Installing Packages
-------------------

### Ubuntu Bionic

Download the `kevm_X.Y.Z_amd64_bionic.deb` package from GitHub releases (where `X.Y.Z` is the version identifier).
Install it with the following command:

```sh
sudo apt-get install ./kevm_X.Y.Z_amd64_bionic.deb
```

### From Source Build

Follow the instructions in the [README file](https://github.com/kframework/evm-semantics) for building KEVM from source.
