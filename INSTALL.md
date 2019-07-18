Installating Release Builds
===========================

These instructions explain how to download, install, and build the KEVM packages.
Current supported systems are:

-   Arch Linux
-   Ubuntu Bionic (18.04)

Downloading Packages
--------------------

We release our packages on GitHub, visit the [Releases](https://github.com/kframework/evm-semantics/releases) page to see available versions.
Releases are generated as often as possible from the `master` branch of the repository.

Installing Packages
-------------------

### Ubuntu/Debian

Install the package with (`X.Y.Z` is version number, `ID` is platform identifier):

```sh
sudo apt install ./kevm_X.Y.Z_amd64_ID.deb
```

### Arch

Install the package with (`X.Y.Z-V` is version number):

```sh
sudo pacman -U ./kevm-git-X.Y.Z-V-x86_64.pkg.tar.xz
```

Building Packages
-----------------

Update `stack` with `sudo stack upgrade` or `curl -sSL https://get.haskellstack.org/ | sh -s - -f` to make sure you have the newest version (> 2.0).

### Ubuntu/Debian

Build the package in by running:

```sh
dpkg-buildpackage --no-sign
```

This will throw an error for any build dependencies you're missing, install them with `sudo apt install ...`.
The `kevm_X.Y.Z_amd64_ID.deb` package will be placed one directory up from the repository root.

### Arch

Build the package with:

```sh
makepkg -s
```

This will put `kevm-git-X.Y.Z-V-x86_64.pkg.tar.xz` in the current directory.
