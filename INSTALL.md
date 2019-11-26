Installing Release Builds
=========================

These instructions explain how to download, install, and build the KEVM packages.
Current supported systems are:

-   Ubuntu Bionic (18.04)
-   Debian Buster
-   Mac OS X Mojave

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

### Mac OS X Mojave

Tap the `kframework/k` bottle then install the downloaded `kevm` bottle:

```sh
brew tap kframework/k "file:///$(pwd)"
brew install "kevm--X.Y.Z.mojave.bottle.tar.gz" -v
```

Building Packages
-----------------

Make sure to bump the version numbers in the following places:

-   `RELEASE_ID` in `Jenkinsfile`,
-   `pkgver` in `package/PKGBUILD`, and
-   version number in `package/debian/changelog`.

If these numbers do not agree, then building the release will not work.

### Ubuntu/Debian

Build the package in by running:

```sh
cp -r package/debian ./
dpkg-buildpackage --no-sign
```

This will throw an error for any missing build dependencies, install them with `sudo apt install ...`.
The `kevm_X.Y.Z_amd64_ID.deb` package will be placed one directory up from the repository root.

### Arch

Build the package with:

```sh
cd package
makepkg -s
```

This will put `kevm-git-X.Y.Z-V-x86_64.pkg.tar.xz` in the current directory.
