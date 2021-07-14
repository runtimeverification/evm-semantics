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

### From Source Build

Follow the instructions in the [README file](https://github.com/kframework/evm-semantics) for building KEVM from source.
