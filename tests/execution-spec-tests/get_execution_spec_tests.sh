#!/bin/bash
set -euxo pipefail

# requires jq
# sudo apt install jq

# Fixture releases live on ethereum/execution-specs (EELS); the old
# ethereum/execution-spec-tests repository was archived in July 2026:
#   https://github.com/ethereum/execution-specs/releases
# Standard releases (tests@vX.Y.Z) ship fixtures_stable.tar.gz /
# fixtures_develop.tar.gz; devnet prereleases (e.g.
# tests-glamsterdam-devnet@vX.Y.Z) ship a single feature tarball such as
# fixtures_glamsterdam-devnet.tar.gz.
# As of Jul 2026, deployed is Osaka (+BPO forks); Glamsterdam (EL fork
# name: Amsterdam) is under development on glamsterdam-devnet releases.

ARTIFACT="fixtures_glamsterdam-devnet.tar.gz"
TARGET_DIR="fixtures"

OWNER="ethereum"
REPO="execution-specs"

# Compute the path of the VERSION file
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
VERSION_FILE="$SCRIPT_DIR/VERSION"

# VERSION RESOLUTION ORDER:
#   1. $FIXTURE_VERSION (env override)
#   2. VERSION file
#   3. the literal string "latest"
if [[ -n "${FIXTURE_VERSION:-}" ]]; then
  VERSION="${FIXTURE_VERSION}"
elif [[ -f $VERSION_FILE ]]; then
  VERSION="$(<"$VERSION_FILE")"
else
  VERSION="latest"
fi

DOWNLOAD_URL="https://github.com/$OWNER/$REPO/releases/download/$VERSION/$ARTIFACT"

# Create target directory
mkdir -p "$TARGET_DIR"

# Download and extract
curl -LO "$DOWNLOAD_URL"

tar -xzf "$ARTIFACT" --strip-components=1 -C "$TARGET_DIR"

# Cleanup
rm "$ARTIFACT"
