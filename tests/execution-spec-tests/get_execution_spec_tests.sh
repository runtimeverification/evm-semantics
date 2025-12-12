#!/bin/bash
set -euxo pipefail

# requires jq
# sudo apt install jq

# The following two artifacts are intended for consumption by clients:
# - fixtures_stable.tar.gz: Generated up to the last deployed fork.
# - fixtures_develop.tar.gz: Generated up to and including the latest dev fork.
# As of Dec 2025, deployed is Osaka.

ARTIFACT="fixtures_stable.tar.gz"
TARGET_DIR="fixtures"

OWNER="ethereum"
REPO="execution-spec-tests"

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
curl -LO $DOWNLOAD_URL

tar -xzf "$ARTIFACT" --strip-components=1 -C "$TARGET_DIR"

# Cleanup
rm $ARTIFACT
