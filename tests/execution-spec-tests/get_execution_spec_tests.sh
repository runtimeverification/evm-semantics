#!/bin/bash
set -e

# requires jq
# sudo apt install jq

# The following two artifacts are intended for consumption by clients:
# - fixtures.tar.gz: Generated up to the last deployed fork.
# - fixtures_develop.tar.gz: Generated up to and including the latest dev fork.
# As of March 2024, dev is Prague, deployed is Cancun.

ARTIFACT="fixtures_develop.tar.gz"
TARGET_DIR="fixtures"

OWNER="ethereum"
REPO="execution-spec-tests"
VERSION="v4.2.0" #"latest"
DOWNLOAD_URL="https://github.com/$OWNER/$REPO/releases/download/$VERSION/$ARTIFACT"

# Create target directory
mkdir -p "$TARGET_DIR"

# Download and extract
echo "Downloading fixture artifacts $ARTIFACT version $VERSION..."
curl -LO $DOWNLOAD_URL

echo "Extracting artifacts to $TARGET_DIR..."
tar -xzf "$ARTIFACT" --strip-components=1 -C "$TARGET_DIR"

# Cleanup
echo "Deleting tar file..."
rm $ARTIFACT
