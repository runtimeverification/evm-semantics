#!/usr/bin/env bash

set -xeuo pipefail

notif() { echo "== $@" >&2 ; }
fatal() { echo "[FATAL] $@" ; exit 1 ; }

version_file="package/version"

# Bumps the patch level. Starting a new major/minor line means setting `package/version`
# by hand first; the first release of that line is then X.Y.1, not X.Y.0.
version_bump() {
    local version version_major version_minor version_patch new_version
    version="$(cat "${version_file}")"
    version_major="$(echo "${version}" | cut --delimiter '.' --field 1)"
    version_minor="$(echo "${version}" | cut --delimiter '.' --field 2)"
    version_patch="$(echo "${version}" | cut --delimiter '.' --field 3)"
    new_version="${version_major}.${version_minor}.$((version_patch + 1))"
    echo "${new_version}" > "${version_file}"
    notif "Version: ${new_version}"
}

version_sub() {
    local version
    version="$(cat $version_file)"
    sed --in-place 's/^version = ".*"$/version = "'${version}'"/' kevm-pyk/pyproject.toml
    # uv.lock records the workspace package version too; re-lock so it cannot drift from the manifest.
    uv --project kevm-pyk lock
}

version_command="$1" ; shift

case "${version_command}" in
    bump) version_bump "$@"                      ;;
    sub)  version_sub  "$@"                      ;;
    *)    fatal "No command: ${version_command}" ;;
esac
