#!/usr/bin/env bash
set -euo pipefail

# Kup relies on cachix registry k-framework-binary.
CACHE="k-framework-binary"
OWNER_REPO="${OWNER_REPO:-$(git remote get-url origin | sed -E 's#(git@github.com:|https://github.com/)##; s#\.git$##')}"
REV="${REV:-${GITHUB_SHA:-$(git rev-parse HEAD)}}"
UNAME_S="$(uname -s)"
UNAME_M="$(uname -m)"
case "${UNAME_S}-${UNAME_M}" in
  Linux-x86_64) SYSTEM="x86_64-linux" ;;
  Linux-aarch64 | Linux-arm64) SYSTEM="aarch64-linux" ;;
  Darwin-x86_64) SYSTEM="x86_64-darwin" ;;
  Darwin-arm64) SYSTEM="aarch64-darwin" ;;
  *)
    echo "Unsupported platform: ${UNAME_S}-${UNAME_M}" >&2
    exit 1
    ;;
esac
PIN_API_URL="https://app.cachix.org/api/v1/cache/${CACHE}/pin"
CHECK_PACKAGES=(kevm)

SUMMARY="${GITHUB_STEP_SUMMARY:-/dev/stdout}"

# Append to the GitHub step summary when set; always print to stdout for live job logs.
summary_and_log() {
  if [[ "${SUMMARY}" == "/dev/stdout" ]]; then
    cat
  else
    tee -a "${SUMMARY}"
  fi
}

{
  echo "## Cachix Publish Summary"
  echo "CACHE: $CACHE"
  echo "OWNER_REPO: $OWNER_REPO"
  echo "REV: $REV"
  echo "SYSTEM: $SYSTEM"
  echo "PACKAGES: ${CHECK_PACKAGES[*]}"
} >> "$SUMMARY"

# Verify push + pin together for each package. Both can become visible with delay.
PIN_VISIBILITY_TIMEOUT_SECONDS=120 # 2 minutes
PIN_VISIBILITY_INTERVAL_SECONDS=5  # 5 seconds
PIN_VISIBILITY_ATTEMPTS=$((PIN_VISIBILITY_TIMEOUT_SECONDS / PIN_VISIBILITY_INTERVAL_SECONDS))
for i in $(seq 1 "$PIN_VISIBILITY_ATTEMPTS"); do
  PIN_JSON="$(curl -fsSL "${PIN_API_URL}?q=${REV}")"
  ALL_OK=1

  for PKG in "${CHECK_PACKAGES[@]}"; do
    KEY="github:${OWNER_REPO}/${REV}#packages.${SYSTEM}.${PKG}"
    STORE_PATH="$(
      echo "$PIN_JSON" \
        | jq -r --arg k "$KEY" 'map(select(.name == $k)) | first | (.lastRevision.storePath // .storePath // .store_path // .path // "")'
    )"
    if [ -z "$STORE_PATH" ]; then
      PIN_STATUS="pin-missing"
      PUSH_STATUS="000"
      ALL_OK=0
      {
        echo "key-${PKG}: ${KEY}"
        echo "pin-status-${PKG}: ${PIN_STATUS}"
        echo "push-http-${PKG}: ${PUSH_STATUS}"
      } | summary_and_log
      continue
    fi

    PIN_STATUS="pin-ok"
    HASH="$(basename "$STORE_PATH" | cut -d- -f1)"
    PUSH_NARINFO_URL="https://${CACHE}.cachix.org/${HASH}.narinfo"
    PUSH_STATUS="$(curl -sS -o /dev/null -w '%{http_code}' "$PUSH_NARINFO_URL")" || PUSH_STATUS="000"
    if [ "$PUSH_STATUS" != "200" ]; then
      ALL_OK=0
    fi

    {
      echo "key-${PKG}: ${KEY}"
      echo "store-path-${PKG}: ${STORE_PATH}"
      echo "pin-status-${PKG}: ${PIN_STATUS}"
      echo "push-http-${PKG}: ${PUSH_STATUS}"
    } | summary_and_log
  done

  if [ "$ALL_OK" = "1" ]; then
    echo "cachix-status: push-and-pin-ok-for-all-packages" >> "$SUMMARY"
    exit 0
  fi

  RETRY_MSG="cachix-check-attempt-${i}: not-ready, retrying in ${PIN_VISIBILITY_INTERVAL_SECONDS}s"
  printf '%s\n' "$RETRY_MSG" | summary_and_log
  sleep "$PIN_VISIBILITY_INTERVAL_SECONDS"
done

echo "cachix-status: push-or-pin-missing-after-${PIN_VISIBILITY_TIMEOUT_SECONDS}s-for-at-least-one-package" >> "$SUMMARY"
# Pin API bulk JSON goes to job logs only (step summary stays readable); helps if the response shape changes.
echo "check-cachix-pin: raw Cachix pin API response (last fetch):" >&2
echo "$PIN_JSON" >&2
exit 1
