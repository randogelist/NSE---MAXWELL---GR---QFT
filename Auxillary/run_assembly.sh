#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
exec python3 Auxillary/assembly/run.py \
  --external-native-linux \
  --repo-root "$PWD" \
  --dependency-report-directory "$PWD/artifacts/external-linux" \
  --report-directory "$PWD/artifacts/assembly" "$@"
