#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
exec python3 Auxillary/assembly/run_flow.py \
  --external-native-linux \
  --repo-root "$PWD" \
  --standard-report-directory "$PWD/artifacts/assembly" \
  --report-directory "$PWD/artifacts/assembly/flow" "$@"
