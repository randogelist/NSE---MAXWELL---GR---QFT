#!/usr/bin/env bash
set -euo pipefail
package_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$package_root/../Auxillary/GR/scripts/run_gr.py" \
  --package-root "$package_root" --expected-platform linux "$@"
