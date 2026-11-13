#!/usr/bin/env bash
set -euo pipefail
package_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
exec python3 "$package_root/../Auxillary/GR/Assembly/scripts/run_assembly.py" \
  --package-root "$package_root" --expected-platform linux "$@"
