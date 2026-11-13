#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
exec pwsh -NoLogo -NoProfile -File Auxillary/scripts/run.ps1 \
  -ExpectedPlatform Linux -ReportDirectory artifacts/external-linux "$@"
