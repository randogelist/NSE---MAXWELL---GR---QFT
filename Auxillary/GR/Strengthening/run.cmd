@echo off
setlocal
where gh >nul 2>nul
if errorlevel 1 (
  echo GITHUB_CLI_REQUIRED_FOR_CACHED_EXTERNAL_CI
  exit /b 1
)
gh workflow run gr-strengthening.yml --repo randogelist/NSE---MAXWELL---GR---QFT --ref STRENGTHENING-GR-FB
exit /b %errorlevel%
