@echo off
setlocal
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0scripts\run.ps1" -ExpectedPlatform Windows %*
set "FEFFERMAN_ADAPTER_EXIT=%ERRORLEVEL%"
exit /b %FEFFERMAN_ADAPTER_EXIT%
