@echo off
setlocal
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0scripts\run.ps1" -ExpectedPlatform Windows %*
set "MAXWELL_ENDPOINT_EXIT=%ERRORLEVEL%"
exit /b %MAXWELL_ENDPOINT_EXIT%
