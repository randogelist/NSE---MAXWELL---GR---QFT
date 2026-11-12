@echo off
setlocal
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0scripts\run.ps1" %*
set "NSE_MAXWELL_EXIT=%ERRORLEVEL%"
exit /b %NSE_MAXWELL_EXIT%
