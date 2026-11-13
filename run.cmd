@echo off
setlocal
rem Historical native Windows entry point; the literal arrow-folder layout requires Linux.
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0Fefferman_B_adapter\scripts\run.ps1" %*
set "NSE_MAXWELL_EXIT=%ERRORLEVEL%"
exit /b %NSE_MAXWELL_EXIT%
