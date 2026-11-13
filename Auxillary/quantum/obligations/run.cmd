@echo off
setlocal
rem External native Windows Lean 4.34.0-rc1 replay; preserves official and project caches.
set "PYTHONUTF8=1"
where py >nul 2>nul
if not errorlevel 1 (
  py -3 "%~dp0windows.py" %*
) else (
  python "%~dp0windows.py" %*
)
exit /b %errorlevel%
