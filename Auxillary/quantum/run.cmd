@echo off
rem External-user WSL/Linux launcher; literal repository paths require POSIX.
wsl.exe --cd "%~dp0..\.." bash -lc "bash Auxillary/run.sh && NSE_QUANTUM_EXTERNAL_NATIVE=1 bash Auxillary/quantum/run.sh"
exit /b %errorlevel%
