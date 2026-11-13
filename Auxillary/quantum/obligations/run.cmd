@echo off
setlocal
rem External-user cached WSL/Linux launcher. Optional first argument: Linux Git checkout.
set "NSE_QUANTUM_REPO=%~1"
if not defined NSE_QUANTUM_REPO set "NSE_QUANTUM_REPO=%~dp0..\..\.."
wsl.exe --cd "%NSE_QUANTUM_REPO%" bash -lc "bash Auxillary/run.sh -Phase Dependencies && NSE_QUANTUM_OBLIGATIONS_EXTERNAL_NATIVE=1 bash Auxillary/quantum/obligations/run.sh"
exit /b %errorlevel%
