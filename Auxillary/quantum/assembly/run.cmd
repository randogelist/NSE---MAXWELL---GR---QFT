@echo off
setlocal
rem External-user WSL/Linux launcher; literal repository paths require POSIX.
rem Optional first argument: absolute Linux path to the existing Git checkout.
set "NSE_QUANTUM_REPO=%~1"
if not defined NSE_QUANTUM_REPO set "NSE_QUANTUM_REPO=%~dp0..\..\.."
wsl.exe --cd "%NSE_QUANTUM_REPO%" bash -lc "bash Auxillary/run.sh -Phase Dependencies && NSE_QUANTUM_ASSEMBLY_EXTERNAL_NATIVE=1 bash Auxillary/quantum/assembly/run.sh"
exit /b %errorlevel%
