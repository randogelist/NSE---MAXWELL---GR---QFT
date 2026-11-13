@echo off
setlocal
where py >nul 2>nul
if errorlevel 1 goto python_fallback
py -3 "%~dp0..\Auxillary\TEMP\scripts\run_temp.py" --package-root "%~dp0." --expected-platform windows %*
exit /b %errorlevel%
:python_fallback
python "%~dp0..\Auxillary\TEMP\scripts\run_temp.py" --package-root "%~dp0." --expected-platform windows %*
exit /b %errorlevel%
