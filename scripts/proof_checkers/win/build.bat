@echo off
rem Build dpr-trim and dsr-trim from the vendored third_party sources with MSVC.
rem
rem Usage:  scripts\proof_checkers\win\build.bat [output-dir]
rem Default output-dir is scripts\proof_checkers\win\bin.
rem
rem The checker sources are used BYTE-IDENTICAL to upstream. Everything Windows
rem needs is supplied as headers on the include path (sys/time.h, unistd.h,
rem getopt.h) plus one force-included compatibility header. A checker is the
rem trust root for a certificate claim, so it must never be patched to make a
rem proof pass.
rem
rem /Dinline= is required for dsr-trim: its sources use the C99 extern-inline
rem pattern (definition in a .c, plain prototype in a .h) that GCC emits a symbol
rem for and MSVC's C mode does not. The sources define no inline functions in
rem headers, so this only turns them into ordinary functions. It is also why the
rem shims never include <windows.h>/<winsock2.h> -- those DO define inline
rem functions, which would then collide.

setlocal
set "HERE=%~dp0"
set "REPO=%HERE%..\..\.."
set "OUT=%~1"
if "%OUT%"=="" set "OUT=%HERE%bin"
rem HERE ends with a backslash; a trailing \ immediately before a closing quote
rem is parsed by MSVC as an ESCAPED QUOTE, which swallows the rest of the command
rem line ("cl : Command line error D8003"). Keep a backslash-free copy for /I.
set "INC=%HERE:~0,-1%"

set "VCVARS="
for /f "delims=" %%V in ('where /r "C:\Program Files (x86)\Microsoft Visual Studio" vcvars64.bat 2^>nul') do set "VCVARS=%%V"
if not defined VCVARS for /f "delims=" %%V in ('where /r "C:\Program Files\Microsoft Visual Studio" vcvars64.bat 2^>nul') do set "VCVARS=%%V"
if not defined VCVARS (
  echo ERROR: vcvars64.bat not found -- install MSVC Build Tools
  exit /b 1
)
call "%VCVARS%" >nul 2>&1

if not exist "%OUT%" mkdir "%OUT%"
if not exist "%OUT%\obj" mkdir "%OUT%\obj"

set "SRC=%REPO%\third_party\dsr-trim\src"
set "DSRFILES=%SRC%\dsr-trim.c %SRC%\bitmask.c %SRC%\cli.c %SRC%\cnf_parser.c %SRC%\global_data.c %SRC%\global_parsing.c %SRC%\hash_table.c %SRC%\lit_occ.c %SRC%\logger.c %SRC%\range_array.c %SRC%\sr_parser.c %SRC%\timer.c %SRC%\xio.c %SRC%\xmalloc.c"

echo Building dpr-trim...
cl /nologo /O2 /wd4996 /wd4005 /FI"%HERE%ay_force.h" /I"%INC%" /Fe:"%OUT%\dpr-trim.exe" /Fo:"%OUT%\obj\\" "%REPO%\third_party\dpr-trim\dpr-trim.c"
if errorlevel 1 exit /b 1

echo Building dsr-trim...
cl /nologo /O2 /wd4996 /wd4005 /wd4013 /Dinline= /FI"%HERE%ay_force.h" /I"%INC%" /Fe:"%OUT%\dsr-trim.exe" /Fo:"%OUT%\obj\\" %DSRFILES%
if errorlevel 1 exit /b 1

echo.
echo Built: %OUT%\dpr-trim.exe
echo Built: %OUT%\dsr-trim.exe
endlocal
