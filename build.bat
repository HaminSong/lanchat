@echo off
setlocal
cd /d "%~dp0"

echo ==================================================
echo  LAN Chat build
echo ==================================================

if /i "%~1"=="installer" goto :step3

echo.
echo [1/3] Installing packages (pywebview, pystray, pillow, segno, pyinstaller)...
py -m pip install --upgrade pywebview pystray pillow segno pyinstaller
if errorlevel 1 goto :err

echo.
echo [2/3] Building app...
py -m PyInstaller --noconfirm --clean --windowed --onedir --name LANChat --icon app.ico --version-file version_info.txt --hidden-import pystray._win32 lanchat.py
if errorlevel 1 goto :err

:step3
echo.
echo [3/3] Building installer...
if not exist "dist\LANChat\LANChat.exe" (
  echo dist\LANChat\LANChat.exe not found. Run build.bat without arguments first.
  goto :err
)
call :findiscc
if not defined ISCC call :installinno
if not defined ISCC goto :noinno

set TRIES=0
:iscc_retry
set /a TRIES+=1
"%ISCC%" installer.iss
if not errorlevel 1 goto :done
if %TRIES% GEQ 4 goto :avhint
echo.
echo Antivirus may be scanning the new file. Retrying in 5 seconds... (%TRIES%/3)
timeout /t 5 /nobreak >nul
goto :iscc_retry

:done
echo.
echo ==================================================
echo  DONE: installer\LANChat-Setup.exe
echo ==================================================
start "" explorer "%~dp0installer"
pause
exit /b 0

:findiscc
set "ISCC="
if exist "%ProgramFiles(x86)%\Inno Setup 6\ISCC.exe" set "ISCC=%ProgramFiles(x86)%\Inno Setup 6\ISCC.exe"
if exist "%ProgramFiles%\Inno Setup 6\ISCC.exe" set "ISCC=%ProgramFiles%\Inno Setup 6\ISCC.exe"
if exist "%LocalAppData%\Programs\Inno Setup 6\ISCC.exe" set "ISCC=%LocalAppData%\Programs\Inno Setup 6\ISCC.exe"
exit /b 0

:installinno
echo Inno Setup not found. Installing with winget...
winget install -e --id JRSoftware.InnoSetup --accept-package-agreements --accept-source-agreements
call :findiscc
exit /b 0

:noinno
echo.
echo Inno Setup could not be installed automatically.
echo Download and install it from https://jrsoftware.org/isdl.php then run this file again.
echo (The app itself was built: dist\LANChat\LANChat.exe)
pause
exit /b 1

:avhint
echo.
echo *** The installer could not be written (usually antivirus locking the file). ***
echo Add this folder to Windows Security exclusions, then run make_installer.bat:
echo    %~dp0installer
echo (Windows Security - Virus ^& threat protection - Manage settings - Exclusions)
pause
exit /b 1

:err
echo.
echo *** Build failed. Please send a screenshot of the messages above. ***
pause
exit /b 1
