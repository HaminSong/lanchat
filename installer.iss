; LAN Chat installer script (Inno Setup 6)
; To release a new version, bump MyAppVersion (and version_info.txt).

#define MyAppName "LAN Chat"
#define MyAppVersion "1.0.6"
#define MyAppPublisher "LAN Chat"
#define MyAppExeName "LANChat.exe"

[Setup]
AppId={{8F3C2A51-6B7D-4E2A-9C1F-5A7E0B3D4C21}
AppName={#MyAppName}
AppVersion={#MyAppVersion}
AppVerName={#MyAppName} {#MyAppVersion}
AppPublisher={#MyAppPublisher}
DefaultDirName={autopf}\LAN Chat
DisableProgramGroupPage=yes
OutputDir=installer
OutputBaseFilename=LANChat-Setup
SetupIconFile=app.ico
UninstallDisplayIcon={app}\{#MyAppExeName}
UninstallDisplayName={#MyAppName}
Compression=lzma2/max
SolidCompression=yes
WizardStyle=modern
PrivilegesRequired=admin
ArchitecturesAllowed=x64compatible
ArchitecturesInstallIn64BitMode=x64compatible
AppMutex=LANChat_SingleInstance_Mutex
CloseApplications=yes
ShowLanguageDialog=no
LanguageDetectionMethod=none

[Languages]
Name: "english"; MessagesFile: "compiler:Default.isl"

[CustomMessages]
TaskDesktop=Create a desktop shortcut
TaskAutostart=Start LAN Chat when Windows starts
TaskGroup=Additional tasks:
Firewall=Configuring firewall...
Launch=Launch LAN Chat

[Tasks]
Name: "desktopicon"; Description: "{cm:TaskDesktop}"; GroupDescription: "{cm:TaskGroup}"
Name: "autostart"; Description: "{cm:TaskAutostart}"; GroupDescription: "{cm:TaskGroup}"; Flags: unchecked

[Files]
Source: "dist\LANChat\*"; DestDir: "{app}"; Flags: ignoreversion recursesubdirs createallsubdirs

[Icons]
Name: "{autoprograms}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"
Name: "{autodesktop}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Tasks: desktopicon
Name: "{userstartup}\{#MyAppName}"; Filename: "{app}\{#MyAppExeName}"; Parameters: "--minimized"; Tasks: autostart

[Run]
; Firewall: allow inbound on Private/Domain networks only
Filename: "{sys}\netsh.exe"; Parameters: "advfirewall firewall delete rule name=""LAN Chat"""; Flags: runhidden
Filename: "{sys}\netsh.exe"; Parameters: "advfirewall firewall add rule name=""LAN Chat"" dir=in action=allow program=""{app}\{#MyAppExeName}"" enable=yes profile=private,domain"; Flags: runhidden; StatusMsg: "{cm:Firewall}"
Filename: "{app}\{#MyAppExeName}"; Description: "{cm:Launch}"; Flags: nowait postinstall skipifsilent

[UninstallRun]
Filename: "{sys}\netsh.exe"; Parameters: "advfirewall firewall delete rule name=""LAN Chat"""; Flags: runhidden; RunOnceId: "RemoveFirewallRule"
