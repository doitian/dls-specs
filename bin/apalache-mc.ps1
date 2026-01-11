# Find the apalache-mc.bat file in ~/.quint/apalache-dist-*/apalache/bin/
$apalacheDistPath = Get-ChildItem -Path "$env:USERPROFILE\.quint\apalache-dist-*\apalache\bin\apalache-mc.bat" -ErrorAction SilentlyContinue | Select-Object -First 1

if ($apalacheDistPath) {
    & $apalacheDistPath.FullName $args
} else {
    Write-Error "apalache-mc.bat not found in $env:USERPROFILE\.quint\apalache-dist-*\apalache\bin\"
    exit 1
}