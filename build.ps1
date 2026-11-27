param([Parameter(ValueFromRemainingArguments = $true)][string[]] $LakeArguments)

$ErrorActionPreference = 'Stop'
$toolchain = (& lean --print-prefix).Trim()
if ($LASTEXITCODE -ne 0) { throw 'Could not locate the pinned Lean toolchain.' }

$sequentialToolchain = Join-Path $PSScriptRoot '.lake/lean-sequential'
$bin = Join-Path $sequentialToolchain 'bin'
New-Item -ItemType Directory -Path $bin -Force | Out-Null

foreach ($name in @('lib', 'src', 'include', 'share')) {
    $source = Join-Path $toolchain $name
    $junction = Join-Path $sequentialToolchain $name
    if ((Test-Path -LiteralPath $source) -and !(Test-Path -LiteralPath $junction)) {
        New-Item -ItemType Junction -Path $junction -Target $source | Out-Null
    }
}

# The pinned strict E-value library builds with sequential elaboration in upstream CI.
$launcher = Join-Path $bin 'lean.exe'
if (!(Test-Path -LiteralPath $launcher)) {
    Add-Type -OutputAssembly $launcher -OutputType ConsoleApplication -TypeDefinition @'
using System;
using System.Diagnostics;

internal static class LeanLauncher
{
    private static int Main()
    {
        string command = Environment.CommandLine;
        int start = command.StartsWith("\"") ? command.IndexOf('"', 1) + 1 : command.IndexOf(' ');
        string arguments = start > 0 ? command.Substring(start) : "";
        string lean = Environment.GetEnvironmentVariable("WIDEE_BUILD_REAL_LEAN");
        using (Process process = Process.Start(new ProcessStartInfo(lean, "-j1 -DElab.async=false " + arguments)
            { UseShellExecute = false }))
        {
            process.WaitForExit();
            return process.ExitCode;
        }
    }
}
'@
}

if (!$LakeArguments) { $LakeArguments = @('build') }
$env:WIDEE_BUILD_REAL_LEAN = Join-Path $toolchain 'bin/lean.exe'
$env:LAKE_OVERRIDE_LEAN = 'true'
$env:LEAN_SYSROOT = $sequentialToolchain
& (Join-Path $toolchain 'bin/lake.exe') @LakeArguments
exit $LASTEXITCODE
