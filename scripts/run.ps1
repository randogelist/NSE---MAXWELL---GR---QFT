[CmdletBinding()]
param(
    [string]$ReportDirectory = "artifacts/external-windows",
    [string]$PythonExecutable = ""
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"
if ($env:OS -ne "Windows_NT") {
    throw "EXTERNAL_NATIVE_WINDOWS_REQUIRED"
}

$RepoRoot = Split-Path -Parent $PSScriptRoot
Set-Location -LiteralPath $RepoRoot
$ReportRoot = Join-Path $RepoRoot $ReportDirectory
$null = New-Item -ItemType Directory -Path $ReportRoot -Force
$ExpectedToolchain = "leanprover/lean4:v4.34.0-rc1"
$ExpectedMathlib = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
$Utf8NoBom = [Text.UTF8Encoding]::new($false)
[Console]::OutputEncoding = $Utf8NoBom
$OutputEncoding = $Utf8NoBom
$env:ELAN_TOOLCHAIN = $ExpectedToolchain
# Lake must supply the module search path for the pinned dependency graph.
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
Remove-Item Env:LEAN_SRC_PATH -ErrorAction SilentlyContinue

function Write-JsonFile {
    param([string]$Path, [object]$Value)
    $Json = ConvertTo-Json -InputObject $Value -Depth 30
    [IO.File]::WriteAllText($Path, $Json + [Environment]::NewLine, $Utf8NoBom)
}

function Invoke-NativeLogged {
    param(
        [string]$Executable,
        [string[]]$Arguments,
        [string]$LogName,
        [switch]$AllowFailure
    )
    $LogPath = Join-Path $ReportRoot $LogName
    $Writer = [IO.StreamWriter]::new($LogPath, $false, $Utf8NoBom)
    $Writer.AutoFlush = $true
    $PreviousPreference = $ErrorActionPreference
    $NativeExitCode = $null
    try {
        # Windows PowerShell represents native stderr as ErrorRecord objects.
        # Exit status, not the presence of stderr, determines command success.
        $ErrorActionPreference = "Continue"
        & $Executable @Arguments 2>&1 | ForEach-Object {
            $Line = $_.ToString()
            $Writer.WriteLine($Line)
            Write-Host $Line
        }
        $NativeExitCode = $LASTEXITCODE
    }
    finally {
        $ErrorActionPreference = $PreviousPreference
        $Writer.Dispose()
    }
    if ($null -eq $NativeExitCode) {
        throw "Native command did not supply an exit code: $Executable"
    }
    if (($NativeExitCode -ne 0) -and -not $AllowFailure) {
        throw "Native command failed ($NativeExitCode): $Executable; log=$LogName"
    }
    return [int]$NativeExitCode
}

$ProvenancePath = Join-Path $ReportRoot "run-provenance.json"
$Evidence = [ordered]@{
    schema_version = 1
    started_at_utc = [DateTime]::UtcNow.ToString("o")
    external_native_windows = $true
    os = [Environment]::OSVersion.VersionString
    powershell_version = $PSVersionTable.PSVersion.ToString()
    processor_count = [Environment]::ProcessorCount
    requested_toolchain = $ExpectedToolchain
    requested_mathlib_commit = $ExpectedMathlib
    source_commit = $null
    github_run_id = $env:GITHUB_RUN_ID
    github_run_attempt = $env:GITHUB_RUN_ATTEMPT
    github_repository = $env:GITHUB_REPOSITORY
    stage = "INITIALIZE"
    build_status = "NOT_RUN"
    audit_command_status = "NOT_RUN"
    theorem_axiom_audit_status = "NOT_RUN"
    exact_root_promotion = "NOT_AUTOMATIC"
}
Write-JsonFile $ProvenancePath $Evidence

try {
    if ((Get-Content "lean-toolchain" -Raw).Trim() -ne $ExpectedToolchain) {
        throw "lean-toolchain does not match the pinned compiler."
    }
    $null = Get-Command "lake" -ErrorAction Stop
    $null = Get-Command "git" -ErrorAction Stop
    foreach ($Required in @(
        "NSEMaxwell.lean", "NSEMaxwell/Audit.lean", "audit-targets.txt",
        "formalization-status.json", "scripts/verify_audit.py"
    )) {
        if (-not (Test-Path -LiteralPath $Required -PathType Leaf)) {
            throw "Required input is absent: $Required"
        }
    }

    $PythonPrefix = @()
    if ($PythonExecutable) {
        $null = Get-Command $PythonExecutable -ErrorAction Stop
    }
    elseif (Get-Command "python" -ErrorAction SilentlyContinue) {
        $PythonExecutable = "python"
    }
    elseif (Get-Command "py" -ErrorAction SilentlyContinue) {
        $PythonExecutable = "py"
        $PythonPrefix = @("-3")
    }
    else {
        throw "Python 3.9 or later is required for the evidence verifier."
    }

    $Evidence.stage = "COMPILER_VERSION"
    $null = Invoke-NativeLogged "lake" @("env", "lean", "--version") "lean-version.log"
    $Version = (Get-Content (Join-Path $ReportRoot "lean-version.log") -Raw).Trim()
    if ($Version -notmatch "version 4\.34\.0-rc1(?:,|\))") {
        throw "The external compiler version is not Lean 4.34.0-rc1."
    }
    $Evidence.actual_lean_version = $Version

    $Evidence.stage = "DEPENDENCY_RESOLUTION"
    if ((-not (Test-Path "lake-manifest.json")) -or
        (-not (Test-Path ".lake/packages/mathlib/lakefile.lean"))) {
        $null = Invoke-NativeLogged "lake" @("update") "dependency-resolution.log"
    }
    $LakeManifest = Get-Content "lake-manifest.json" -Raw | ConvertFrom-Json
    $MathlibPackage = @($LakeManifest.packages | Where-Object { $_.name -eq "mathlib" })
    if (($MathlibPackage.Count -ne 1) -or ($MathlibPackage[0].rev -ne $ExpectedMathlib)) {
        throw "The Lake manifest does not pin the approved Mathlib commit."
    }
    $null = Invoke-NativeLogged "git" @(
        "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"
    ) "mathlib-revision.log"
    $MathlibRevision = (Get-Content (Join-Path $ReportRoot "mathlib-revision.log") -Raw).Trim()
    if ($MathlibRevision -ne $ExpectedMathlib) {
        throw "The Mathlib checkout does not match the pinned commit."
    }
    $null = Invoke-NativeLogged "git" @(
        "-C", ".lake/packages/mathlib", "status", "--porcelain", "--untracked-files=no"
    ) "mathlib-working-tree.log"
    if ((Get-Item (Join-Path $ReportRoot "mathlib-working-tree.log")).Length -ne 0) {
        throw "The pinned Mathlib checkout contains tracked modifications."
    }
    $Evidence.actual_mathlib_commit = $MathlibRevision

    $Evidence.stage = "CACHE"
    $CacheTargets = [Collections.Generic.HashSet[string]]::new()
    if (Test-Path "cache-targets.txt") {
        foreach ($Line in Get-Content "cache-targets.txt") {
            $Target = $Line.Trim()
            if ($Target -and -not $Target.StartsWith("#")) {
                $null = $CacheTargets.Add($Target)
            }
        }
    }
    else {
        $LeanSources = @(Get-ChildItem "NSEMaxwell" -Recurse -File -Filter "*.lean")
        $LeanSources += Get-Item "NSEMaxwell.lean"
        foreach ($Source in $LeanSources) {
            foreach ($Line in Get-Content -LiteralPath $Source.FullName) {
                if ($Line -match '^\s*(?:public\s+)?import\s+(.+)$') {
                    $ImportText = ($Matches[1] -split "--", 2)[0]
                    foreach ($Token in ($ImportText -split '\s+')) {
                        if ($Token -match '^Mathlib(?:\.[A-Za-z0-9_]+)*$') {
                            $null = $CacheTargets.Add($Token)
                        }
                    }
                }
            }
        }
    }
    $SortedTargets = @($CacheTargets | Sort-Object)
    if ($SortedTargets.Count -eq 0) {
        throw "No Mathlib cache targets found; supply cache-targets.txt."
    }
    foreach ($Target in $SortedTargets) {
        if ($Target -notmatch '^Mathlib(?:\.[A-Za-z0-9_]+)*$') {
            throw "Invalid Mathlib cache target: $Target"
        }
    }
    $CacheArguments = @("exe", "cache", "get", "--cache-from=master,legacy") + $SortedTargets
    $null = Invoke-NativeLogged "lake" $CacheArguments "run-cache.log"
    $Evidence.cache_targets = $SortedTargets
    foreach ($Target in $SortedTargets) {
        $RelativeOlean = $Target.Replace(".", "/") + ".olean"
        $Olean = Join-Path ".lake/packages/mathlib/.lake/build/lib/lean" $RelativeOlean
        if (-not (Test-Path -LiteralPath $Olean -PathType Leaf)) {
            throw "Cached Mathlib artifact is absent: $RelativeOlean"
        }
    }

    $Evidence.stage = "SOURCE_MANIFEST"
    $Inputs = [Collections.Generic.HashSet[string]]::new()
    $GitCode = Invoke-NativeLogged "git" @("rev-parse", "HEAD") "source-commit.log" -AllowFailure
    if ($GitCode -eq 0) {
        $Evidence.source_commit = (Get-Content (Join-Path $ReportRoot "source-commit.log") -Raw).Trim()
        $null = Invoke-NativeLogged "git" @("status", "--porcelain") "working-tree.log"
        $null = Invoke-NativeLogged "git" @("ls-files") "tracked-files.log"
        foreach ($Path in Get-Content (Join-Path $ReportRoot "tracked-files.log")) {
            $null = $Inputs.Add($Path.Replace("\", "/"))
        }
    }
    else {
        foreach ($File in Get-ChildItem $RepoRoot -Recurse -File) {
            $Relative = $File.FullName.Substring($RepoRoot.Length + 1).Replace("\", "/")
            if ($Relative -notmatch '^(\.lake|\.git|artifacts|\.mathlib-download-cache)/') {
                $null = $Inputs.Add($Relative)
            }
        }
    }
    # Hash untracked project source inputs as well as the resolved lockfile.
    foreach ($Source in Get-ChildItem "NSEMaxwell" -Recurse -File -Filter "*.lean") {
        $null = $Inputs.Add($Source.FullName.Substring($RepoRoot.Length + 1).Replace("\", "/"))
    }
    foreach ($Required in @(
        "lean-toolchain", "lake-manifest.json", "NSEMaxwell.lean",
        "NSEMaxwell/Audit.lean", "audit-targets.txt", "formalization-status.json",
        "scripts/run.ps1", "scripts/verify_audit.py", "run.cmd"
    )) {
        $null = $Inputs.Add($Required)
    }
    foreach ($Optional in @("lakefile.lean", "lakefile.toml", "cache-targets.txt")) {
        if (Test-Path -LiteralPath $Optional -PathType Leaf) { $null = $Inputs.Add($Optional) }
    }
    $SourceFiles = @(
        foreach ($Relative in ($Inputs | Sort-Object)) {
            $Path = Join-Path $RepoRoot $Relative
            if (Test-Path -LiteralPath $Path -PathType Leaf) {
                [ordered]@{
                    path = $Relative
                    sha256 = (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()
                    size_bytes = (Get-Item -LiteralPath $Path).Length
                }
            }
        }
    )
    $ManifestPath = Join-Path $ReportRoot "source-manifest.json"
    Write-JsonFile $ManifestPath ([ordered]@{
        schema_version = 1
        algorithm = "SHA256"
        source_commit = $Evidence.source_commit
        files = $SourceFiles
    })
    $Evidence.source_manifest_sha256 = (Get-FileHash -LiteralPath $ManifestPath -Algorithm SHA256).Hash.ToLowerInvariant()

    $Evidence.stage = "BUILD"
    # Bound concurrent heavy imports on native Windows without disabling Lean's
    # asynchronous theorem elaboration. Every dependency precedes its consumer;
    # each invocation reuses all already compiled and restored Lake artifacts.
    $BuildModules = @(
        "NSEMaxwell.Classical",
        "NSEMaxwell.Kinematics",
        "NSEMaxwell.Constitutive",
        "NSEMaxwell.Negation",
        "NSEMaxwell.Lamb",
        "NSEMaxwell.Pressure",
        "NSEMaxwell.ConstantPaths",
        "NSEMaxwell.Ampere",
        "NSEMaxwell.CurlCurl",
        "NSEMaxwell.PeriodicIntegration",
        "NSEMaxwell.Spacetime",
        "NSEMaxwell.FourierPeriodic",
        "NSEMaxwell.DominatedWithin",
        "NSEMaxwell.LocalEvolution",
        "NSEMaxwell.TemporalMean",
        "NSEMaxwell.MeanConservation",
        "NSEMaxwell.Residual",
        "NSEMaxwell.ExistenceTransport",
        "NSEMaxwell.AnalyticBridge",
        "NSEMaxwell.AnalyticReduction",
        "NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE"
    )
    $Evidence.module_build_schedule = $BuildModules
    $Evidence.module_build_concurrency = 1
    $FailedModules = [Collections.Generic.List[string]]::new()
    $SkippedModules = [Collections.Generic.List[string]]::new()
    $Evidence.failed_modules = @()
    $Evidence.skipped_modules = @()
    Write-JsonFile $ProvenancePath $Evidence
    foreach ($Module in $BuildModules) {
        $Evidence.current_build_module = $Module
        $ModuleLog = "run-build-" + $Module.Replace(".", "-") + ".log"
        $SourcePath = $Module.Replace(".", "/") + ".lean"
        $Dependencies = @()
        foreach ($Line in Get-Content -LiteralPath $SourcePath) {
            if ($Line -match '^import\s+(.+)$') {
                $Dependencies += $Matches[1].Trim().Split(' ', [StringSplitOptions]::RemoveEmptyEntries)
            }
        }
        $Blocked = @($Dependencies | Where-Object { $FailedModules.Contains($_) -or $SkippedModules.Contains($_) })
        if ($Blocked.Count -gt 0) {
            $SkippedModules.Add($Module)
            $Evidence.skipped_modules = @($SkippedModules.ToArray())
            [IO.File]::WriteAllText((Join-Path $ReportRoot $ModuleLog),
                "SKIPPED_FAILED_DEPENDENCY: " + ($Blocked -join ", ") + [Environment]::NewLine, $Utf8NoBom)
            Write-JsonFile $ProvenancePath $Evidence
            continue
        }
        Write-JsonFile $ProvenancePath $Evidence
        $ModuleExitCode = Invoke-NativeLogged "lake" @("build", $Module) $ModuleLog -AllowFailure
        if ($ModuleExitCode -ne 0) {
            $FailedModules.Add($Module)
            $Evidence.failed_modules = @($FailedModules.ToArray())
            Write-JsonFile $ProvenancePath $Evidence
        }
    }
    if ($FailedModules.Count -gt 0) {
        $Evidence.build_status = "FAIL"
        Write-JsonFile $ProvenancePath $Evidence
        throw ("Lean module failures: " + ($FailedModules -join ", "))
    }
    $Evidence.current_build_module = "NSEMaxwell"
    Write-JsonFile $ProvenancePath $Evidence
    $null = Invoke-NativeLogged "lake" @("build", "NSEMaxwell") "run-build.log"
    $Evidence.build_status = "PASS"

    $Evidence.stage = "AXIOM_AUDIT"
    Write-JsonFile $ProvenancePath $Evidence
    $null = Invoke-NativeLogged "lake" @("env", "lean", "NSEMaxwell/Audit.lean") "run-audit.log"
    $Evidence.audit_command_status = "PASS"

    $Evidence.stage = "VERIFY_EVIDENCE"
    Write-JsonFile $ProvenancePath $Evidence
    $VerifierArguments = $PythonPrefix + @(
        "scripts/verify_audit.py",
        "--root", $RepoRoot,
        "--targets", "audit-targets.txt",
        "--audit-source", "NSEMaxwell/Audit.lean",
        "--log", (Join-Path $ReportRoot "run-audit.log"),
        "--manifest", $ManifestPath,
        "--provenance", $ProvenancePath,
        "--scope", "formalization-status.json",
        "--output", (Join-Path $ReportRoot "audit-summary.json")
    )
    $null = Invoke-NativeLogged $PythonExecutable $VerifierArguments "audit-verifier.log"
    $Evidence.theorem_axiom_audit_status = "PASS_STANDARD_ONLY"
    $Evidence.stage = "COMPLETE"
    $Evidence.completed_at_utc = [DateTime]::UtcNow.ToString("o")
    Write-JsonFile $ProvenancePath $Evidence
    Write-Host "EXTERNAL_COMPILER=PASS"
    Write-Host "THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY"
    Write-Host "EXACT_ROOT_PROMOTION=NOT_AUTOMATIC"
    exit 0
}
catch {
    $Evidence.failure = $_.Exception.Message
    $Evidence.completed_at_utc = [DateTime]::UtcNow.ToString("o")
    Write-JsonFile $ProvenancePath $Evidence
    Write-Host ("EXTERNAL_RUN=FAIL: " + $_.Exception.Message)
    exit 1
}
