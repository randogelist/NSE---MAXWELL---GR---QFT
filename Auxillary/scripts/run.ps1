[CmdletBinding()]
param(
    [string]$ReportDirectory = "",
    [string]$PythonExecutable = "",
    [ValidateSet("Auto", "Windows", "Linux")]
    [string]$ExpectedPlatform = "Auto",
    [ValidateSet("All", "Dependencies", "BuildAudit")]
    [string]$Phase = "All"
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"
if ($env:OS -eq "Windows_NT") {
    $NativePlatform = "windows"
}
elseif ([Runtime.InteropServices.RuntimeInformation]::IsOSPlatform(
    [Runtime.InteropServices.OSPlatform]::Linux)) {
    $NativePlatform = "linux"
}
else {
    throw "EXTERNAL_NATIVE_WINDOWS_OR_LINUX_REQUIRED"
}
if (($ExpectedPlatform -ne "Auto") -and
    ($ExpectedPlatform.ToLowerInvariant() -ne $NativePlatform)) {
    throw "The native platform does not match -ExpectedPlatform."
}
if (-not $ReportDirectory) {
    $ReportDirectory = "artifacts/external-" + $NativePlatform
}

$RepoRoot = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
Set-Location -LiteralPath $RepoRoot
$AdapterSourceRoot = "Fefferman_B_adapter"
$ForwardSourceRoot = "B <-> Maxwell/=>"
$ReverseSourceRoot = "B <-> Maxwell/<="
$MaxwellSourceRoot = "Maxwell_Endpoint"
$ProjectSourceRoots = @($AdapterSourceRoot, $ForwardSourceRoot, $ReverseSourceRoot)
$ProjectRootSource = "$AdapterSourceRoot/NSEMaxwell.lean"
$AuditSource = "$AdapterSourceRoot/NSEMaxwell/Audit.lean"
$VerifierSource = "Auxillary/scripts/verify_audit.py"
$AggregateTargets = @("MaxwellEndpoint", "NSEMaxwell", "NSEMaxwellForward.Reduced", "NSEMaxwellReverse.Reduced")
$ReportRoot = Join-Path $RepoRoot $ReportDirectory
$null = New-Item -ItemType Directory -Path $ReportRoot -Force
$ExpectedToolchain = "leanprover/lean4:v4.34.0-rc1"
$ExpectedMathlib = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
$Utf8NoBom = [Text.UTF8Encoding]::new($false)
[Console]::OutputEncoding = $Utf8NoBom
$OutputEncoding = $Utf8NoBom
$env:ELAN_TOOLCHAIN = $ExpectedToolchain
# Cache acquisition has one explicit, logged invocation. Lake's dependency
# post-update hook must not fetch the same Mathlib cache a second time.
$env:MATHLIB_NO_CACHE_ON_UPDATE = "1"
# Lake must supply the module search path for the pinned dependency graph.
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
Remove-Item Env:LEAN_SRC_PATH -ErrorAction SilentlyContinue
$CommandTimings = [Collections.Generic.List[object]]::new()

function Get-ProjectSourcePath {
    param([string]$Module)
    $Relative = $Module.Replace(".", "/") + ".lean"
    if ($Module -match '^MaxwellEndpoint(?:\.|$)') {
        return Join-Path $MaxwellSourceRoot $Relative
    }
    if ($Module -match '^NSEMaxwellForward(?:\.|$)') {
        return Join-Path $ForwardSourceRoot $Relative
    }
    if ($Module -match '^NSEMaxwellReverse(?:\.|$)') {
        return Join-Path $ReverseSourceRoot $Relative
    }
    if ($Module -match '^NSEMaxwell(?:\.|$)') {
        return Join-Path $AdapterSourceRoot $Relative
    }
    throw "No active project source root is registered for module: $Module"
}

function Get-ProjectLeanSources {
    foreach ($SourceRoot in $ProjectSourceRoots) {
        if (-not (Test-Path -LiteralPath $SourceRoot -PathType Container)) {
            throw "Active project source root is absent: $SourceRoot"
        }
        Get-ChildItem -LiteralPath $SourceRoot -Recurse -File -Filter "*.lean"
    }
    # Enumerate native package sources without descending into its separate caches.
    Get-Item -LiteralPath "$MaxwellSourceRoot/MaxwellEndpoint.lean"
    Get-ChildItem -LiteralPath "$MaxwellSourceRoot/MaxwellEndpoint" -Recurse -File -Filter "*.lean"
}

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
    $Started = [DateTime]::UtcNow
    $Timer = [Diagnostics.Stopwatch]::StartNew()
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
        $Timer.Stop()
        $CommandTimings.Add([ordered]@{
            executable = $Executable
            arguments = $Arguments
            log = $LogName
            started_at_utc = $Started.ToString("o")
            elapsed_seconds = [Math]::Round($Timer.Elapsed.TotalSeconds, 3)
            exit_code = $NativeExitCode
        })
        Write-JsonFile (Join-Path $ReportRoot ("command-timings-" + $Phase + ".json")) @($CommandTimings.ToArray())
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
    external_platform = $NativePlatform
    external_native_windows = ($NativePlatform -eq "windows")
    external_native_linux = ($NativePlatform -eq "linux")
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
    phase = $Phase
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
        $ProjectRootSource, $AuditSource, "Auxillary/audit-targets.txt",
        "Auxillary/formalization-status.json", $VerifierSource, "lake-manifest.json",
        "$ForwardSourceRoot/NSEMaxwellForward.lean",
        "$ForwardSourceRoot/NSEMaxwellForward/Reduced.lean",
        "$ReverseSourceRoot/NSEMaxwellReverse.lean",
        "$ReverseSourceRoot/NSEMaxwellReverse/Reduced.lean",
        "$MaxwellSourceRoot/MaxwellEndpoint.lean",
        "$MaxwellSourceRoot/MaxwellEndpoint/Audit.lean",
        "$MaxwellSourceRoot/lakefile.lean", "$MaxwellSourceRoot/lake-manifest.json",
        "$MaxwellSourceRoot/lean-toolchain", "$MaxwellSourceRoot/audit-targets.txt",
        "$MaxwellSourceRoot/cache-targets.txt", "$MaxwellSourceRoot/formalization-status.json",
        "$MaxwellSourceRoot/scripts/run.ps1", "$MaxwellSourceRoot/scripts/verify_audit.py",
        "$MaxwellSourceRoot/run.sh", "$MaxwellSourceRoot/run.cmd"
    )) {
        if (-not (Test-Path -LiteralPath $Required -PathType Leaf)) {
            throw "Required input is absent: $Required"
        }
    }
    $EntryPoint = if ($NativePlatform -eq "linux") { "Auxillary/run.sh" } else { "Auxillary/run.cmd" }
    if (-not (Test-Path -LiteralPath $EntryPoint -PathType Leaf)) {
        throw "Required platform entry point is absent: $EntryPoint"
    }

    $PythonPrefix = @()
    if ($PythonExecutable) {
        $null = Get-Command $PythonExecutable -ErrorAction Stop
    }
    elseif (Get-Command "python" -ErrorAction SilentlyContinue) {
        $PythonExecutable = "python"
    }
    elseif (Get-Command "python3" -ErrorAction SilentlyContinue) {
        $PythonExecutable = "python3"
    }
    elseif (Get-Command "py" -ErrorAction SilentlyContinue) {
        $PythonExecutable = "py"
        $PythonPrefix = @("-3")
    }
    else {
        throw "Python 3.9 or later is required for the evidence verifier."
    }

    $Evidence.stage = "COMPILER_VERSION"
    $null = Invoke-NativeLogged "lean" @("--version") "lean-version.log"
    $VersionLines = @(Get-Content (Join-Path $ReportRoot "lean-version.log") | Where-Object {
        $_ -match '^Lean \(version 4\.34\.0-rc1(?:,|\))'
    })
    if ($VersionLines.Count -ne 1) {
        throw "The external compiler version is not Lean 4.34.0-rc1."
    }
    # Elan may print installation diagnostics on a cold compiler cache. Only
    # the actual version record participates in dependency preparation reuse.
    $Version = $VersionLines[0].Trim()
    if ($Version -notmatch (",\s*[^,\s]*-" + $NativePlatform + "-[^,\s]*,")) {
        throw "The Lean compiler target does not match the native platform."
    }
    $Evidence.actual_lean_version = $Version

    $Evidence.stage = "DEPENDENCY_RESOLUTION"
    $LockfileHash = (Get-FileHash "lake-manifest.json" -Algorithm SHA256).Hash.ToLowerInvariant()
    $LakeManifest = Get-Content "lake-manifest.json" -Raw | ConvertFrom-Json
    $MathlibPackage = @($LakeManifest.packages | Where-Object { $_.name -eq "mathlib" })
    if (($MathlibPackage.Count -ne 1) -or ($MathlibPackage[0].rev -ne $ExpectedMathlib)) {
        throw "The Lake manifest does not pin the approved Mathlib commit."
    }
    $MissingPackages = @($LakeManifest.packages | Where-Object {
        -not (Test-Path (Join-Path (Join-Path ".lake/packages" $_.name) $_.configFile))
    })
    if ($MissingPackages.Count -gt 0) {
        # `lake env` materializes the committed lockfile without `lake update`.
        $null = Invoke-NativeLogged "lake" @("env", "lean", "--version") "dependency-resolution.log"
    }
    if ((Get-FileHash "lake-manifest.json" -Algorithm SHA256).Hash.ToLowerInvariant() -ne $LockfileHash) {
        throw "Dependency resolution modified the committed lockfile."
    }
    $DependencyRevisions = @(
        foreach ($Package in $LakeManifest.packages) {
            if (($Package.type -ne "git") -or ($Package.name -notmatch '^[A-Za-z0-9_-]+$') -or
                ($Package.rev -notmatch '^[a-f0-9]{40}$')) {
                throw "Invalid pinned dependency manifest entry."
            }
            $PackagePath = Join-Path ".lake/packages" $Package.name
            $RevisionLog = "dependency-" + $Package.name + "-revision.log"
            $null = Invoke-NativeLogged "git" @("-C", $PackagePath, "rev-parse", "HEAD") $RevisionLog
            $Revision = (Get-Content (Join-Path $ReportRoot $RevisionLog) -Raw).Trim()
            if ($Revision -ne $Package.rev) { throw "Dependency revision mismatch: $($Package.name)" }
            $StatusLog = "dependency-" + $Package.name + "-working-tree.log"
            $null = Invoke-NativeLogged "git" @(
                "-C", $PackagePath, "status", "--porcelain", "--untracked-files=no"
            ) $StatusLog
            if ((Get-Item (Join-Path $ReportRoot $StatusLog)).Length -ne 0) {
                throw "Tracked dependency modifications: $($Package.name)"
            }
            [ordered]@{ name = $Package.name; revision = $Revision }
        }
    )
    $Evidence.dependency_revisions = $DependencyRevisions
    $Evidence.lockfile_sha256 = $LockfileHash
    Copy-Item "lake-manifest.json" (Join-Path $ReportRoot "resolved-lake-manifest.json") -Force
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
    if (Test-Path "Auxillary/cache-targets.txt") {
        foreach ($Line in Get-Content "Auxillary/cache-targets.txt") {
            $Target = $Line.Trim()
            if ($Target -and -not $Target.StartsWith("#")) {
                $null = $CacheTargets.Add($Target)
            }
        }
    }
    else {
        $LeanSources = @(Get-ProjectLeanSources)
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
        throw "No Mathlib cache targets found; supply Auxillary/cache-targets.txt."
    }
    foreach ($Target in $SortedTargets) {
        if ($Target -notmatch '^Mathlib(?:\.[A-Za-z0-9_]+)*$') {
            throw "Invalid Mathlib cache target: $Target"
        }
    }
    $DependencyInputLines = @(
        "platform=" + $NativePlatform
        "toolchain=" + $ExpectedToolchain
        "compiler=" + $Version
        foreach ($InputPath in @("lean-toolchain", "lakefile.lean", "lake-manifest.json")) {
            $InputPath + "=" + (Get-FileHash $InputPath -Algorithm SHA256).Hash.ToLowerInvariant()
        }
        "targets=" + ($SortedTargets -join ",")
    )
    $Hasher = [Security.Cryptography.SHA256]::Create()
    try {
        $DependencyFingerprint = [BitConverter]::ToString(
            $Hasher.ComputeHash($Utf8NoBom.GetBytes(($DependencyInputLines -join "`n")))
        ).Replace("-", "").ToLowerInvariant()
    }
    finally { $Hasher.Dispose() }
    $PreparationPath = Join-Path $ReportRoot "dependency-preparation.json"
    if ($Phase -eq "BuildAudit") {
        if (-not (Test-Path $PreparationPath -PathType Leaf)) {
            throw "BuildAudit requires a successful Dependencies phase in this report directory."
        }
        $Prepared = Get-Content $PreparationPath -Raw | ConvertFrom-Json
        if (($Prepared.status -ne "PASS") -or ($Prepared.dependency_fingerprint -ne $DependencyFingerprint)) {
            throw "Prepared dependencies do not match the current pinned inputs and compiler."
        }
        $Evidence.cache_mode = "REUSE_VERIFIED_DEPENDENCY_PHASE"
    }
    else {
        $CacheArguments = @("exe", "cache", "get", "--cache-from=master,legacy") + $SortedTargets
        $null = Invoke-NativeLogged "lake" $CacheArguments "run-cache.log"
        $Evidence.cache_mode = "OFFICIAL_INCREMENTAL_CACHE_GET"
    }
    $Evidence.cache_targets = $SortedTargets
    foreach ($Target in $SortedTargets) {
        $RelativeOlean = $Target.Replace(".", "/") + ".olean"
        $Olean = Join-Path ".lake/packages/mathlib/.lake/build/lib/lean" $RelativeOlean
        if (-not (Test-Path -LiteralPath $Olean -PathType Leaf)) {
            throw "Cached Mathlib artifact is absent: $RelativeOlean"
        }
    }
    if ((Get-FileHash "lake-manifest.json" -Algorithm SHA256).Hash.ToLowerInvariant() -ne $LockfileHash) {
        throw "Cache preparation modified the committed lockfile."
    }
    if ($Phase -ne "BuildAudit") {
        Write-JsonFile $PreparationPath ([ordered]@{
            schema_version = 1
            status = "PASS"
            external_platform = $NativePlatform
            dependency_fingerprint = $DependencyFingerprint
            dependency_inputs = $DependencyInputLines
            cache_targets = $SortedTargets
            dependency_revisions = $DependencyRevisions
            completed_at_utc = [DateTime]::UtcNow.ToString("o")
            proof_or_audit_reuse = $false
        })
    }
    $Evidence.dependency_cache_status = "VERIFIED"
    $Evidence.dependency_preparation_sha256 = (Get-FileHash $PreparationPath -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($Phase -eq "Dependencies") {
        $Evidence.stage = "DEPENDENCIES_COMPLETE"
        $Evidence.completed_at_utc = [DateTime]::UtcNow.ToString("o")
        Write-JsonFile $ProvenancePath $Evidence
        Write-Host "PINNED_DEPENDENCY_CACHE=VERIFIED"
        exit 0
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
    foreach ($Source in Get-ProjectLeanSources) {
        $null = $Inputs.Add($Source.FullName.Substring($RepoRoot.Length + 1).Replace("\", "/"))
    }
    foreach ($Required in @(
        "lean-toolchain", "lake-manifest.json", $ProjectRootSource,
        $AuditSource, "Auxillary/audit-targets.txt", "Auxillary/formalization-status.json",
        "Auxillary/scripts/run.ps1", $VerifierSource, "Auxillary/run.cmd",
        "$MaxwellSourceRoot/lakefile.lean", "$MaxwellSourceRoot/lake-manifest.json",
        "$MaxwellSourceRoot/lean-toolchain", "$MaxwellSourceRoot/audit-targets.txt",
        "$MaxwellSourceRoot/cache-targets.txt", "$MaxwellSourceRoot/formalization-status.json",
        "$MaxwellSourceRoot/scripts/run.ps1", "$MaxwellSourceRoot/scripts/verify_audit.py",
        "$MaxwellSourceRoot/run.sh", "$MaxwellSourceRoot/run.cmd",
        "Auxillary/scripts/isolate_maxwell_endpoint.py"
    )) {
        $null = $Inputs.Add($Required)
    }
    $null = $Inputs.Add($EntryPoint)
    foreach ($Optional in @("lakefile.lean", "lakefile.toml", "Auxillary/cache-targets.txt")) {
        if (Test-Path -LiteralPath $Optional -PathType Leaf) { $null = $Inputs.Add($Optional) }
    }
    $SourceFiles = @(
        foreach ($Relative in ($Inputs | Sort-Object)) {
            $Path = Join-Path $RepoRoot $Relative
            if (Test-Path -LiteralPath $Path -PathType Leaf) {
                [ordered]@{
                    path = $Relative
                    sha256 = (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()
                    # Unix dotfiles carry PowerShell's Hidden attribute even
                    # when their exact literal path is supplied.
                    size_bytes = (Get-Item -LiteralPath $Path -Force).Length
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
    # Bound concurrent heavy imports on each native platform without disabling Lean's
    # asynchronous theorem elaboration. Every dependency precedes its consumer;
    # each invocation reuses all already compiled and restored Lake artifacts.
    $BuildModules = @(
        "MaxwellEndpoint.Geometry",
        "MaxwellEndpoint.Constitutive",
        "MaxwellEndpoint.System",
        "MaxwellEndpoint.Native",
        "MaxwellEndpoint",
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
        "NSEMaxwell.AnalyticContracts",
        "NSEMaxwellForward",
        "NSEMaxwellReverse",
        "NSEMaxwell.AnalyticBridge",
        "NSEMaxwell.CanonicalSmoothness",
        "NSEMaxwell.AnalyticReduction",
        "NSEMaxwellForward.Reduced",
        "NSEMaxwellReverse.Reduced",
        "NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE"
    )
    $Evidence.module_build_schedule = $BuildModules
    $Evidence.module_build_concurrency = 1
    $Evidence.aggregate_build_targets = $AggregateTargets
    # The official no-build mode validates the ordinary transitive Lake traces.
    # Exit 0 certifies freshness; exit 3 requests the bounded compilation path.
    # No cached theorem-audit output participates in either branch.
    $FreshnessExit = Invoke-NativeLogged "lake" (@("build", "--no-build") + $AggregateTargets) `
        "run-build-freshness.log" -AllowFailure
    $Evidence.freshness_check_exit_code = $FreshnessExit
    $Evidence.failed_modules = @()
    $Evidence.skipped_modules = @()
    if ($FreshnessExit -eq 0) {
        $Evidence.build_strategy = "LAKE_TRANSITIVE_TRACE_VERIFIED_WARM_REUSE"
        $Evidence.executed_module_builds = 0
        $Evidence.current_build_module = "NSEMaxwell"
        Copy-Item (Join-Path $ReportRoot "run-build-freshness.log") (Join-Path $ReportRoot "run-build.log") -Force
    }
    elseif ($FreshnessExit -eq 3) {
        $Evidence.build_strategy = "SERIAL_INCREMENTAL_REBUILD"
        $Evidence.executed_module_builds = 0
        $FailedModules = [Collections.Generic.List[string]]::new()
        $SkippedModules = [Collections.Generic.List[string]]::new()
        $Evidence.failed_modules = @()
        $Evidence.skipped_modules = @()
        Write-JsonFile $ProvenancePath $Evidence
        foreach ($Module in $BuildModules) {
            $Evidence.current_build_module = $Module
            $ModuleLog = "run-build-" + $Module.Replace(".", "-") + ".log"
            $SourcePath = Get-ProjectSourcePath $Module
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
            $Evidence.executed_module_builds += 1
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
        $null = Invoke-NativeLogged "lake" (@("build") + $AggregateTargets) "run-build.log"
    }
    else {
        throw "Lake freshness validation failed with exit code $FreshnessExit."
    }
    $Evidence.build_status = "PASS"

    $Evidence.stage = "AXIOM_AUDIT"
    Write-JsonFile $ProvenancePath $Evidence
    $null = Invoke-NativeLogged "lake" @(
        "env", "lean", "-R", $AdapterSourceRoot, $AuditSource
    ) "run-audit.log"
    $Evidence.audit_command_status = "PASS"

    $Evidence.stage = "VERIFY_EVIDENCE"
    Write-JsonFile $ProvenancePath $Evidence
    $VerifierArguments = $PythonPrefix + @(
        $VerifierSource,
        "--expected-platform", $NativePlatform,
        "--root", $RepoRoot,
        "--targets", "Auxillary/audit-targets.txt",
        "--audit-source", $AuditSource,
        "--log", (Join-Path $ReportRoot "run-audit.log"),
        "--manifest", $ManifestPath,
        "--provenance", $ProvenancePath,
        "--scope", "Auxillary/formalization-status.json",
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
    $Evidence.failure_error_id = $_.FullyQualifiedErrorId
    $Evidence.failure_stack_trace = $_.ScriptStackTrace
    $Evidence.failure_position = if ($_.InvocationInfo) {
        $_.InvocationInfo.PositionMessage
    } else { $null }
    $Evidence.completed_at_utc = [DateTime]::UtcNow.ToString("o")
    Write-JsonFile $ProvenancePath $Evidence
    Write-Host ("EXTERNAL_RUN=FAIL: " + $_.Exception.Message)
    exit 1
}
