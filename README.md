# Periodic NSE–Maxwell equivalence

## Exact target

```lean
NSEMaxwell.Classical.ExactEquivalence
-- ∀ ν : ℝ, 0 < ν → ∀ c : ℝ, 0 < c →
--   (FeffermanB ν ↔ MaxwellB ν c)
```

Scope: the unforced three-dimensional periodic Fefferman B problem, arbitrary velocity mean, periodic pressure, and joint smoothness through `t = 0`.

The Maxwell problem includes the exact constitutive constraints

```text
u = m + K B
E = G[B] = B × u + ν curl B
ρ = div G[B]
J = c² curl B − DG[B](−curl G[B])
```

`K = curl (-Δ)⁻¹₀` is defined by an explicit real Fourier series. The derivative, integral, and Fourier definitions are concrete Mathlib expressions.

## Status

```text
ORIGINAL_NINE_ENDPOINT_ROOT = A_TIER
REDUCED_FOUR_ENDPOINT_ROOT = A_TIER
CURRENT_FORMAL_STATUS = CONDITIONAL_FORMAL_CLOSURE
ACTIVE_CI_PLATFORM = NATIVE_LINUX_UBUNTU_24_04
ACTIVE_LINUX_VALIDATION = PASS_BUILD_AND170_FRESH_AUDITS
EXACT_UNCONDITIONAL_TARGET = UNPROVED
ANALYTIC_REALIZATION = OPEN
LOCAL_LEAN_EXECUTIONS = 0
```

The original externally compiled and audited concrete root has type:

```lean
NSEMaxwell.Bridge.PeriodicAnalyticLaws → NSEMaxwell.Classical.ExactEquivalence
```

The new reduced entry point has type:

```lean
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED :
  NSEMaxwell.Bridge.FourierHodgeLaws → NSEMaxwell.Classical.ExactEquivalence
```

`FourierHodgeLaws` retains four named endpoints: velocity reconstruction, curl reconstruction, canonical velocity/pressure smoothness and incompressibility, and the electric Hodge identity. Its smoothness endpoint has three explicit components. No inhabitant is supplied.

Vorticity regularity, mean conservation, the vorticity residual, temporal reconstruction, and the electric chain rule are now derived. Temporal reconstruction and the chain rule still depend on the remaining Hodge and smoothness premises. The five canonical periodicity fields and electric/charge/current smoothness are also derived.

The historical `PeriodicAnalyticLaws` structure contains nine explicit local analytic obligations. It contains neither an existence assertion nor a map between global solution-existence propositions. Its fields include periodic Hodge reconstruction, smooth Fourier realization, derivative commutation, conservation of mean, and the constitutive chain rule. No inhabitant of this structure is supplied.

Initial-data admissibility and the reconstructed mean are derived from the retained endpoints. The root uses on-solution cancellation and requires no separate K- or DG-additivity premise. The optional off-solution factorization keeps its own explicit additivity hypothesis.

The conditional proof constructs both solutions on the actual fields, with the initial-data maps `a ↦ (mean a, curl a)` and `(m, B₀) ↦ m + K B₀`, and reconstructs the explicit periodic pressure. The unconditional `ExactEquivalence` remains open.

## Verified external Linux evidence

[Native Linux run 43336709607](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43336709607): complete build and **170/170** fresh theorem-level audits passed. Source: `d241f2b700be66ab447cb1650770271e1b364b8a`. All **25/25** Lean input hashes match the delivered proof files. Original artifact bytes: `evidence/linux-43336709607/` (60 files).

The compiler is native Linux Lean `4.34.0-rc1`, target `x86_64-unknown-linux-gnu`, compiler commit `3447a668783dbce1a8fdb97101dd067687b2b418`. Both root declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or additional axiom identity occurs. The four remaining analytic endpoints are explicit theorem hypotheses; no inhabitant is supplied. The audit also covers the four registered target-pin Mathlib endpoints.

The independently successful 170-target Windows certificate remains under `evidence/windows-43333835295/`; the older 74-target certificate remains under `evidence/windows-43318057281/`. Each describes its own source snapshot.

## Linux restart

Active CI: external native Linux, Ubuntu 24.04. The preceding Windows run had already completed successfully before cancellation was requested. No active Windows run remained to cancel. The Linux workflow replaces the automatic Windows workflow; `run.cmd` remains available for external Windows use.

The first Linux initialization preserved its compiler and dependency caches, then stopped before proof compilation on Unix dotfile metadata. `Get-Item -Force` corrected that platform issue. The cached Linux restart passed the complete project build and fresh audit. No Lean proof source or theorem premise changed during the migration.

## External compilation

Required: external Linux or Windows; Git; an elan-managed `lake`; Python 3.9 or later. Linux uses PowerShell Core (`pwsh`). The selected toolchain is pinned by the runner.

```bash
bash run.sh
```

Retained Windows entry point:

```cmd
run.cmd
```

Compiler: native Lean `4.34.0-rc1`; active CI: Ubuntu 24.04.

Mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

The runner retains compiler, dependency, and project caches. Dependency keys contain the exact compiler/configuration/lockfile/cache-scope hashes; project keys additionally contain the Lean source hashes. `.lake/packages`, `.lake/config`, and compressed Mathlib archives share the stable dependency cache. `.lake/build` has its own incremental project cache. The Windows migration preserved its earlier combined cache. Linux keys include their own OS and architecture; no Windows cache is restored in Linux CI.

Nine dependency revisions are locked and checked. The workflow verifies and preserves dependencies before proof compilation, then reuses Lake's dependency traces for individual module builds. Project modules remain sequential to bound memory use; native theorem elaboration remains enabled. Partial successful objects survive unrelated failures. The complete library build and fresh exact-signature/axiom audit remain mandatory.

```bash
bash run.sh -Phase Dependencies
bash run.sh -Phase BuildAudit
```

The default `run.sh` and `run.cmd` perform both phases. The dependency preparation fingerprint authorizes dependency acquisition reuse only. It cannot promote a theorem or reuse an old theorem audit. Source hashes, the resolved lockfile, command timings, compiler logs, and fresh audit evidence are recorded. See [CI_CACHE_AUDIT.txt](CI_CACHE_AUDIT.txt).

`lake build --no-build NSEMaxwell` validates ordinary transitive build traces in one Lake process. Exit `0` reuses the current library objects and proceeds to the fresh audit. Exit `3` invokes the sequential incremental rebuild. Other failures reject the run. No `--old` option or cached theorem-audit seal is used.

## Registered reference endpoints

[ENDPOINT_REGISTRY.json](ENDPOINT_REGISTRY.json) records eleven exact signatures with pinned source commits, blob hashes, compiler compatibility, and remaining definition-alignment obligations. Four declarations already exist in the exact target Mathlib and passed the fresh 170-target Linux audit. Seven independent harmonic-analysis declarations from Methlib are registered for source porting; Lean 4.33.0 evidence cannot certify them under the target Lean 4.34.0-rc1 compiler.

The Methlib candidates cover cube/torus coefficient transport, differentiation multipliers, polynomial decay, coefficient injectivity, smooth Fourier synthesis, coefficient recovery, and infinite-series pressure recovery. They do not supply an inhabitant of `FourierHodgeLaws` in this project. The original all-mean NSE proposition and the exact cosine-defined pressure remain fixed.

Approved foundational axioms: `propext`, `Classical.choice`, `Quot.sound`. A matching audit excludes `sorryAx` and unapproved axioms for each audited theorem. It does not discharge theorem hypotheses.

Native asynchronous elaboration is enabled by the normal Lean 4.34.0-rc1 CLI frontend. Typed signatures remain provisional until proof elaboration and kernel checking complete. See the [pinned Lean frontend](https://github.com/leanprover/lean4/blob/v4.34.0-rc1/src/Lean/Elab/Frontend.lean).

## Source map

| File | Scope |
|---|---|
| `NSEMaxwell/Classical.lean` | Concrete PDE definitions and exact target proposition |
| `NSEMaxwell/Kinematics.lean` | Concrete slice, derivative-congruence, and zero-input lemmas |
| `NSEMaxwell/Constitutive.lean` | Concrete constitutive algebra and explicit residual identities |
| `NSEMaxwell/Negation.lean` | Actual negation identities without regularity premises |
| `NSEMaxwell/Lamb.lean` | Actual Lamb identity from first derivatives |
| `NSEMaxwell/Pressure.lean` | Actual canonical pressure-gradient identity |
| `NSEMaxwell/CurlCurl.lean` | Actual second-derivative symmetry, curl-curl, and viscosity identities |
| `NSEMaxwell/ConstantPaths.lean` | Actual constant-trajectory regularity |
| `NSEMaxwell/Ampere.lean` | Ampere from Faraday and the constitutive chain rule |
| `NSEMaxwell/Residual.lean` | Abstract additive residual proof spine |
| `NSEMaxwell/ExistenceTransport.lean` | Logical transport across explicit data and solution maps |
| `NSEMaxwell/AnalyticBridge.lean` | Explicit analytic premises and concrete forward/reverse solution constructions |
| `NSEMaxwell/PeriodicIntegration.lean` | Cube integrability and zero integrals of periodic derivatives |
| `NSEMaxwell/Spacetime.lean` | Actual mixed derivative and closed-half-space calculus |
| `NSEMaxwell/FourierPeriodic.lean` | Concrete termwise Fourier-operator periodicity |
| `NSEMaxwell/DominatedWithin.lean` | Dominated differentiation within the time domain |
| `NSEMaxwell/LocalEvolution.lean` | Concrete vorticity residual and constitutive chain rule |
| `NSEMaxwell/TemporalMean.lean` | Time differentiation of the actual spatial mean |
| `NSEMaxwell/MeanConservation.lean` | NSE conservation of the unrestricted velocity mean |
| `NSEMaxwell/CanonicalSmoothness.lean` | Electric, charge, and current smoothness reduction |
| `NSEMaxwell/AnalyticReduction.lean` | Four-endpoint analytic premise and deterministic reduction |
| `NSEMaxwell/FEFFERMAN_B_MAXWELL_EQUIVALENCE.lean` | Conditional root theorem with the exact concrete conclusion |
| `FEFFERMAN_B_MAXWELL_EQUIVALENCE_A_TIER.txt` | Scope, premise register, proof spine, and evidence contract |
| `NSEMaxwell/Audit.lean` | Enumerated theorem signatures and axiom audit |
| `formalization-status.json` | Exact semantic status and unresolved obligations |
| `docs/FEFFERMAN_B_MAXWELL_EQUIVALENCE_B_TIER.txt` | Mathematical derivation |

## Mathematical reference

[Charles L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf), periodic assertion B and the periodic-pressure erratum.
