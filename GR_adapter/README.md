# NSE ↔ normalized marked GR sector

```text
BASE_BRANCH = codex/fefferman-b-maxwell
BASE_COMMIT = 1de664f2ef5ddc11caef25ac2274278b4171ab6b
BRANCH = codex/gr-adapter
MODE = A_TIER_DERIVATION
STATUS = CONDITIONAL_FORMAL_CLOSURE
NATIVE_DECLARATIONS = A_TIER
LOCAL_LEAN_EXECUTIONS = 0
```

For `ν>0`, `ρ≠0`, `t0 : ℝ`, the exact target is

```lean
NSEGR.ExactSectorEquivalence ν ρ t0
-- Nonempty (NSEGR.NSEgerm ν t0 ≃ NSEGR.GRgerm ν ρ t0)
```

The source carrier consists of actual local jointly analytic periodic NSE representatives modulo full-spatial-slice time-germ equality and time-only pressure gauge. The target carrier consists of actual analytic five-dimensional Lorentzian vacuum metrics in the fixed Gaussian marking, with flat timelike induced metric, fixed boundary normalization, and the independently computed STF constitutive tensor equal to zero. Neither carrier is defined as the image of a lift.

This statement is local in time and radius. The inherited `FeffermanB` is a global smooth arbitrary-data existence proposition. No equivalence between those distinct scopes is asserted.

| Stage | Source | Exact content |
|---|---|---|
| 1 | `GRAdapter/Geometry.lean` | Actual derivatives, inverse metric, Christoffel, Ricci, Einstein tensor; native analytic Lorentzian flat vacuum |
| 1 | `GRAdapter/Algebra.lean` | STF projection, signed trace reversal, Hamiltonian identity, normalized initial `K00`, viscosity difference |
| 1 | `GRAdapter/Fields.lean` | Ordinary-time local analytic NSE, concrete Poisson/Leray series, actual constant solutions |
| 1 | `GRAdapter/Boundary.lean` | Actual `K`, beta, velocity, pressure, STF stress, Codazzi and Hamiltonian expressions |
| 1 | `GRAdapter/Sector.lean` | Independent constrained-boundary, normalized vacuum and canonical metric predicates |
| 1 | `GRAdapter/NativeBoundary.lean` | Actual constant constrained boundary for every rho; no bulk realization asserted |
| 1 | `GRAdapter/Germs.lean` | Independent pressure-gauge and marked metric germ quotients |
| 1 | `GRAdapter/CompletionSource.lean` | Actual source, scalar correction, lowering and completed boundary tensor |
| 1 | `GRAdapter/Locality.lean` | Actual metric-jet and decoded-field germ locality; analytic pressure gauge; second time derivative locality |
| 1 | `GRAdapter/Contracts.lean` | Explicit scalar/radial/reconstruction obligations and exact zero-stress deduction |
| 2 | `NSEGRForward.lean` | Scalar completion → constrained boundary → actual radial vacuum → canonical sector; velocity recovery |
| 3 | `NSEGRReverse.lean` | Actual metric → reconstructed analytic NSE; separate germ descent/inverse assembly |

The conditional root is `NSEGR.NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_NAMED_CONTRACTS`.

| Unresolved premise | Exact remaining content |
|---|---|
| `ScalarBoundaryCompletionLaws` | Actual analytic normalized scalar completion, constraints and boundary recovery for every supplied analytic NSE representative |
| `AnalyticRadialExtensionLaws` | Actual analytic radial extension and vacuum constraint propagation, with allowed time-collar shrink |
| `GeometricReconstructionLaws` | Analytic Poisson/Leray mapping, geometric constraints and exact reconstructed residual identity |
| `GermInverseLaws` | Forward gauge descent and the lift-after-decode identity for the chosen completions |

All four premises remain visible. No inhabitants are supplied. Native tensor proofs and flat-vacuum semantics do not discharge them. The flat metric is explicitly proved to fail the nonzero-rho normalization.

The full [B-tier derivation](Derivation/NSE_GR_EXACT_SECTOR_EQUIVALENCE_B_TIER.txt), version 1.6.0, contains 153 proof contracts and 62 Mathlib / 24 Methlib source indices. Its older 4.33.0 source pins are retained as provenance. The active package inherits Lean 4.34.0-rc1 and the newer pinned Mathlib source; this package's exact declarations require their own external audits. No old source index is presented as a new compiler certificate.

External cached execution:

```bash
bash GR_adapter/run.sh
```

`run.cmd` is the native Windows entry point for the Windows-safe standalone export containing the sibling `GR_adapter/` and `Auxillary/GR/` directories. The full inherited repository contains POSIX-only names and is not a native Windows checkout target.

Source inventory, explicit hypotheses and matching evidence are recorded in [GR_ADAPTER_A_TIER.txt](GR_ADAPTER_A_TIER.txt), [audit targets](../Auxillary/GR/audit-targets.json), and [scope status](../Auxillary/GR/formalization-status.json). Existing compiler/dependency/project caches are retained. Each stage must pass compilation and a fresh named axiom audit before the next stage runs.

Detailed source-to-obligation map: [ENDPOINT_PLAN.md](ENDPOINT_PLAN.md).

## External certificate

Cached native Lean 4.34.0-rc1 [run 43365946484](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43365946484) passed at `3dc98a61115f8d2e79d115d70b8c3478c504d82e`: adapter 190/190, forward 6/6, reverse 6/6 named standard-only audits. All input hashes were verified. The [immutable original artifact](../Auxillary/GR/evidence/3dc98a61115f8d2e79d115d70b8c3478c504d82e/external-artifact.zip) and its original logs, types and manifests are retained. The [source-equivalence record](../Auxillary/GR/source-equivalence.json) identifies the subsequent status-only changes to audited inputs.

[Windows-safe standalone package](../Auxillary/GR/exports/GR_adapter_4.34.0-rc1.zip): extract both sibling folders and run `GR_adapter/run.cmd`. The package contains all project Lean files, pinned dependency configuration, the B-tier derivation and retained evidence. Dependency objects are restored by the cache runner; external compiler/dependency installation is required.

The root is **CONDITIONAL_FORMAL_CLOSURE**. Scalar completion, radial extension, reconstruction, and the two remaining forward germ laws have no supplied inhabitants. `UNCONDITIONAL_CLOSURE` remains open.
