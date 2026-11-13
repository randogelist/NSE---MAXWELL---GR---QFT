# Fefferman B adapter

## Exact Lean statement

Location: [NSEMaxwell/Classical.lean](NSEMaxwell/Classical.lean).

```lean
NSEMaxwell.Classical.FeffermanB (ν : ℝ) : Prop :=
  ∀ a : Field, Data a →
    ∃ (u : Velocity) (p : Pressure), NSSolution ν a u p
```

`Data`, `NSSolution`, actual derivatives, periodicity, cube means, joint smoothness, and the unrestricted velocity mean retain their frozen definitions. A compiled proposition definition is distinct from a proof of that proposition.

## Contents

| Path | Content |
|---|---|
| [NSEMaxwell/Classical.lean](NSEMaxwell/Classical.lean) | Exact Fefferman-B statement and concrete PDE definitions |
| [NSEMaxwell/AnalyticContracts.lean](NSEMaxwell/AnalyticContracts.lean) | Shared magnetic-path objects and explicit analytic contracts |
| [NSEMaxwell/AnalyticReduction.lean](NSEMaxwell/AnalyticReduction.lean) | Four-field FourierHodgeLaws contract and reduction |
| [NSEMaxwell/AnalyticBridge.lean](NSEMaxwell/AnalyticBridge.lean) | Compatibility assembly of the two directions |
| [NSEMaxwell/](NSEMaxwell/) | Shared derivative, periodic integration, mean, vorticity, and constitutive calculus |
| [Endpoints/](Endpoints/) | Selected Mathlib/Methlib source copies and index |
| [NSEMaxwell/Audit.lean](NSEMaxwell/Audit.lean) | Exact signature and theorem-level axiom audit commands |
| [scripts/](scripts/) | External runner and evidence verifier |
| [evidence/](evidence/) | Retained external compiler evidence |

The module root remains `NSEMaxwell`; Lake maps it to this physical directory.

## Copied endpoint boundary

```text
PUBLIC_SOURCE_COPIES   = PRESENT
TARGET_NATIVE_PORTS   = DEFERRED
HODGE_LEAN_INHABITANT  = NOT_SUPPLIED
```

Fourteen original source files are copied under `Endpoints/sources/`, with `.lean.txt` suffixes and unchanged bytes: six Mathlib files and eight Methlib files. Complete imports are recorded; the snapshots do not constitute a standalone dependency-closed package.

Mathematical composition: [FOURIER_HODGE_COMPOSITION_B_TIER.txt](../B%20%3C-%3E%20Maxwell/FOURIER_HODGE_COMPOSITION_B_TIER.txt).

Deferred Lean contracts: [INTEGRATION_PLAN.md](../B%20%3C-%3E%20Maxwell/INTEGRATION_PLAN.md).

## Directional consumers

- [Fefferman B ⇒ Maxwell](../B%20%3C-%3E%20Maxwell/%3D%3E/).
- [Maxwell ⇒ Fefferman B](../B%20%3C-%3E%20Maxwell/%3C%3D/).

The directional base modules import `NSEMaxwell.AnalyticContracts`. Their separate reduced modules import `NSEMaxwell.AnalyticReduction`. The resulting module graph is acyclic.

## Matching external certificate

[Native Linux run 43345557147](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147): build PASS; 174/174 named audits PASS_STANDARD_ONLY; 30/30 Lean input hashes match the delivered source. [Audit summary](evidence/linux-43345557147/audit-summary.json). The conditional directions are A-tier; the Hodge inhabitant remains deferred.
