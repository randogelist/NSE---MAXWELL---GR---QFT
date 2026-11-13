# Fefferman B ↔ constrained Maxwell

```text
TARGET = forall nu > 0, forall c > 0, FeffermanB nu iff MaxwellB nu c
```

## Direction folders

| Folder | Implication | Active proof root |
|---|---|---|
| [=>/](%3D%3E/) | Fefferman B ⇒ Maxwell | [NSEMaxwellForward.lean](%3D%3E/NSEMaxwellForward.lean) |
| [<=/](%3C%3D/) | Maxwell ⇒ Fefferman B | [NSEMaxwellReverse.lean](%3C%3D/NSEMaxwellReverse.lean) |

These are the two direct child directories. The full derivation and integration contracts are files at this level.

## Shared adapter

[Fefferman_B_adapter/](../Fefferman_B_adapter/) supplies the exact Lean statement, shared calculus, explicit analytic premises, and copied public endpoints.

```text
AnalyticContracts
  -> NSEMaxwellForward / NSEMaxwellReverse
  -> AnalyticBridge
  -> AnalyticReduction
  -> reduced directional endpoints and exact conditional root.
```

The existing `NSEMaxwell.Bridge` declaration namespace is retained across the directional libraries.

## Derivations and formal boundary

| File | Scope |
|---|---|
| [FOURIER_HODGE_COMPOSITION_B_TIER.txt](FOURIER_HODGE_COMPOSITION_B_TIER.txt) | Complete B-tier derivation of the four Hodge fields and both implications |
| [FEFFERMAN_B_MAXWELL_EQUIVALENCE_B_TIER.txt](FEFFERMAN_B_MAXWELL_EQUIVALENCE_B_TIER.txt) | Earlier exact equivalence derivation |
| [FEFFERMAN_B_MAXWELL_EQUIVALENCE_A_TIER.txt](FEFFERMAN_B_MAXWELL_EQUIVALENCE_A_TIER.txt) | Exact conditional theorem, premise boundary, compiler evidence status |
| [INTEGRATION_PLAN.md](INTEGRATION_PLAN.md) | Deferred target-native Hodge adapter contracts |

```text
B_TIER_HODGE_COMPOSITION      = COMPLETE
LEAN_DIRECTION_SEPARATION    = IMPLEMENTED
CURRENT_LAYOUT_CERTIFICATION = PENDING_CACHED_NATIVE_LINUX
LEAN_HODGE_INHABITANT        = NOT_SUPPLIED
UNCONDITIONAL_LEAN_CLOSURE   = NOT_ESTABLISHED
```

The Lean directions retain their explicit `PeriodicAnalyticLaws` or `FourierHodgeLaws` premise. The equivalence does not constitute a standalone proof of global NSE existence.
