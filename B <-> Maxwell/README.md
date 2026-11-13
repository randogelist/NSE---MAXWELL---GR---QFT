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
PROOF_SOURCE_CERTIFICATION   = PASS_BUILD_AND174_STANDARD_ONLY_AUDITS
AUXILLARY_LAYOUT_VALIDATION = PASS_CACHED_NATIVE_LINUX_BUILD_AND174_FRESH_AUDITS
LEAN_HODGE_INHABITANT        = NOT_SUPPLIED
UNCONDITIONAL_LEAN_CLOSURE   = NOT_ESTABLISHED
```

The Lean directions retain their explicit `PeriodicAnalyticLaws` or `FourierHodgeLaws` premise. The equivalence does not constitute a standalone proof of global NSE existence.

Matching certificate: [native Linux run 43345557147](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43345557147), proof-source commit `be8376a08573a7789e36b68c2bc48178aa6f53c3`. The exact conditional directional endpoints and conditional reduced root are A-tier. [Retained audit summary](../Auxillary/evidence/linux-43345557147/audit-summary.json).

Current auxiliary-layout certificate: [native Linux run 43348914489](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43348914489), source `b02425040a217a94855cfa52934e303f12fe80de`; 174/174 fresh audits, 30/30 matching Lean input hashes. [Current audit summary](../Auxillary/evidence/linux-43348914489/audit-summary.json).
