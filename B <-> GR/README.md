# B <-> GR

```text
REQUESTED_GLOBAL_TARGET = forall nu > 0, forall rho != 0, FeffermanB nu iff GRB nu rho
GLOBAL_TARGET_STATUS = OPEN
AVAILABLE_NATIVE_SUBCHAIN = local analytic NSE germs <-> normalized marked 5D Gaussian vacuum germs
AVAILABLE_NATIVE_SUBCHAIN_STATUS = !!!! UNCONDITIONAL_CLOSURE
```

## Ordered implication sources

| Location | Exact available content |
|---|---|
| [=>/NSEGRForward.lean](%3D%3E/NSEGRForward.lean) | Scalar boundary completion, actual Gaussian vacuum extension, velocity recovery, and pressure-gauge recovery |
| [<=/NSEGRReverse.lean](%3C%3D/NSEGRReverse.lean) | Geometric reconstruction, quotient maps, both inverse identities, and the actual `Equiv` constructor |
| [NSE_GR_EXACT_SECTOR_EQUIVALENCE_B_TIER.txt](NSE_GR_EXACT_SECTOR_EQUIVALENCE_B_TIER.txt) | Complete mathematical derivation of the exact local sector theorem |
| [NSE_B_GR_GLOBAL_BRIDGE_FRONTIER.txt](NSE_B_GR_GLOBAL_BRIDGE_FRONTIER.txt) | Literal global target, candidate geometric endpoint, and remaining global bridge obligations |

## Certified local subchain

```text
native CK + native Gaussian vacuum extension + native Fourier input
  -> native scalar completion / radial extension / reconstruction / inverse laws
  -> forwardGerm and reverseGerm
  -> reverseGerm (forwardGerm n) = n
  -> forwardGerm (reverseGerm g) = g
  -> Nonempty (NSEgerm nu t0 ≃ GRgerm nu rho t0)
```

Exact unconditional root:

```lean
NSEGR.NativeLiterature.NSE_GR_NATIVE_LITERATURE_CLOSURE :
  ∀ (ν ρ t0 : ℝ),
    0 < ν → ρ ≠ 0 → NSEGR.ExactSectorEquivalence ν ρ t0
```

[Native root](../ASSEMBLY/GRAssembly/NSE_GR_NATIVE_LITERATURE_CLOSURE.lean) ·
[Native composition](../ASSEMBLY/GRAssembly/RootClosure.lean) ·
[A-tier report](../Auxillary/GR/Closure/Native/NSE_GR_NATIVE_LITERATURE_CLOSURE_A_TIER.txt) ·
[Exact certificate](../Auxillary/GR/Closure/Native/EXTERNAL_CERTIFICATE.json).

```text
CERTIFIED_PROOF_SOURCE = d5231111cbdbe8a9c686b52ae4224554d4fba48a
EXTERNAL_RUN = 43509144981
NAMED_AUDITS = 1549/1549 PASS_STANDARD_ONLY
FOUNDATIONAL_AXIOMS = {propext, Classical.choice, Quot.sound}
```

## Literal Fefferman-B endpoint

`FeffermanB` retains its existing definition in
[NSEMaxwell/Classical.lean](../Fefferman_adapter/NSEMaxwell/Classical.lean):
arbitrary smooth periodic divergence-free initial data, arbitrary velocity mean,
and a global solution jointly smooth through `t = 0`.

The supplied GR directional files concern local analytic representatives and
germs. Their theorem types contain no `FeffermanB` argument or conclusion.
The global target therefore remains open. Required additional constructions:

1. Positive-time joint analytic realization of a global smooth NSE solution,
   with an analytic pressure representative after pressure-gauge normalization.
2. Positive-time GR collar construction with compatible decoded boundary fields.
3. Global boundary reconstruction with the exact smooth initial trace and the
   NSE identity extended to `t = 0`.

No single global Einstein metric or metric transition maps are asserted by a
family of boundary-compatible collars. The candidate global endpoint and its
stronger single-metric alternative are distinguished in the frontier record.

## Source identity and cached validation

The two directional files and the local derivation are byte-identical mirrors
of the certified sources. Canonical compilation paths remain in `GR_adapter/`;
the native closure remains in `ASSEMBLY/GRAssembly/`. This layout introduces no
new Lean declarations and preserves the Windows-safe GR export paths.

[Source map](../Auxillary/GR/Directions/source-map.json) ·
[Source-identity verifier](../Auxillary/GR/Directions/verify_source_identity.py).

```bash
python3 Auxillary/GR/Directions/verify_source_identity.py
```

The source-identity check compares every mirror with its canonical source and
checks all 373 inputs of the retained native certificate. It invokes no Lean,
Lake, or elan process. Existing external cached GR compilation and exact audits
remain available through `ASSEMBLY/run.sh` and the GR assembly workflow.
