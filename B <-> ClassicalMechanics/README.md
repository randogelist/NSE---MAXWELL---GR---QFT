# Exact directional proof spine

```text
actual stress definition
→ scalar entry derivative
→ full tensor-divergence identity
→ incompressible stress identity
→ NSE ⇒ Newtonian balance
→ Newtonian balance ⇒ NSE
→ global and finite solution/existence equivalences
→ existing Maxwell implications under FourierHodgeLaws
```

The files in `=>/` and `<=/` contain the actual directional construction bodies. `ClassicalMechanics.Equivalence` imports those bodies and composes them deterministically.

```text
NATIVE_FIRST_ROOT = local Cauchy balance ↔ NSE
PRESSURE_GLOBAL = arbitrary periodic gauge
PRESSURE_FINITE = mean zero on each time slice
VELOCITY_MEAN = arbitrary
MATERIAL_FLOW_ROOT = pending actual analytic adapters
LAGRANGE_DALEMBERT_ROOT = pending actual variation and pressure reconstruction adapters
GLOBAL_NONEMPTINESS = not asserted
```

The full mathematical chain is preserved in `../Auxillary/derivations/NSE_CLASSICAL_MECHANICS_EQUIVALENCE_B_TIER.txt`; its reference lines and native-port boundary are indexed by `../Auxillary/classical-mechanics-proof-spine.json`.
