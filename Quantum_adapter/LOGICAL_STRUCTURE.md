# Quantum adapter: logical structure

```text
DERIVATION = NSE_3D_CANONICAL_QUANTUM_BRIDGE_B_TIER.txt@1.8.0
ROOT = R1--R24
CHECKPOINTS = CP00--CP74
PROSPECTIVE_DECLARATIONS = 361
DERIVATION_STATUS = B_TIER
LEAN_CHECKPOINT_PROMOTION = NONE
LOCAL_LEAN_EXECUTIONS = 0
```

\[
\operatorname{FeffermanB}(\nu)
\iff G_3(\nu)
\iff\operatorname{QREG}(\nu,\hbar)
\iff\operatorname{QLIP}(\nu,\hbar).
\]

```text
CLASSICAL_ENDPOINT = NSEMaxwell.Classical.FeffermanB
SPACE = R^3 / Z^3
FORCING = 0
MEAN = ARBITRARY
INITIAL_REGULARITY = joint C-infinity through t=0
PRESSURE = periodic; arbitrary gauge
```

The TXT pressure gauge fixes spatial mean zero. The existing exact native
`FeffermanB` permits arbitrary pressure gauges. Any identification with the
gauge-fixed TXT endpoint requires the pressure-normalization adapter; neither
the velocity mean nor the regularity class may be replaced.

## Native sequence

| Order | Native target | Exact analytic frontier |
|---:|---|---|
| 0 | Full finite Fourier phase; reality and solenoidality; constant modes | Actual real Hilbert phase, Fourier/physical energy agreement |
| 1 | Canonical cotangent function and transport differential expression | Actual tangent drift equality (native Tangency.lean bodies externally compiled and standard-only audited at 216217a88fc8039b5551738a0ce3b6bbe884e45d), complete flow, divergence trace |
| 2 | Complex states; Born density; actual energy expectation | Normalization, moment integrability, actual operator domains |
| 3 | Galerkin scalar bound ⇒ packet expectation bound | Quantitative forward packet estimate |
| 4 | Packet expectation bound ⇒ Galerkin scalar bound | Quantitative converse estimate/reference selection |
| 5 | `FeffermanB` ⇒ Galerkin bound | Actual smooth-solution stability, uniform in cutoff |
| 6 | Galerkin bound ⇒ `FeffermanB` | Actual compactness, pressure reconstruction, all-time gluing |
| 7 | Deterministic conjunction/equivalence assembly | Every previous body; unchanged explicit premises |

```text
PARTIAL_NATIVE_ADAPTER != FULL_CP_DISCHARGE
ACTUAL_DIFFERENTIAL_EXPRESSION != SELFADJOINT_L2_OPERATOR
FLOW_CONTRACT != PROVED_FLOW_INHABITANT
SPECTRAL_SOURCE_COPY != ACTUAL_REAL_PHASE_IDENTIFICATION
BOOL_CERTIFICATE_ACCEPTANCE != ACTUAL_INPUT_ENCLOSURE
```

## Root/checkpoint relation

| Root | Checkpoint families | Mathematical content |
|---|---|---|
| R1–R4 | CP00–CP29, CP32 | Finite model, actual generator, deterministic reconstruction, base equivalence |
| R5 | CP33–CP35 | Prescribed compact packets, reference stability, conditional continuum error |
| R6–R7 | CP37–CP40 | Finite moments, Gaussian states, canonical moments, actual domains |
| R8 | CP41–CP45 | Weighted resolvents, Cayley steps, observable criteria |
| R9–R12 | CP46–CP52 | Finite Gaussian graph data, partitions, residuals, normalized core witnesses |
| R13–R16 | CP53–CP59 | Hermite graph density, rational trials, finite checker, admitted families |
| R17–R20 | CP60–CP66 | Certified real names, explicit Fourier frame, validated residual construction |
| R21–R22 | CP67–CP70 | Spatial gradient grids, elementary names, nonpolynomial Gaussian quadrature |
| R23–R24 | CP71–CP74 | Actual temporal moduli, extrema/integrals, strict-threshold witnesses |
| Supporting | CP15, CP36 | Energy/shear/noncoercivity and momentum diagnostics |
| Optional | CP30 | AX6-dependent comparison; no root dependency |
| Evidence | CP31 | Matching external compiler and theorem-level axiom audit |

The exact dependency sets, input/output contracts, named subgoals, source
declaration references, and prospective names are in
[`checkpoint-manifest.json`](checkpoint-manifest.json). No checkpoint is promoted
by importing its source, recording its signature, or proving a smaller theorem.

## Source identities

| Scope | Lean | Mathlib | Methlib |
|---|---|---|---|
| TXT source register | 4.33.0 | `db584cd6d46c92f209a44c0f1c829460d327499d` | `09dfe94a1ef150e21d09df3013fbe09002ef139c` |
| Native repository | 4.34.0-rc1 | `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` | contained pinned source closure |

```text
PIN_TRANSITION = EXACT_DECLARATION_REVALIDATION_REQUIRED
EXTERNAL_COMPILER = native Linux / cached
APPROVED_AXIOMS = propext, Classical.choice, Quot.sound
PROMOTION = matching source hashes + successful kernel + exact theorem axiom audit
```

## Unresolved universal bound

\[
\forall a\in C^\infty_\sigma(\mathbb T^3),\ \forall T<\infty,
\quad\sup_{N\ge1}\sup_{0\le t\le T}\|u_N^a(t)\|_{H^3}<\infty.
\]

```text
UNIVERSAL_NSE_REGULARITY = UNRESOLVED
SINGLE_CONTINUUM_QUANTUM_HAMILTONIAN = NOT_CONSTRUCTED
PER_CUTOFF_EFFECTIVE_ACCESS != UNIFORM_CUTOFF_BOUND
```

`QuantumAdapter.QREG` denotes the canonical Gaussian criterion `QREG_Gauss` in R7. The full B-tier source is contained at `B <-> Quantum/NSE_3D_CANONICAL_QUANTUM_BRIDGE_B_TIER.txt`; its exact SHA256 is retained in checkpoint-manifest.json.
