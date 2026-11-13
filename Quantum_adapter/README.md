# Quantum adapter

STATUS = A_TIER; ROOT = UNCONDITIONAL_CLOSURE_OF_EXACT_EQUIVALENCE.

```text
THEOREM = QuantumAdapter.Obligations.NSE_B_IFF_CANONICAL_QUANTUM
TYPE = forall nu > 0, FeffermanB nu iff QREG (closedPhaseFlow hnu)
P1..P7 = DISCHARGED
UNRESOLVED_ADAPTER_PREMISES = NONE
SOURCE_COMMIT = 3c2a8f5435b4e95e779222b37637f12a57d1eea9
MODULES = 77
THEOREMS = 581 / 581 PASS_STANDARD_ONLY
DECLARATIONS = 679 / 679 PASS_STANDARD_ONLY
COMPILER = Lean 4.34.0-rc1; Linux x86_64
AXIOMS = propext; Classical.choice; Quot.sound
LOCAL_LEAN_EXECUTIONS = 0
```

[Exact report](../Auxillary/quantum/obligations/NSE_QUANTUM_P1_P7_A_TIER.txt) · [Root source](QuantumAdapter/Obligations/Closure.lean) · [Retained compiler evidence](../Auxillary/quantum/obligations/evidence/3c2a8f5435b4e95e779222b37637f12a57d1eea9/) · [External CI](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43469332973).

Native scope: intrinsic real Hilbert full Fourier phase; actual conjugate reality and solenoidality; arbitrary velocity mean; torus Fourier initial coefficients; original finite-width canonical Gaussian QREG; periodic pressure and joint smoothness through t=0.

P1 supplies the exact drift trace. P2 and P3 supply initial-data differentiability and the Jacobian formula. P4 supplies relative L2 stability. P5 supplies a positive uniform H3 tame constant, instantiated by 512. P6 and P7 supply the native Galerkin stability and compactness implications. The existing Gaussian and packet estimates compose with these inhabitants into the root equivalence. The stronger quantitative constant 16 is not certified by this endpoint.

The conclusion is an equivalence; neither global regularity nor a selfadjoint quantum generator is a separate conclusion.

[Cached external replay](../Auxillary/quantum/obligations/README.md) · [Windows replay ZIP](../Auxillary/quantum/obligations/exports/NSE_QUANTUM_P1_P7_WINDOWS_REPLAY.zip). Windows runtime verification remains external and pending; the certificate above is Linux.

Historical checkpoints: [204-declaration adapter](QUANTUM_ADAPTER_A_TIER.txt), [203-declaration conditional assembly](../Auxillary/quantum/assembly/exports/exact_quantum_root_for_canonical_flow_A_TIER.txt), [logical structure](LOGICAL_STRUCTURE.md), [checkpoint manifest](checkpoint-manifest.json), and [endpoint index](ENDPOINT_INDEX.md). Their original evidence remains unchanged.
