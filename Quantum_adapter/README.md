# Quantum adapter

BASE = `codex/fefferman-b-maxwell` @ `1de664f2ef5ddc11caef25ac2274278b4171ab6b`.

STATUS = A_TIER: 204 adapter declarations + 203 native assembly declarations.
ROOT = CONDITIONAL_FORMAL_CLOSURE; UNCONDITIONAL_CLOSURE = NOT_ESTABLISHED.

Native assembly proof commit: `1a0664fc219e6b4e2caf005384bd71b585ad0847`.
Cached external Linux Lean 4.34.0-rc1 and fresh standard-axiom audit: PASS.

[Current exact root / premises / theorem index](../Auxillary/quantum/assembly/exports/exact_quantum_root_for_canonical_flow_A_TIER.txt)
· [Native source](QuantumAdapter/Assembly.lean)
· [Exact assembly evidence](../Auxillary/quantum/assembly/evidence/1a0664fc219e6b4e2caf005384bd71b585ad0847/).

Native scope: intrinsic real Hilbert full Fourier phase; actual conjugate reality
and solenoidality; zero mode and arbitrary velocity mean retained; torus Fourier
initial coefficients; canonical finite-width Gaussian QREG.

Constructed: unique complete native orbits for nonnegative viscosity; smooth
time dependence; bounded-ball Lipschitz time maps and joint continuity; initial
Sobolev projection bounds; gradient embedding; Gaussian normalization/moments;
transport and full multiplier/expectation domains from the explicit Jacobian
hypotheses; forward/reverse packet estimates from the remaining energy inequalities.

Root: `QuantumAdapter.Assembly.exact_quantum_root_for_canonical_flow`.
Explicit frontier: divergence; initial-data differentiability; Jacobian;
relative L2 estimate; one positive uniform tame H3 constant; Galerkin stability;
Galerkin compactness. No unconditional Navier–Stokes regularity or selfadjoint
generator is asserted.

[Logical structure](LOGICAL_STRUCTURE.md), [75-checkpoint manifest](checkpoint-manifest.json),
[historical endpoint index](ENDPOINT_INDEX.md), and [historical 204-target scope](QUANTUM_ADAPTER_A_TIER.txt)
retain the earlier checkpoint. The current assembly report supplies the reduced
premise inventory and the exact pinned Mathlib/Methlib entrypoints.

[External replay](../Auxillary/quantum/assembly/README.md).
Local Lean executions = 0. Proof bodies remain byte-identical to the audited commit.
