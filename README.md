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
SOURCE_STATUS = A_TIER_CANDIDATE
EXACT_UNCONDITIONAL_TARGET = UNPROVED
ANALYTIC_REALIZATION = OPEN
LOCAL_LEAN_EXECUTIONS = 0
```

The prepared concrete root has type:

```lean
NSEMaxwell.Bridge.PeriodicAnalyticLaws → NSEMaxwell.Classical.ExactEquivalence
```

`PeriodicAnalyticLaws` contains fifteen explicit local analytic obligations. It contains neither an existence assertion nor a map between global solution-existence propositions. Its fields include periodic Hodge reconstruction, smooth Fourier realization, derivative commutation, conservation of mean, and the constitutive chain rule. No inhabitant of this structure is supplied.

The conditional proof constructs both solutions on the actual fields, with the initial-data maps `a ↦ (mean a, curl a)` and `(m, B₀) ↦ m + K B₀`, and reconstructs the explicit periodic pressure. The unconditional `ExactEquivalence` remains open.

## External compilation

```cmd
run.cmd
```

Compiler: native Windows Lean `4.34.0-rc1`.

Mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

The runner retains dependency/build caches, obtains the official Mathlib cache, compiles the project, prints the complete signatures and axioms of the enumerated audit targets, and records source SHA-256 values. The workflow runs the same entry point on `windows-latest`.

Approved foundational axioms: `propext`, `Classical.choice`, `Quot.sound`. A matching audit excludes `sorryAx` and unapproved axioms for each audited theorem. It does not discharge theorem hypotheses.

## Source map

| File | Scope |
|---|---|
| `NSEMaxwell/Classical.lean` | Concrete PDE definitions and exact target proposition |
| `NSEMaxwell/Kinematics.lean` | Concrete slice, derivative-congruence, and zero-input lemmas |
| `NSEMaxwell/Constitutive.lean` | Concrete constitutive algebra and explicit residual identities |
| `NSEMaxwell/Negation.lean` | Actual negation identities without regularity premises |
| `NSEMaxwell/Lamb.lean` | Actual Lamb identity from first derivatives |
| `NSEMaxwell/Pressure.lean` | Actual canonical pressure-gradient identity |
| `NSEMaxwell/Residual.lean` | Abstract additive residual proof spine |
| `NSEMaxwell/ExistenceTransport.lean` | Logical transport across explicit data and solution maps |
| `NSEMaxwell/AnalyticBridge.lean` | Explicit analytic premises and concrete forward/reverse solution constructions |
| `NSEMaxwell/FEFFERMAN_B_MAXWELL_EQUIVALENCE.lean` | Conditional root theorem with the exact concrete conclusion |
| `FEFFERMAN_B_MAXWELL_EQUIVALENCE_A_TIER.txt` | Scope, premise register, proof spine, and evidence contract |
| `NSEMaxwell/Audit.lean` | Enumerated theorem signatures and axiom audit |
| `formalization-status.json` | Exact semantic status and unresolved obligations |
| `docs/FEFFERMAN_B_MAXWELL_EQUIVALENCE_B_TIER.txt` | Mathematical derivation |

## Mathematical reference

[Charles L. Fefferman, Existence and Smoothness of the Navier–Stokes Equation](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf), periodic assertion B and the periodic-pressure erratum.
