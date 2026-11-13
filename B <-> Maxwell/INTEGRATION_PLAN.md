# Deferred Lean integration contracts

```text
STATE              = SPECIFIED_MATHEMATICALLY
IMPLEMENTATION     = DEFERRED
COMPILER           = external native Linux / Lean 4.34.0-rc1
DEPENDENCIES       = existing pinned Mathlib with retained caches
SOURCE_LAYOUT      = Fefferman_B_adapter plus B <-> Maxwell/=> and /<=
```

The names below are prospective adapter names. They are not assertions that compiled declarations already exist. Their mathematical bodies are the indicated sections of [FOURIER_HODGE_COMPOSITION_B_TIER.txt](FOURIER_HODGE_COMPOSITION_B_TIER.txt).

## 1. Spatial contracts

| Proposed endpoint | Exact mathematical contract | Inputs | Derivation |
|---|---|---|---|
| `cube_fourierCoeff_eq_torus` | Actual coefficient integral over the frozen Euclidean closed cube equals the normalized torus coefficient | Continuous periodic input; coordinate-volume and null-face adapters | C01; M01/T01 |
| `fourierCoeff_coordinateDerivative` | `coeff (∂ⱼ f) k = (2πikⱼ) * coeff f k` | Smooth periodic input; actual `fderiv` | C02; T02 |
| `fourierCoeff_weighted_summable` | `∀ r : ℕ, ∑ₖ (1+|k|)^r |coeff f k| < ∞` | Smooth periodic input | C02–C03; T03/M05 |
| `fourier_reconstruction` | Pointwise reconstruction of the input from its coefficients | Previous summability and cube/torus transport | C04; M02; alternative M03/M04/M12/T06 |
| `scalarL_eq_real_multiplier` | Frozen `scalarL` equals the real complex-exponential synthesis with `λ(0)=0`, `λ(k)=(4π²|k|²)⁻¹` | Smooth periodic scalar input | C05 |
| `vectorL_eq_real_multiplier` | Componentwise counterpart for the actual vector Bochner integral | Smooth periodic vector input | C05 |
| `L_spatial_smooth` | Frozen scalar/vector `L` is smooth and periodic | Weighted coefficient summability | C06; M07/T04 |
| `L_coefficient` | `coeff (L f) k = λ(k) * coeff f k`; `mean (L f)=0` | Previous synthesis identity and summability | C06; T05; optional T08 |
| `L_poisson` | `-Δ(L f)=f-mean(f)` | Previous inversion and actual derivative calculation | C06 |
| `L_commutes_coordinateDerivative` | `∂ⱼ(L f)=L(∂ⱼ f)` | Previous smoothness and multiplier calculation | C06; optional T09 |
| `periodic_hodge_identity` | `K(curl F)=F-mean(F)+grad(L(div F))` | Smooth periodic F; actual curl-curl identity | C07 |

The scalar/vector adapters must preserve `EuclideanSpace ℝ (Fin 3)`, the actual cube and volume, the sign of the derivative symbol, and the all-frequency cosine normalization. The coordinate map to a default Pi normed space is used as a linear/measure identification, not as an isometry to the maximum norm.

Linearity of `L` and `K` is proved on the smooth periodic class through summability. No unrestricted linearity of totalized nonsummable `tsum` is introduced.

## 2. Parameter and boundary contracts

| Proposed endpoint | Exact mathematical contract | Inputs | Derivation |
|---|---|---|---|
| `fourierCoeff_time_derivative` | Actual within time derivative of the coefficient equals the coefficient of the actual within derivative | Joint `ContDiffOn ℝ ∞` on forward spacetime | C08; existing dominated-within integral theorem |
| `fourierCoeff_uniform_rapid` | For each finite T,r,N, a finite bound `supₜ |∂ₜʳ coeff F(t) k| ≤ M (1+4π²|k|²)⁻ᴺ` on `[0,T]` | Compactness of input jets; periodic spatial integration by parts | C08 |
| `parameter_fourier_jets` | All candidate mixed Fourier derivatives converge normally and form continuous multilinear jets on the forward half-space | Previous bounds; M05 | C09 |
| `fourier_jets_interior_derivative` | `D Jq = curry J(q+1)` on positive-time spacetime | Summable uniform derivative bounds on open slabs | C09; M06 |
| `fourier_jets_boundary_derivative` | Full `HasFDerivWithinAt` for every jet on the closed forward half-space | Interior identity; continuous jets; convexity and closure | C09; M08 |
| `parameter_fourier_contDiffOn` | Exact `ContDiffOn ℝ ∞` for the summed trajectory on forward spacetime | Compatible continuous within jets; unique differentiation | C09; M09 at finite orders, then M10 |
| `scalarL_trajectory_smooth` | Frozen scalar `L` preserves joint smoothness for every smooth spatially periodic trajectory | Exact cosine/multiplier identification | C09 |
| `vectorL_trajectory_smooth` | Vector counterpart | Same, componentwise | C09 |
| `scalarMean_trajectory_smooth` | The actual cube mean is smooth in time through zero | Coefficient time calculus at k=0 | C09–C10 |

The `L` trajectory lemmas have no divergence-free or mean-zero premise. This stronger contract prevents circular dependence through the four Hodge fields and applies directly to `Q = div G` and to the current-field reconstruction.

Jet representation adapters include the canonical identification of arity-zero multilinear maps with scalar values and the continuous linear currying equivalences for higher arities. These transport the explicit finite-coordinate jets; they add no analytic premise.

## 3. Final four endpoints

| Existing field | Construction | Exact preserved condition |
|---|---|---|
| `reconstruct_velocity` | Apply general Hodge with `div a=0`; restore `mean a` | Arbitrary velocity mean |
| `reconstruct_curl` | Apply curl-curl/Poisson with `div B=0` and `mean B=0` | Arbitrary independent m |
| `canonical_smoothness` | Parameter smoothness of `L`; actual spatial curl/divergence; smooth scalar mean | Joint `ContDiffOn ℝ ∞` through t=0; all three fields |
| `electric_hodge` | Derive `mean G=0` from Lamb identity and periodic integration, then general Hodge | Exact `headPotential = scalarL (div G)` and plus gradient sign |

Optional T07 pressure integration additionally requires the exact scalar-potential and zero-mode adapters. Full Leray projection preserves the constant mode; `K ∘ curl` removes it. Equality for the electric field follows only after `mean G=0` is proved.

## 4. Deterministic final composition

Prospective constructor:

```text
fourierHodgeLaws_proved : NSEMaxwell.Bridge.FourierHodgeLaws
  := { reconstruct_velocity := proved H1,
       reconstruct_curl := proved H2,
       canonical_smoothness := proved H3,
       electric_hodge := proved H4 }
```

Prospective root application:

```text
NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED
  fourierHodgeLaws_proved
  : NSEMaxwell.Classical.ExactEquivalence
```

The displayed forms specify proof dependencies. They are not `.lean` deliverables and do not establish `A_TIER_CANDIDATE` or `A_TIER` for the new constructor.

## 5. Source-port boundary

Mathlib endpoints are available at the target dependency pin. Selected Methlib files originate from Lean 4.33.0 and an older Mathlib pin. Their complete original imports are preserved in `../Fefferman_B_adapter/Endpoints/ENDPOINTS.json` and in the reference snapshots. Some imports reach Sobolev, Galerkin, or unrelated NSE modules.

Integration should transport only the required harmonic-analysis definitions and proof bodies into target-native modules, maintaining their explicit hypotheses. The copied endpoint reference files do not constitute a standalone build. The existing conditional equivalence is compiled separately through the adapter and directional source roots. No source-package global-existence endpoint, adjusted mean-zero theorem, all-order Sobolev admission, or unspecified inverse-Laplacian operator is part of the selected root route.

## 6. Compiler and audit gates

1. Exact frozen target signatures and dependency pins.
2. Existing compiler, dependency, compressed Mathlib download, and project caches retained.
3. External native Linux compilation with Lean `4.34.0-rc1`; no local Lean/Lake/elan.
4. Independent edge proofs elaborated asynchronously where the existing toolchain permits; pending signatures never count as proofs.
5. Deterministic final constructor and root application.
6. Named theorem-level axiom audits for every new edge, the H inhabitant, and the exact root; inherited upstream names audited as required.
7. Allowed foundational axioms: `propext`, `Classical.choice`, `Quot.sound` only.
8. Explicit accounting for every remaining theorem hypothesis; successful axiom audits do not discharge analytic premises.

The existing cached workflow remains the later execution path. This staging does not trigger a proof-status promotion or modify the workflow.
