# Maxwell endpoint

```text
PACKAGE                       = Maxwell_Endpoint
NATIVE_MODULE_ROOT            = MaxwellEndpoint
EXISTING_DEFINITION_NAMESPACE = NSEMaxwell.Classical
CURRENT_PACKAGE_STATUS        = A_TIER_FOR_EXACT_AUDITED_DECLARATIONS
CURRENT_EXTERNAL_VALIDATION   = PASS_RUN_43359539373
LOCAL_LEAN_EXECUTIONS         = 0
STANDALONE_AUDIT_TARGETS       = 62
NATIVE_MAXWELL_THEOREMS        = 23
NATIVE_DEFINITION_TYPE_TARGETS = 29
NATIVE_METHLIB_ENDPOINTS       = 10
INTEGRATED_AUDIT_TARGETS       = 236
```

## Contained dependency sources

[NativeSources/](NativeSources/) contains complete pinned snapshots of Mathlib and all eight companion dependency repositories, plus the selected 39-module native Methlib closure. [native-sources.json](native-sources.json) records each upstream revision, Git tree/blob identity and SHA256. Native `.lean` bytes and module paths are preserved; upstream Git attribute/ignore files retain their original bytes under `.upstream` basenames.

`scripts/hydrate_native_sources.py` reconstructs exact dependency checkouts from these contained sources on a cache miss. `scripts/verify_native_sources.py` verifies full source inventory, import closure and identity with actual compiler inputs. Existing dependency objects remain cached. `MethlibEndpoints.lean` provides ten separately audited harmonic-analysis declarations without introducing an NSE adapter import or discharging Hodge premises.

## Native source closure

| File | Scope |
|---|---|
| [MaxwellEndpoint/Geometry.lean](MaxwellEndpoint/Geometry.lean) | Actual three-dimensional fields, derivatives, cube integrals, periodicity, smoothness, magnetic data |
| [MaxwellEndpoint/Constitutive.lean](MaxwellEndpoint/Constitutive.lean) | Exact cosine-integral operators and canonical constitutive fields |
| [MaxwellEndpoint/System.lean](MaxwellEndpoint/System.lean) | Exact `MaxwellSolution` and `MaxwellB` definitions |
| [MaxwellEndpoint/Native.lean](MaxwellEndpoint/Native.lean) | Native construction, equation projections, and concrete zero-field instance |
| [MaxwellEndpoint.lean](MaxwellEndpoint.lean) | Native aggregate import |
| [MaxwellEndpoint/Audit.lean](MaxwellEndpoint/Audit.lean) | Exact declaration checks and theorem-level axiom audits |
| [lakefile.lean](lakefile.lean), [lake-manifest.json](lake-manifest.json), [lean-toolchain](lean-toolchain) | Standalone package and exact dependency/compiler pins |
| [run.sh](run.sh), [run.cmd](run.cmd), [scripts/](scripts/) | External native runners and evidence verification |
| [audit-targets.txt](audit-targets.txt), [cache-targets.txt](cache-targets.txt) | Named declaration audit and incremental Mathlib cache targets |
| [MAXWELL_ENDPOINT_A_TIER.txt](MAXWELL_ENDPOINT_A_TIER.txt) | Exact scope, proof boundary, and external certification record |

```text
NATIVE_IMPLEMENTATION_PROJECT_IMPORTS = MaxwellEndpoint.*
NATIVE_IMPLEMENTATION_EXTERNAL_IMPORTS = Mathlib
ADDITIONAL_AUDITED_SOURCE_CLOSURE = MethlibEndpoints + SingularClosure
ADAPTER_SOURCE_DEPENDENCY = NONE
DIRECTIONAL_SOURCE_DEPENDENCY = NONE
```

The original declaration names and definition bodies remain fixed. `Fefferman_adapter/NSEMaxwell/Classical.lean` imports this native endpoint and retains `NSSolution`, `FeffermanB`, and `ExactEquivalence`.

## Exact constrained system

For real parameters `ν`, `c`, arbitrary `m : Vec`, and `B₀ : Field`:

```lean
NSEMaxwell.Classical.MaxwellB (ν c : ℝ) : Prop :=
  ∀ (m : Vec) (B₀ : Field), MagneticData B₀ →
    ∃ (B E : Velocity) (ρ : Pressure) (J : Velocity),
      MaxwellSolution ν c m B₀ B E ρ J
```

```text
Vec = EuclideanSpace ℝ (Fin 3)
K B = curl (vectorL B)
u = m + K B
E = G[B] = B × u + ν curl B
ρ = div G[B]
J = c² curl B − DG[B](−curl G[B])
```

The Maxwell equations are

\[
\nabla\!\cdot B=0,\qquad
\partial_tB+\nabla\!\times E=0,\qquad
\nabla\!\cdot E=\rho,\qquad
\partial_tE-c^2\nabla\!\times B=-J.
\]

`MaxwellSolution` also requires joint `ContDiffOn ℝ ∞` through `t = 0`, spatial periodicity, zero spatial mean of `B`, the three exact constitutive identities, and `B 0 = B₀`. The time derivative is `derivWithin` on `[0,∞)`. All fields and operators have concrete Mathlib-based definitions.

## Concrete native instance

\[
\forall\nu,c\in\mathbb R,\ orall m\in\mathbb R^3:
\quad
\operatorname{MaxwellSolution}(\nu,c,m,0;0,0,0,0).
\]

The zero-field instance retains arbitrary `m`, with reconstructed velocity `U m 0 = fun _ => m`. `MaxwellEndpoint.zero_solution` contains the complete externally certified proof using constant derivatives, zero integrals, zero series, and the actual constitutive formulas. `MaxwellEndpoint.zero_datum_global_instance` combines admissibility with the explicit global witness. Both declarations passed the matching native Linux compiler and named axiom audit in [run 43351199370](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43351199370).

## Named native endpoints

All names below have namespace `MaxwellEndpoint`.

| Declaration | Exact conclusion |
|---|---|
| `equations_of_solution` | `MaxwellSolution ν c m B₀ B E ρ J → MaxwellEquations c B E ρ J` |
| `constitutive_fields_of_solution` | For every `t ≥ 0`, `E t = G ν m (B t)`, `ρ t = Q ν m (B t)`, and `J t = current ν c m (B t)` |
| `magnetic_evolution_of_solution` | For every `t ≥ 0`, `timeDerivative B t = V ν m (B t)` |
| `electric_evolution_of_solution` | For every `t ≥ 0`, `timeDerivative E t = DG ν m (B t) (V ν m (B t))` |
| `maxwellB_iff_native` | Exact unfolding equivalence for the existing `MaxwellB ν c` proposition |
| `U_zero` | `U m (0 : Field) = fun _ : Vec => m` |
| `magneticData_zero` | `MagneticData (0 : Field)` |
| `zero_solution` | Complete zero-field `MaxwellSolution`, for every real `ν`, `c`, and every `m : Vec` |
| `zero_datum_global_instance` | Zero-datum admissibility and existence of the explicit global solution |

The four solution projections retain their `MaxwellSolution` premise. The zero-field endpoints have no Hodge premise. [audit-targets.txt](audit-targets.txt) registers all **23 native theorems**, **29 concrete definition/type targets**, and **ten selected Methlib endpoints**; the integrated root audit registers **236 declarations**.

## External cached compilation

```bash
bash Maxwell_Endpoint/run.sh
```

```text
LEAN = leanprover/lean4:v4.34.0-rc1
MATHLIB = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
ALLOWED_AXIOMS = propext, Classical.choice, Quot.sound
CACHE_POLICY = PRESERVE_COMPILER_DEPENDENCY_PROJECT_CACHES
AUDIT_POLICY = FRESH_NAMED_DECLARATION_AUDIT
```

The independent build uses this folder as its project source closure. Root integration and isolated-package compilation passed their separate validations. The isolated build reconstructs its own dependency source checkouts, reuses verified dependency compilation objects, and maintains a separate project cache seeded by physical copies of matching audited root objects.

## Contained native source certificate

[Native Linux run 43359539373](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43359539373), source `1de664f2ef5ddc11caef25ac2274278b4171ab6b`:

| Scope | Fresh named audits | Matching source files | Matching Lean inputs |
|---|---:|---:|---:|
| Integrated repository | 236/236 | 20,353/20,353 | 19,160/19,160 |
| Isolated Fefferman | 236/236 | 9,968/9,968 | 9,592/9,592 |
| Isolated Maxwell | 62/62 | 9,914/9,914 | 9,563/9,563 |

All three builds and named axiom audits passed with only `propext`, `Classical.choice`, and `Quot.sound`. Each package contains **9,515 native Lean files** across nine complete pinned dependency snapshots, including **8,853 Mathlib Lean files**, plus the selected **39 Methlib modules**. The ten selected `SingularClosure` endpoints passed the target Lean `4.34.0-rc1` compiler and named audits. Every reachable non-compiler import is contained; missing and ambiguous modules are both zero. `Init`, `Lean`, `Std`, and `Lake` remain supplied by the pinned compiler distribution.

The integrated build restored exact compiler, dependency, and project caches and passed ordinary Lake trace validation with zero module-build invocations. Standalone source checkouts were reconstructed from contained files with zero dependency-source downloads. Their separate project caches received physical copies of matching audited root objects; subsequent native build validation and fresh audits passed. Incremental module-build invocations: **72 Fefferman**, **44 Maxwell**; these counts do not assert recompilation counts. Dependency compilation objects were shared; dependency source checkouts and standalone project object directories were separate.

Artifact `14008727271` contains **242 preserved files**; ZIP SHA256:
`e3c5b60b16610af15c6f40454698e35c81228a1b44c5bf490d41a852cf354482`.

The source manifests describe the compiled source commit. Documentation/evidence publication preserves all certified Lean sources, build configuration, runners, and audit inventories. The exact reduced implication remains **CONDITIONAL_FORMAL_CLOSURE**; `FourierHodgeLaws` remains an explicit unresolved premise, and arbitrary-data `FeffermanB`/`MaxwellB` existence is not proved.

[Integrated audit](../Auxillary/evidence/linux-43359539373/audit-summary.json) · [Maxwell audit](../Auxillary/evidence/linux-43359539373/standalone/audit-summary.json) · [Retained evidence](../Auxillary/evidence/linux-43359539373/)

## Initial native external certificate

[Native Linux run 43351199370](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43351199370) certified source commit `7e2bcf918b6bade04200a72c377ce0f7c9a5bbc6`.

| Scope | Fresh named audits | Matching Lean inputs | Result |
|---|---:|---:|---|
| Integrated repository | 226/226 | 37/37 | `PASS_STANDARD_ONLY` |
| Isolated Maxwell package | 52/52 | 7/7 | `PASS_STANDARD_ONLY` |

The isolated package verified all **18 source files** at the recorded source commit. It shared the verified dependency cache and used separate project build objects. Its initial independent project cache was absent; four native modules compiled and the resulting project cache was retained. The integrated runner used incremental build validation with 32 scheduled module-build invocations; this count does not assert 32 recompilations.

[Integrated audit](../Auxillary/evidence/linux-43351199370/audit-summary.json) · [Isolated audit](../Auxillary/evidence/linux-43351199370/standalone/audit-summary.json) · [Retained evidence](../Auxillary/evidence/linux-43351199370/)

```text
ARTIFACT_ID = 14003922945
PRESERVED_ORIGINAL_ARTIFACT_FILES = 109
ARTIFACT_SHA256 = 4da8e2720886ff08fd905a6e3b94ec579dcf0027411bd07e2c275dc7d282a2fb
ISOLATION = PASS
SHARED_DEPENDENCY_CACHE = TRUE
SHARED_PROJECT_OBJECT_CACHE = FALSE
```

The certificate identifies its compiled source snapshot. Subsequent documentation and evidence publication preserve the certified Lean/build inputs.

## Proof boundary

```text
CONCRETE_MODEL_DEFINITIONS = PRESENT
NATIVE_THEOREM_CERTIFICATION = A_TIER_STANDARD_AXIOMS_ONLY
ARBITRARY_DATA_MAXWELLB = NOT_PROVED
FOURIER_HODGE_LAWS_INHABITANT = NOT_SUPPLIED
UNCONDITIONAL_NSE_MAXWELL_EQUIVALENCE = NOT_PROVED
```

The Fourier formulas are total Lean definitions. Convergence, Poisson inversion, parameter smoothness, and the four `FourierHodgeLaws` fields remain separate analytic obligations. The standalone package supplies neither an assumed Hodge inhabitant nor an arbitrary-data global-existence proof.

## Adapter rename certificate

[Run 43353327242](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43353327242), source `8fd783b4d977fdb1a31cf4716023148ddfa26af9`: 226/226 integrated and 52/52 isolated audits passed; 37/37 integrated and 7/7 standalone Lean input hashes match. Both scopes reused trace-validated cached objects with zero module rebuilds. The 35 proof-module files remain byte-identical under the directory rename.

[Matching evidence](../Auxillary/evidence/linux-43353327242/).
