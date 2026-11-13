# Native checkpoint progress

`ORIGINAL_MANIFEST = checkpoint-manifest.json`

`ORIGINAL_CARDS = 75`; `ORIGINAL_PROSPECTIVE_DECLARATIONS = 361`; `ORIGINAL_ROOT = R1–R24`.

`∀ c ∈ {CP00,…,CP74}, c.lean_status = NOT_FORMALIZED`.

`NATIVE_DECLARATION_STATUS = A_TIER; SELECTED_TARGETS = 204/204; ROOT = CONDITIONAL_FORMAL_CLOSURE`.

`LOCAL_LEAN_EXECUTIONS = 0`.

The [manifest](checkpoint-manifest.json) retains the exact v1.8.0 checkpoint titles, output contracts, subgoals, prospective declarations and original pins. This document maps actual branch declarations to fragments of those contracts. It does not mutate the manifest, establish an original prospective declaration, or promote a complete card. The [endpoint index](ENDPOINT_INDEX.md) supplies pinned source-level dependencies; the [A-tier record](QUANTUM_ADAPTER_A_TIER.txt) supplies the separate external-evidence record.

A current native theorem may obtain external evidence before its larger original card is complete. Such evidence applies only to its exact source, type and premises. In particular, external success for the conditional native equivalence cannot establish the original R1–R24 root or discharge its analytic hypotheses.

## Coverage vocabulary

| Label | Exact interpretation |
|---|---|
| `BODY_FRAGMENT` | A named native proof body establishes a concrete identity/estimate on its displayed hypotheses; relation to a larger card is partial. External acceptance remains separately required. |
| `CONDITIONAL_FRAGMENT` | A named native proof body derives a consequence from explicit unresolved flow, transport or analytic assumptions; those assumptions remain in its type. |
| `INTERFACE_ONLY` | Concrete definitions, predicates, positive-parameter facts or structure fields prepare a card; the card's main assertion is not proved. |
| `RELATED_ONLY` | Actual objects overlap with a card's inputs, but no exact requested output/subgoal is claimed. |
| `EVIDENCE_PARTIAL` | Selected native declarations have matching external evidence; the full original CP29 theorem does not. |
| `NO_MAPPED_BODY` | No current native proof body is assigned to this card. |

These labels are coverage annotations. Every original card retains `NOT_FORMALIZED` regardless of its coverage label.

## Actual module inventory

| Native module | Related original cards | Present scope |
|---|---|---|
| `QuantumAdapter.Phase` | CP01–CP03, CP17, CP26, CP61 | Actual arbitrary-mean finite coefficient phase and datum embedding. |
| `QuantumAdapter.FiniteModel` | CP03–CP04, CP08, CP16, CP61 | Explicit synthesis, full convection, projected drift, H3 weight and cotangent derivative. |
| `QuantumAdapter.Tangency` | CP02–CP04, CP26 | Actual raw-RHS reality/solenoidality and equality to projected drift. |
| `QuantumAdapter.Energy` | CP04–CP05, CP15, CP40 | Actual full-mode cancellation and unweighted coefficient-energy derivative along supplied trajectories. |
| `QuantumAdapter.Born` | CP09, CP11, CP16, CP39 | Actual complex waves, Born integrals, normalization/MemLp/full multiplier-domain predicates. |
| `QuantumAdapter.Transport` | CP09, CP11, CP13 | Actual half-density formula and conditional measure/expectation transport. |
| `QuantumAdapter.L2Norm` | CP09 | Actual L2 norm/integral identity and conditional norm preservation. |
| `QuantumAdapter.L2Transport` | CP09 | Conditional descent to complex L2 quotient and actual linear isometric equivalence. |
| `QuantumAdapter.Dynamics` | CP05–CP11, CP13, CP16, CP39–CP40 | Intrinsic volume, Gaussian, actual-flow obligations and first-order differential expression. |
| `QuantumAdapter.RegularityContracts` | CP00, CP17, CP22, CP24, CP27, CP38 | Concrete cutoff-uniform predicates and explicit unresolved analytic estimates. |
| `NSEQuantumForward` | CP24, CP27, CP38 | Three ordered conditional forward edges. |
| `NSEQuantumReverse` | CP22, CP27, CP38 | Three ordered conditional reverse edges. |
| `NSEQuantumBridge` | CP00, CP27, CP29 | Deterministic conditional subset assembly. |

## Exact-card fragment map

Output numbers refer to the exact card's `output_contract`; lettered subgoals retain the exact manifest label. Card titles below are copied directly from the manifest. A reference to an output is a partial mapping, not a statement that the output is complete.

| Card / exact manifest title | Coverage | Actual native declarations | Exact fragment | Residual obligations |
|---|---|---|---|---|
| **CP00 — Frozen scope, predicates, and dependency identity** | `INTERFACE_ONLY`; `NOT_FORMALIZED` | [RegularityContracts](QuantumAdapter/RegularityContracts.lean): `centralEnergy`, `packetEnergy`, `G3`, `QREG`, `ExactQuantumEquivalence`; [bridge](NSEQuantumBridge.lean): `exact_quantum_conditional_root`. | Output01–02: concrete native predicates retain arbitrary smooth data and finite-horizon/cutoff quantifiers. The native root is the displayed conditional `FeffermanB ν ↔ QREG F` subset. | The complete R1–R24 contract, five original criteria, prescribed-family predicates, effective-data interfaces and all exact root projections remain unassembled. No identity between the native subset and `NSEQuantumBridge.RootContract` is proved. |
| **CP01 — Periodic quotient / physical-lift dictionary** | `RELATED_ONLY`; `NOT_FORMALIZED` | [Phase](QuantumAdapter/Phase.lean): `datumFourierCoeff_solenoidal`, `initialPhaseData_mean`. | Actual Euclidean periodic lifts and unit-cube Fourier integrals are used through the native field contracts. | All output01–05 quotient/lift dictionary theorems remain: quotient integrals, derivative/Laplacian transport, Fourier identity, closed-time extension dictionary and literal source-predicate transport. No quotient dictionary is inferred from coefficient membership. |
| **CP02 — Exact cutoff, Leray projector, and real Fourier eigenbasis** | `BODY_FRAGMENT`; `NOT_FORMALIZED` | [Phase](QuantumAdapter/Phase.lean): `fullModes_neg_mem`, `phaseCoeff_reality`, `phaseCoeff_solenoidal`, `initialAmbient_mem`; [Tangency](QuantumAdapter/Tangency.lean): `coefficientLeray_solenoidal`. | Fragments of output01–02: zero retained; exact nonzero source cutoff; actual coefficient reality/solenoidality and finite Leray algebra. | Physical L2 orthogonal projection, all commutation identities, explicit real Fourier eigenbasis, exact dimension `3+2*card(K_N^0)`, eigenvalue maximum and physical multiplier dictionary remain. An abstract orthonormal basis of the coefficient submodule does not prove the specified physical eigenbasis. |
| **CP03 — Real-coordinate / constrained-complex isometry and exact drift conjugacy** | `BODY_FRAGMENT`; `NOT_FORMALIZED` | [FiniteModel](QuantumAdapter/FiniteModel.lean): `synthesis_eq_mean_add_source`, `fullTransport_eq_source_add_mean`, `fullTransport_eq_source_of_mean_zero`; [Tangency](QuantumAdapter/Tangency.lean): `drift_eq_rawRhs`, `drift_mean`. | Coefficient-level fragments of output04–05: actual finite drift retains constant advection, reduces to source transport under an explicit zero-mean premise, and has zero mean derivative. | Explicit `Realify_N`, exact real coordinate dimension, physical Parseval and Hs isometries, literal conjugacy with the prescribed real Fourier coordinate drift, and source finite-Galerkin solution identification remain. Projection onto the constrained submodule is not a proof of physical isometry. |
| **CP04 — Polynomial drift, local solutions, and exact energy/mean identities** | `BODY_FRAGMENT`; `NOT_FORMALIZED` | [Tangency](QuantumAdapter/Tangency.lean): `rawRhs_tangent`, `drift_mean`; [Energy](QuantumAdapter/Energy.lean): `fullTransport_complex_energy_zero`, `rawRhs_energy_rate`, `IsTrajectory.energy0_identity`; [FiniteModel](QuantumAdapter/FiniteModel.lean): `zero_isTrajectory`. | Actual unweighted coefficient-energy fragments of output02–04: nonlinear cancellation, exact viscous rate and within-derivative along an actual supplied trajectory. The zero trajectory has a body. | Polynomial/smooth/local-Lipschitz drift proofs, general local existence/uniqueness, the full bilinear tensor identities, real-coordinate/physical norm transport, and conservation of mean along arbitrary trajectories remain. Zero mean derivative alone does not constitute the complete conservation theorem. |
| **CP05 — Complete two-sided finite flow** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [Energy](QuantumAdapter/Energy.lean): `IsTrajectory.energy0_antitoneOn`, `IsTrajectory.energy0_le_initial`; [Dynamics](QuantumAdapter/Dynamics.lean): `PhaseFlow`, `phaseFlow_isTrajectory`. | For an actual supplied trajectory and `0≤ν`, coefficient energy decreases on `Ici 0`. Supplied `PhaseFlow` gives an actual trajectory. | No complete-flow inhabitant or uniqueness is constructed. Backward exponential bound, two-sided finite escape exclusion and continuation remain. `PhaseFlow` quantification is an explicit assumption, not output01. |
| **CP06 — Joint smooth dependence, flow group, inverse, and variational equation** | `INTERFACE_ONLY`; `NOT_FORMALIZED` | [Dynamics](QuantumAdapter/Dynamics.lean): `PhaseFlow.map_zero`, `.map_add`, `.orbit_derivative`; `phaseFlow_isTrajectory`. | Zero/group equations and actual ODE derivative are retained as structure fields; trajectory continuity follows from the derivative field. | Derivation of group/inverse laws from unique complete solutions; joint smoothness; variational equation; smooth diffeomorphism and derivative-inverse identities; compact time/initial support transport all remain. |
| **CP07 — Constant Euler divergence, viscous trace, and exact flow Jacobian** | `INTERFACE_ONLY`; `NOT_FORMALIZED` | [Dynamics](QuantumAdapter/Dynamics.lean): `finiteLaplaceTrace`, `finiteLaplaceTrace_nonneg`, `driftDivergence`, `PhaseFlow.divergence_eq`. | Explicit finite trace expression and nonnegativity have native bodies; actual derivative trace is defined; its equality to `-phaseDecayRate` is a field. | Constant diagonal kernel, zero Euler divergence, identification of the physical spectral trace, strict positivity for `ν>0,N≥1`, determinant derivative and exact Jacobian remain. Defining a finite sum does not prove it is the drift trace. |
| **CP08 — Canonical lift and dense symmetric minimal operator** | `BODY_FRAGMENT`; `NOT_FORMALIZED` | [FiniteModel](QuantumAdapter/FiniteModel.lean): `cotangent_momentum_increment`, `cotangent_hasFDerivAt_momentum`, `cotangent_fderiv_momentum`; [Dynamics](QuantumAdapter/Dynamics.lean): `hamiltonianExpression`, `HamiltonianTestDomain`. | Part of output01: actual cotangent Hamiltonian `inner ℝ p (drift ν N q)` and its momentum derivative. Actual differential expression and smooth compact-support predicate are defined. | Configuration derivative and momentum Hamilton equation; dense L2 test submodule; quotient-independent unbounded operator; domain preservation, CCR and formal symmetry remain. A function expression and domain predicate are not a densely defined symmetric operator. |
| **CP09 — Jacobian-weighted strongly continuous unitary group** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [Transport](QuantumAdapter/Transport.lean): `halfDensityPullback_add`, `halfDensityPullback_inverse`; [L2Norm](QuantumAdapter/L2Norm.lean): `halfDensityPullback_toLp_norm`; [L2Transport](QuantumAdapter/L2Transport.lean): `halfDensityPullback_congr_ae`, `l2PullbackEquiv`, `l2Pullback_add_times`. | Conditional output01–03 fragments: actual complex-L2 quotient transport, AE compatibility, norm preservation, complex linearity and inverse at `-t`. The construction requires actual integral/MemLp transport laws and the respective flow laws. | Derive those laws for the actual Galerkin flow from its Jacobian; identify an adjoint/unitary-group package as needed; prove norm continuity in time and invariance of the actual compact-smooth L2 core. No strong continuity is supplied by an isometric equivalence at each time. |
| **CP10 — Explicit nonreal resolvents, selfadjoint closure, maximal domains and core** | `INTERFACE_ONLY`; `NOT_FORMALIZED` | [Dynamics](QuantumAdapter/Dynamics.lean): `hamiltonianExpression`, `HamiltonianTestDomain`; [L2Transport](QuantumAdapter/L2Transport.lean): conditional `l2PullbackEquiv`. | Input-level objects related to CP10.b `actual_core_derivative` only; no CP10 output theorem is claimed. | Every CP10.a–h subgoal remains: dense symmetric graph closure; L2 core differentiation; both actual nonreal resolvents; graph/core integrals; full inverse ranges; selfadjointness; exact maximal domains and strong Schrödinger evolution; resolvent algebra and quantitative graph core. |
| **CP11 — Maximal multipliers and exact Heisenberg NSE** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [Born](QuantumAdapter/Born.lean): `MultiplierDomain`, `ObservableIntegrable`, `expectation_congr_ae`; [Transport](QuantumAdapter/Transport.lean): `expectation_halfDensityPullback`; [Dynamics](QuantumAdapter/Dynamics.lean): `quantumEnergy_conjugacy`. | Quadratic-form/expectation fragment related to CP11.b `domain_conjugacy`: exact integrable expectation conjugacy under explicit transport laws. The full multiplier-domain predicate retains `MemLp ((f:ℂ)*ψ) 2 μ`. | CP11.a actual maximal selfadjoint L2 multiplier, CP11.b domain equality, CP11.c domain-aware commutator, and CP11.d multiplication spectral projections remain. Scalar expectation equality is weaker than unbounded-operator/domain equality. |
| **CP13 — Finite-cutoff stability and quantitative packet localization** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [Transport](QuantumAdapter/Transport.lean): `expectation_halfDensityPullback`; [Dynamics](QuantumAdapter/Dynamics.lean): `quantumEnergy_conjugacy`. | A generic integral identity supports part of output03 when its flow/integrability hypotheses are supplied; canonical native packets are Gaussian. | Compact packet construction and support, finite-cutoff stability, actual normalization/domain membership, uniform localization limits and explicit energy/gradient error estimates remain. The current Gaussian formulas are not the original compact packet family. |
| **CP15 — Energy dissipation, shear model, spectral and coercivity diagnostics** | `BODY_FRAGMENT`; `NOT_FORMALIZED` | [Energy](QuantumAdapter/Energy.lean): `rawRhs_energy_rate`, `IsTrajectory.energy0_identity`, `IsTrajectory.energy0_le_initial`. | Classical coefficient-energy input to CP15.a `fluid_energy_dissipation`; exact actual ODE rate is prepared. | Domain-aware Heisenberg energy commutator and quantum expectation derivative remain. CP15.b–e independent shear quantization, unbounded numerical range, spectral implication and translated noncoercive family remain. CP15 remains supporting rather than a new root assumption. |
| **CP16 — Exact H3 and gradient quantum observables at fixed cutoff** | `INTERFACE_ONLY`; `NOT_FORMALIZED` | [FiniteModel](QuantumAdapter/FiniteModel.lean): `energy3`, `energy3_nonneg`, `gradientSquare`, `gradientObservable`; [Dynamics](QuantumAdapter/Dynamics.lean): `quantumEnergy`, `quantumAdmissible`, `quantumEnergy_nonneg`. | Explicit weighted coefficient H3 candidate and actual spatial derivative/supremum expression; actual expectation and full state/observable admissibility predicates. | Identify coefficient energy with physical H3 norm; prove gradient supremum finiteness/continuity; construct maximal selfadjoint multipliers; prove all fixed-cutoff profile-independent localization and integrated-gradient limits. Nonnegative totalized integral does not prove integrability. |
| **CP17 — Periodic Sobolev realization, projections, tails, and compact inclusion** | `INTERFACE_ONLY`; `NOT_FORMALIZED` | [Phase](QuantumAdapter/Phase.lean): `initialPhase_coeff`, `initialPhaseData_mean`; [RegularityContracts](QuantumAdapter/RegularityContracts.lean): `InitialProjectionBounds`. | Actual initial Fourier coefficients are explicit, including the mean. Uniform initial weighted bound remains a named premise. | All physical/weighted Sobolev isometries, projection contraction, tails, compact adjacent inclusions and smooth-data convergence remain. `InitialProjectionBounds` is not a proved Sobolev projection theorem. |
| **CP22 — Normalized pressure, smooth uniqueness, global gluing: G3 implies FB** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [reverse direction](../B%20%3C-%3E%20Quantum/%3C%3D/NSEQuantumReverse.lean): `galerkin_implies_feffermanB_of_analyticLaws`; [RegularityContracts](QuantumAdapter/RegularityContracts.lean): `GalerkinAnalyticLaws.compactness`. | Conditional aggregation corresponding to output04: fixed-datum all-horizon compactness hypothesis produces the exact native `NSEMaxwell.Classical.NSSolution` and hence `FeffermanB`. | The compactness inhabitant, physical nonlinear passage, pressure construction/normalization, uniqueness and global gluing remain. Native pressure gauge is preserved; literal equality with the TXT normalized-pressure contract needs a separate adapter. |
| **CP24 — Nonlinear stability bootstrap and all-cutoff bound: FB implies G3** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [forward direction](../B%20%3C-%3E%20Quantum/%3D%3E/NSEQuantumForward.lean): `feffermanB_implies_galerkin_of_analyticLaws`; [RegularityContracts](QuantumAdapter/RegularityContracts.lean): `GalerkinAnalyticLaws.smooth_stability`. | Conditional aggregation corresponding to output04: extract each native smooth solution and apply the named finite-horizon stability estimate. | The actual reference residual, error equation, cutoff-independent nonlinear bootstrap, high-cutoff convergence and finitely many low-cutoff bounds remain. The structure field is an unresolved analytic estimate. |
| **CP26 — Galilean mean transport and exact source predicate identification** | `BODY_FRAGMENT`; `NOT_FORMALIZED` | [Phase](QuantumAdapter/Phase.lean): `initialPhaseData_mean`; [FiniteModel](QuantumAdapter/FiniteModel.lean): `fullTransport_eq_source_add_mean`; [Tangency](QuantumAdapter/Tangency.lean): `drift_mean`. | Arbitrary mean is retained in initial coefficients and convection; actual mean derivative vanishes. | Galilean moving-frame conjugacy of complete flows/physical solutions, pressure-gauge dictionary and literal source predicate identification remain. No mean-zero replacement of native `FeffermanB` is performed. |
| **CP27 — Quantum/classical criterion equivalences** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [forward direction](../B%20%3C-%3E%20Quantum/%3D%3E/NSEQuantumForward.lean), [reverse direction](../B%20%3C-%3E%20Quantum/%3C%3D/NSEQuantumReverse.lean): six independent named implication bodies; [bridge](NSEQuantumBridge.lean): `feffermanB_iff_qreg_of_analytic_bounds`. | A concrete conditional equivalence among native `FeffermanB`, actual central-energy `G3`, and actual finite-width canonical-Gaussian `QREG`, with datum/horizon-dependent but cutoff-independent bounds. | Original five-criterion equivalence, LIP/QLIP routes and exact identification with the original localization-limit QREG remain. The native `QREG F` is not silently identified with the original `(ν,ℏ)` predicate; selfadjoint-generator construction and all analytic contracts remain open. |
| **CP29 — Deterministic assembly of the exact strengthened root** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [bridge](NSEQuantumBridge.lean): `exactQuantumEquivalence_of_analytic_bounds`, `exact_quantum_conditional_root`. | Deterministic assembly of the displayed native conditional subset only; exact analytic premises stay in the type. | The complete R1–R24 strengthened root and every retained domain/family/covariance/resolvent/effective-access/name/refinement projection remain unassembled. This subset theorem is not the original CP29 endpoint. |
| **CP31 — Cached external compilation and theorem-level evidence** | `EVIDENCE_PARTIAL`; `NOT_FORMALIZED` | [A-tier record](QUANTUM_ADAPTER_A_TIER.txt), repository cached external compilation/audit workflow. | The 204 selected native declarations have exact matching external theorem-level evidence at commit 216217a88fc8039b5551738a0ce3b6bbe884e45d. No local Lean execution is authorized or recorded. | CP31 requires evidence for the source containing the full CP29 theorem. Evidence for a smaller conditional native theorem may promote only that exact theorem, never CP29 or the whole original checkpoint set. |
| **CP38 — Exact noncompact moment-family quantum criterion equivalence** | `CONDITIONAL_FRAGMENT`; `NOT_FORMALIZED` | [RegularityContracts](QuantumAdapter/RegularityContracts.lean): `forwardPacketBound`, `reversePacketBound`, their nonnegativity theorems, `PacketBounds`; directional `galerkin_implies_quantum_of_packetBounds`, `quantum_implies_galerkin_of_packetBounds`. | Canonical-Gaussian numeric specialization related to CP38.a `forward_reference_bound` and CP38.d `center_reconstruction`: explicit `D₂=1/2`, `λ=1` formulas and deterministic propagation of assumed per-cutoff estimates. | Derive the actual forward estimate, probability Cauchy–Schwarz, selected reference and tame/reference stability; prove every-λ family, QLIP route, errors and compact-family specialization. CP38.a–e analytic subgoals remain; defining the formulas does not prove the estimates. |
| **CP39 — Gaussian normalization, exact moments, Schwartz domains and Weyl kinematics** | `INTERFACE_ONLY`; `NOT_FORMALIZED` | [Dynamics](QuantumAdapter/Dynamics.lean): `phaseVolume`, `canonicalScale`, `canonicalScale_pos`, `gaussianAmplitude_pos`, `canonicalPacket_im`, `canonicalPacket_center`, `canonicalPacket_re_pos`; [Born](QuantumAdapter/Born.lean): `WaveAdmissible`. | Positive-parameter/formula portion of CP39.a `gaussian_normalization`; explicit intrinsic real Haar measure and centered Gaussian; canonical scale formula relevant to CP39.h `canonical_family_instance`. | Gaussian integral normalization, exact covariance/radial moments and `ω_N=1/(N+1)` calculation remain. CP39.b–i actual moments, variances, polynomial Schwartz action, Hamiltonian domain powers, cutoff/tail rates, canonical family proof, closed momenta and Weyl identities remain. `PacketBounds.admissible` assumes the required transported-state facts. |
| **CP40 — Finite Fourier traces, harmonic coefficient drift and initial Gaussian consistency** | `INTERFACE_ONLY`; `NOT_FORMALIZED` | [Dynamics](QuantumAdapter/Dynamics.lean): `finiteLaplaceTrace`, `finiteLaplaceTrace_nonneg`; [FiniteModel](QuantumAdapter/FiniteModel.lean): `gradientSquare`, `gradientObservable`; [Energy](QuantumAdapter/Energy.lean): actual classical dissipation. | Concrete finite expressions related to CP40.c `gradient_kernel_trace` and output06; no CP40 trace/moment identity is derived from them. | CP40.a nonlinear projection trace, .b coefficient harmonicity, .c exact physical gradient-kernel trace, .d Gaussian drift/centroid and .e phase/quadratic moments all remain. Classical orbit dissipation is distinct from Gaussian expectation identities. |
| **CP61 — Explicit full real Fourier frame and actual finite coefficient circuits** | `RELATED_ONLY`; `NOT_FORMALIZED` | [Phase](QuantumAdapter/Phase.lean): `fullModes`, `initialPhase_coeff`, `initialPhaseData_mean`; [FiniteModel](QuantumAdapter/FiniteModel.lean): `fullTransport`; [Tangency](QuantumAdapter/Tangency.lean): `drift_mean`. | Actual full complex coefficient realization and vanishing mean rows are inputs related to CP61.d `projected_tensor_and_trace` and .e `datum_coefficients`. | All explicit half-lattice/polarization construction, real sine/cosine orthonormal frame, exact dimension and resonance tensor, signed sine-coordinate dictionary, effective finite circuit/parameter syntax and basis-access distinction remain. An abstract Hilbert basis is not the prescribed explicit effective Fourier frame. |

## Analytic premise placement

| Current explicit premise | Original work still required | Non-implication |
|---|---|---|
| `F : PhaseFlow ν` | CP04 local theory; CP05 complete flow; CP06 smooth/group theory; CP07 actual divergence. | A quantified structure is not an existence theorem. |
| `PhaseTransportLaws F` | CP07 exact Jacobian and change of variables; CP09 L2 membership transport. | Algebraic group laws alone do not imply measure transport. |
| `PacketBounds.admissible` | CP11 multiplier domains; CP37 finite-moment integrability; CP39 actual Gaussian normalization/domains. | Positivity, a finite formal expression, or a totalized integral does not establish normalized admissibility. |
| `PacketBounds.forward_estimate` | CP32 reference-gradient stability; CP37 actual moments/Fubini; CP38.a forward reference bound. | Defining `forwardPacketBound` proves neither stability nor expectation control. |
| `PacketBounds.reverse_estimate` | CP18–CP19 embedding/tame estimates; CP32 reference stability; CP37 selected reference; CP38.b–d reconstruction. | A global `G3` estimate may not be applied to cutoff-dependent sampled data. |
| `InitialProjectionBounds` | CP17 actual Sobolev projection/isometry and smooth-data bound. | Having actual Fourier coefficients does not prove a cutoff-independent H3 bound. |
| `GalerkinAnalyticLaws.smooth_stability` | CP23 spectral residual/error equation; CP24 nonlinear bootstrap and all-cutoff bound. | The conditional forward composition does not prove this analytic field. |
| `GalerkinAnalyticLaws.compactness` | CP17–CP22 derivative bounds, compactness, nonlinear passage, pressure, uniqueness and gluing. | The conditional reverse composition does not construct these continuum objects. |

The exact native root remains:

```lean
∀ ν : ℝ, 0 < ν → ∀ F : QuantumAdapter.PhaseFlow ν, ∀ Cemb C3 : ℝ,
  QuantumAdapter.GalerkinAnalyticLaws F →
  QuantumAdapter.PacketBounds F Cemb C3 →
  QuantumAdapter.InitialProjectionBounds →
  (NSEMaxwell.Classical.FeffermanB ν ↔ QuantumAdapter.QREG F)
```

The original native `FeffermanB` datum, pressure and closed-time regularity conventions are retained. The new `QREG F` concerns the actual canonical Gaussian energy criterion and contains full state/observable admissibility. It has no artificial `ℏ` parameter. Identifying it with the original localization-limit predicate or a Schrödinger-generator predicate requires additional theorems.

## Remaining cards without an assigned native body

For every row: `coverage = NO_MAPPED_BODY`; `lean_status = NOT_FORMALIZED`. All output contracts and subgoals in the manifest remain. Importing upstream material or defining a nearby object does not change this status.

| Card | Exact manifest title | TXT sections |
|---|---|---|
| CP12 | C0 characters and exact deterministic reconstruction | 8.1, 18.4, 19/AD08 |
| CP14 | Orthogonal covariance and viscosity/hbar normalization | 7.A, 15.1 |
| CP18 | Periodic algebra, Sobolev embedding, and higher-order interpolation | 10.2, 10.3, 12.3 |
| CP19 | Cutoff-independent tame energy inequality | 10.3, 10.4 |
| CP20 | G3 gives all spatial and time derivative bounds | 12.1, 12.2 |
| CP21 | Smooth compactness through t=0 and nonlinear equation passage | 12.3, 12.4 |
| CP23 | Smooth-reference spectral residual and exact Galerkin error equation | 13, 13.1 |
| CP25 | Equivalence of the H3 and integrated-gradient criteria | 14.A, 10.4 |
| CP28 | Mean, basis, and parameter covariance of criterion predicates | 2.A, 7.A, 14.A, 15.1 |
| CP30 | Optional AX6-to-quantum application | 18.2/MT12, 18.2/MT19, 19/AD14 |
| CP32 | Reference-gradient L2 stability and exact spectral H3 upgrade | 8.5, 19/AD15 |
| CP33 | Prescribed packets, Born probability measure, Fubini and reference selection | 14.B, 18.5, 19/AD15 |
| CP34 | Exact finite-width quantum criterion equivalence and full-ball bound | 14.B, 19/AD15 |
| CP35 | Quantitative packet errors and conditional continuum-observable limits | 14.C, 13.3, 19/AD15 |
| CP36 | Compact localization and the explicit conjugate-momentum lower bound | 15.6, 18.5/MT21, 19/AD16, 14.E.4/G13 |
| CP37 | Finite-moment profiles, noncompact domains, Fubini and joint-score selection | 14.D.1--14.D.3, 19/AD17 |
| CP41 | Actual affine resolvent and unitary Cayley step | 14.F.1, 19/AD19 |
| CP42 | Weighted state spaces, dissipativity and Cayley contraction | 14.F notation, 14.F.2--14.F.3, 19/AD19 |
| CP43 | Exact trapezoid defect and weighted quadratic finite-product error | 14.F.4--14.F.5, 19/AD19 |
| CP44 | Actual unbounded-observable error and explicit horizon-dependent schedule | 14.G.1--14.G.3, 19/AD19 |
| CP45 | Exact finite-resolvent-product criteria and conditional continuum limits | 14.G.4--14.G.5, 19/AD19 |
| CP46 | Finite Gaussian polynomial Hamiltonian powers and exact weighted moment data | 14.H.0--14.H.6, 19/AD20 |
| CP47 | Positive Gaussian coefficient bounds and finite exact/conservative schedules | 14.H.7--14.H.8, 19/AD20 |
| CP48 | Positive Cayley partitions and continuous partial-step errors | 14.I.0--14.I.3, 19/AD21 |
| CP49 | Dyadic refinement, summable cutoff budgets and exact partition criteria | 14.I.4--14.I.5, 19/AD21 |
| CP50 | Actual residual certificates, finite accumulation and normalized nodal observables | 14.J.0--14.J.6, 19/AD21 |
| CP51 | Derived core residual witnesses and continuous affine reconstruction | 14.K.1--14.K.4, 19/AD22 |
| CP52 | Normalized core paths, summable approximation budgets and exact regularity criteria | 14.K.5--14.K.7, 19/AD22 |
| CP53 | Explicit Hermite family and proved L2 completeness | 14.L.1--14.L.3, 14.L.6, 19/AD23 |
| CP54 | Explicit Hermite tails and density in the full actual weighted graph domain | 14.L.4--14.L.9, 19/AD23 |
| CP55 | Finite Hermite least-residual matrices and actual resolvent access | 14.M.0--14.M.5, 19/AD24 |
| CP56 | Rational polynomial residual witnesses and finite-coefficient state paths | 14.M.6--14.M.8, 19/AD24 |
| CP57 | Finite rational interval arithmetic and exact polynomial-Gaussian residual bounds | 14.N.1--14.N.3, 19/AD25 |
| CP58 | Total finite residual and accuracy checkers with normalized-path soundness | 14.N.4, 14.O.1--14.O.2, 19/AD25 |
| CP59 | Finite certificate existence, conditional terminating search and exact regularity criteria | 14.O.3--14.O.5, 19/AD25 |
| CP60 | Total certified rational names and finite arithmetic circuit access | 14.P.1--14.P.5, 19/AD26 |
| CP62 | Derived effective parameter enclosures and finite rational-data access | 14.Q.6--14.Q.9, 19/AD27 |
| CP63 | Rational matrix inversion and monomial inverse-defect certificates | 14.R.0--14.R.5, 19/AD28 |
| CP64 | Adaptive degree/precision least-residual refinement and tuple termination | 14.R.6--14.R.9, 19/AD28 |
| CP65 | Refined finite checkers, uniform approximation and finite path reconstruction | 14.S.1--14.S.5, 19/AD29 |
| CP66 | Effective finite-input quantum access, exact energy names and all-data criteria | 14.S.5--14.S.6, 19/AD29 |
| CP67 | Exact Hessian trace, Frobenius gradient and periodic maximum grids | 14.T.1--14.T.2, 19/AD30 |
| CP68 | Total elementary function names and actual spatial-gradient names | 14.T.3, 19/AD30 |
| CP69 | Finite Gaussian moment tails and normalized gradient quadrature | 14.U.0--14.U.2, 19/AD31 |
| CP70 | Actual pointwise gradient expectation names | 14.U.3--14.U.4, 19/AD31 |
| CP71 | Exact weighted-orbit and observable temporal Lipschitz bounds | 14.V.1--14.V.2, 19/AD32 |
| CP72 | Exact finite-horizon extrema and integral names | 14.V.3--14.V.5, 19/AD32 |
| CP73 | Uniform named scalar sequences and strict-threshold witnesses | 14.W.1--14.W.2, 19/AD33 |
| CP74 | Exact rational boundedness with the full cutoff quantifiers retained | 14.W.3--14.W.4, 19/AD33 |

## Promotion invariant

```text
Source-verified upstream declaration ≠ accepted native caller.
Accepted native fragment ≠ complete original checkpoint.
Accepted conditional equivalence ≠ analytic-premise discharge.
Accepted conditional subset ≠ original R1–R24 root.

Full-card promotion requires:
  exact original endpoint
  + complete displayed premises
  + matching external cached compilation
  + theorem-level axiom audit
  + source/dependency/evidence identity.
```


[Exact native evidence](../Auxillary/quantum/evidence/216217a88fc8039b5551738a0ce3b6bbe884e45d/): 14 build modules (13 declaration modules plus the public aggregator); source hashes and explicit premises retained.
