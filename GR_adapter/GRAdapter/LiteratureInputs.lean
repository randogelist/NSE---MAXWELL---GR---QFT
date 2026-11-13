import GRAdapter.Boundary

/-!
# Explicit source-facing literature signatures

LI01: Chaperon, On the Cauchy-Kowalevski theorem, Section 2, equation (2).
LI02: Dahia--Romero, gr-qc/0109076, Lemmas 1 and 2, Theorem 2 sufficient
direction; fixed lapse 1, extra sign +1, zero cosmological constant.
LI03: Guillemin, Notes for 18.117 (2005), Section 4, Propositions 4.1/4.3,
Corollary 4.2 and equation (4.5), after the period-one normalization.

These are concrete mathematical propositions, not new axioms and not
inhabitants of the propositions. All four project adapter contracts remain
separate obligations. In particular no periodic collar, scalar completion,
constitutive residual, or inverse-germ theorem occurs in the input fields.

The germ formulation uses globally typed functions whose behavior is
constrained only on neighborhoods. It is equivalent to the usual source
formulation on open neighborhoods by restriction and arbitrary extension.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

namespace NSEGR

noncomputable section

abbrev LiteratureSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

abbrev LiteratureCKJet (n m : ℕ) :=
  (ℝ × LiteratureSpace n) ×
    (LiteratureSpace m × (LiteratureSpace n →L[ℝ] LiteratureSpace m))

abbrev LiteratureCKRHS (n m : ℕ) := LiteratureCKJet n m → LiteratureSpace m

def LiteratureCKInitialJet {n m : ℕ} (t0 : ℝ) (x0 : LiteratureSpace n)
    (u0 : LiteratureSpace n → LiteratureSpace m) : LiteratureCKJet n m :=
  ((t0, x0), (u0 x0, fderiv ℝ u0 x0))

/-- Actual analytic Cauchy solution near one base point; all equality data are
germs on neighborhoods, not just equality of values at the base point. -/
structure LiteratureCKSolution {n m : ℕ} (F : LiteratureCKRHS n m)
    (u0 : LiteratureSpace n → LiteratureSpace m) (t0 : ℝ)
    (x0 : LiteratureSpace n)
    (u : ℝ × LiteratureSpace n → LiteratureSpace m) : Prop where
  analytic : AnalyticAt ℝ u (t0, x0)
  initial : ∀ᶠ x in 𝓝 x0, u (t0, x) = u0 x
  equation : ∀ᶠ z in 𝓝 (t0, x0),
    deriv (fun t : ℝ => u (t, z.2)) z.1 =
      F (z, (u z, fderiv ℝ (fun x => u (z.1, x)) z.2))

/-- LI01. The finite-dimensional first-order analytic CK theorem, including
analytic solution-germ uniqueness. No radius uniformity is assumed. -/
structure LiteratureAnalyticCKInput : Prop where
  exists_unique : ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ (F : LiteratureCKRHS n m)
      (u0 : LiteratureSpace n → LiteratureSpace m)
      (t0 : ℝ) (x0 : LiteratureSpace n),
      AnalyticAt ℝ u0 x0 →
      AnalyticAt ℝ F (LiteratureCKInitialJet t0 x0 u0) →
      ∃ u : ℝ × LiteratureSpace n → LiteratureSpace m,
        LiteratureCKSolution F u0 t0 x0 u ∧
        ∀ v : ℝ × LiteratureSpace n → LiteratureSpace m,
          LiteratureCKSolution F u0 t0 x0 v → u =ᶠ[𝓝 (t0, x0)] v

/-- Flat constrained analytic boundary data near a single boundary point.
No periodicity, rho normalization, or constitutive condition is present. -/
structure LiteratureFlatBoundaryGerm (K : BoundaryTensor) (t0 : ℝ)
    (x0 : Vec) : Prop where
  analytic : AnalyticAt ℝ (fun z : ℝ × Vec => K z.1 z.2) (t0, x0)
  symmetric : ∀ᶠ z in 𝓝 (t0, x0), (K z.1 z.2).IsSymm
  hamiltonian : ∀ᶠ z in 𝓝 (t0, x0), boundaryHamiltonian K z.1 z.2 = 0
  codazzi : ∀ᶠ z in 𝓝 (t0, x0), ∀ b : Fin 4, boundaryCodazzi K z.1 z.2 b = 0

/-- Actual Gaussian metric germ with both prescribed boundary data germs.
The native Lorentzian change-of-basis witness is not inserted as an input;
it remains a consequence to derive from the induced eta metric. -/
structure LiteratureFlatGaussianGerm (K : BoundaryTensor) (t0 : ℝ)
    (x0 : Vec) (g : Metric) : Prop where
  analytic : AnalyticAt ℝ g (bulkPoint 0 t0 x0)
  symmetric : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), (g z).IsSymm
  nondegenerate : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), (g z).det ≠ 0
  gaussian_rr : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), g z 0 0 = 1
  gaussian_rboundary : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0),
    ∀ a : Fin 4, g z 0 (boundaryIndex a) = 0
  induced : ∀ᶠ z in 𝓝 (t0, x0), ∀ a b : Fin 4,
    g (bulkPoint 0 z.1 z.2) (boundaryIndex a) (boundaryIndex b) = eta4 a b
  boundary_match : ∀ᶠ z in 𝓝 (t0, x0), boundaryK g z.1 z.2 = K z.1 z.2
  vacuum : ∀ᶠ z in 𝓝 (bulkPoint 0 t0 x0), ricci g z = 0

/-- LI02. Point-local prescribed-data Gaussian vacuum existence and uniqueness.
The source extrinsic-curvature sign is the negative of `boundaryK`.
Uniqueness is in the same coordinates and normal orientation. -/
structure LiteratureGaussianJetInput : Prop where
  exists_unique : ∀ (K : BoundaryTensor) (t0 : ℝ) (x0 : Vec),
    LiteratureFlatBoundaryGerm K t0 x0 →
      ∃ g : Metric, LiteratureFlatGaussianGerm K t0 x0 g ∧
        ∀ h : Metric, LiteratureFlatGaussianGerm K t0 x0 h →
          g =ᶠ[𝓝 (bulkPoint 0 t0 x0)] h

abbrev LiteratureFrequency (n : ℕ) := Fin n → ℤ

def LiteratureUnitVector {n : ℕ} (i : Fin n) : LiteratureSpace n :=
  EuclideanSpace.single i (1 : ℝ)

def LiteratureUnitCube (n : ℕ) : Set (LiteratureSpace n) :=
  {x | ∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1}

def LiteraturePeriodic {n : ℕ} (f : LiteratureSpace n → ℂ) : Prop :=
  ∀ (x : LiteratureSpace n) (i : Fin n), f (x + LiteratureUnitVector i) = f x

/-- The actual unit-period character; no Fourier data are supplied abstractly. -/
def LiteratureCharacter {n : ℕ} (k : LiteratureFrequency n)
    (x : LiteratureSpace n) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
    ((∑ i : Fin n, (k i : ℝ) * x i : ℝ) : ℂ))

def LiteratureFourierCoefficient {n : ℕ} (f : LiteratureSpace n → ℂ)
    (k : LiteratureFrequency n) : ℂ :=
  ∫ x in LiteratureUnitCube n, f x * LiteratureCharacter (-k) x

/-- A finite coordinate derivative word, expressed using actual Frechet
derivatives. Smoothness identifies these with the usual multiindex partials. -/
def LiteraturePartialWord {n : ℕ} :
    List (Fin n) → (LiteratureSpace n → ℂ) → LiteratureSpace n → ℂ
  | [], f => f
  | i :: w, f => fun x =>
      fderiv ℝ (LiteraturePartialWord w f) x (LiteratureUnitVector i)

def LiteratureFourierWordMultiplier {n : ℕ} (w : List (Fin n))
    (k : LiteratureFrequency n) : ℂ :=
  (w.map (fun i => 2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ))).prod

/-- LI03. Smooth periodic Fourier inversion, derivative multipliers, absolute
coefficient summability, and uniform differentiated convergence. The native
Poisson/Leray identities and time-analytic estimates are not input fields. -/
structure LiteratureSmoothFourierInput : Prop where
  reconstruct : ∀ (n : ℕ), 0 < n → ∀ (f : LiteratureSpace n → ℂ),
    ContDiff ℝ ∞ f → LiteraturePeriodic f → ∀ w : List (Fin n),
      (∀ k : LiteratureFrequency n,
        LiteratureFourierCoefficient (LiteraturePartialWord w f) k =
          LiteratureFourierWordMultiplier w k * LiteratureFourierCoefficient f k) ∧
      Summable (fun k : LiteratureFrequency n =>
        ‖LiteratureFourierWordMultiplier w k * LiteratureFourierCoefficient f k‖) ∧
      HasSumUniformly
        (fun (k : LiteratureFrequency n) (x : LiteratureSpace n) =>
          (LiteratureFourierWordMultiplier w k * LiteratureFourierCoefficient f k) *
            LiteratureCharacter k x)
        (LiteraturePartialWord w f)

/-- Three explicit source signatures. This structure does not contain any
of the four project law packages, nor does its declaration inhabit it. -/
structure LiteratureInputs : Prop where
  ck : LiteratureAnalyticCKInput
  gaussianJet : LiteratureGaussianJetInput
  smoothFourier : LiteratureSmoothFourierInput

/-- Exact source field extraction. This does not discharge LI01. -/
theorem LiteratureInputs_ck (h : LiteratureInputs) : LiteratureAnalyticCKInput := h.ck

/-- Exact source field extraction. This does not discharge LI02. -/
theorem LiteratureInputs_gaussianJet (h : LiteratureInputs) :
    LiteratureGaussianJetInput := h.gaussianJet

/-- Exact source field extraction. This does not discharge LI03. -/
theorem LiteratureInputs_smoothFourier (h : LiteratureInputs) :
    LiteratureSmoothFourierInput := h.smoothFourier

end

end NSEGR
