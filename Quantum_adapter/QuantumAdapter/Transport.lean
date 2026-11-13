import QuantumAdapter.Born

/-!
Pointwise half-density transport algebra. The integral and MemLp transport
laws are explicit hypotheses, specialized to the actual Galerkin phase later.
Their definitions do not assert existence of any flow or unitary generator.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory

namespace QuantumAdapter

noncomputable section

def halfDensityPullback {E : Type*} (κ : ℝ) (Φ : ℝ → E → E)
    (t : ℝ) (ψ : Wave E) : Wave E :=
  fun q => (Real.exp (κ * t / 2) : ℂ) * ψ (Φ (-t) q)

theorem halfDensityPullback_zero {E : Type*} (κ : ℝ) (Φ : ℝ → E → E)
    (hzero : ∀ q, Φ 0 q = q) (ψ : Wave E) :
    halfDensityPullback κ Φ 0 ψ = ψ := by
  funext q
  simp [halfDensityPullback, hzero]

theorem halfDensityPullback_add {E : Type*} (κ : ℝ) (Φ : ℝ → E → E)
    (hadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (s t : ℝ) (ψ : Wave E) :
    halfDensityPullback κ Φ s (halfDensityPullback κ Φ t ψ) =
      halfDensityPullback κ Φ (s + t) ψ := by
  funext q
  have htime : -t + -s = -(s + t) := by ring
  have hcoef :
      (Real.exp (κ * s / 2) : ℂ) * (Real.exp (κ * t / 2) : ℂ) =
        (Real.exp (κ * (s + t) / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have he : κ * s / 2 + κ * t / 2 = κ * (s + t) / 2 := by ring
    rw [he]
  dsimp [halfDensityPullback]
  rw [← hadd (-t) (-s) q, htime, ← mul_assoc, hcoef]

theorem halfDensityPullback_inverse {E : Type*} (κ : ℝ) (Φ : ℝ → E → E)
    (hzero : ∀ q, Φ 0 q = q)
    (hadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (t : ℝ) (ψ : Wave E) :
    halfDensityPullback κ Φ (-t) (halfDensityPullback κ Φ t ψ) = ψ := by
  rw [halfDensityPullback_add κ Φ hadd, neg_add_cancel]
  exact halfDensityPullback_zero κ Φ hzero ψ

theorem bornDensity_halfDensityPullback {E : Type*}
    (κ : ℝ) (Φ : ℝ → E → E) (t : ℝ) (ψ : Wave E) (q : E) :
    bornDensity (halfDensityPullback κ Φ t ψ) q =
      Real.exp (κ * t) * bornDensity ψ (Φ (-t) q) := by
  have he : Real.exp (κ * t / 2) * Real.exp (κ * t / 2) =
      Real.exp (κ * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [bornDensity, halfDensityPullback, Complex.normSq_mul,
    Complex.normSq_ofReal, he]

/-- The exact real-integral change-of-variables identity. It is not inferred
from the pointwise group laws. -/
def IntegralPullbackLaw {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (κ : ℝ) (Φ : ℝ → E → E) : Prop :=
  ∀ (t : ℝ) (f : E → ℝ), Integrable f μ →
    (∫ q, Real.exp (κ * t) * f (Φ (-t) q) ∂μ) = ∫ q, f q ∂μ

/-- Preservation of actual L2 membership; a separate analytic law. -/
def MemLpPullbackLaw {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (κ : ℝ) (Φ : ℝ → E → E) : Prop :=
  ∀ (t : ℝ) (ψ : Wave E), MemLp ψ 2 μ →
    MemLp (halfDensityPullback κ Φ t ψ) 2 μ

theorem WaveAdmissible.halfDensityPullback {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {κ : ℝ} {Φ : ℝ → E → E}
    (hI : IntegralPullbackLaw μ κ Φ) (hLp : MemLpPullbackLaw μ κ Φ)
    {ψ : Wave E} (hψ : WaveAdmissible μ ψ) (t : ℝ) :
    WaveAdmissible μ (halfDensityPullback κ Φ t ψ) := by
  refine ⟨hLp t ψ hψ.memLp, ?_⟩
  calc
    (∫ q, bornDensity (halfDensityPullback κ Φ t ψ) q ∂μ) =
        ∫ q, Real.exp (κ * t) * bornDensity ψ (Φ (-t) q) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with q
      exact bornDensity_halfDensityPullback κ Φ t ψ q
    _ = ∫ q, bornDensity ψ q ∂μ := hI t (bornDensity ψ) hψ.density_integrable
    _ = 1 := hψ.normalized

theorem expectation_halfDensityPullback {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (κ : ℝ) (Φ : ℝ → E → E)
    (hzero : ∀ q, Φ 0 q = q)
    (hadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hI : IntegralPullbackLaw μ κ Φ) (t : ℝ) (f : E → ℝ) (ψ : Wave E)
    (hf : Integrable (fun q => f (Φ t q) * bornDensity ψ q) μ) :
    expectation μ f (halfDensityPullback κ Φ t ψ) =
      expectation μ (fun q => f (Φ t q)) ψ := by
  have hinv (q : E) : Φ t (Φ (-t) q) = q := by
    rw [← hadd t (-t) q, add_neg_cancel, hzero]
  unfold expectation
  calc
    (∫ q, f q * bornDensity (halfDensityPullback κ Φ t ψ) q ∂μ) =
        ∫ q, Real.exp (κ * t) *
          (f (Φ t (Φ (-t) q)) * bornDensity ψ (Φ (-t) q)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [bornDensity_halfDensityPullback, hinv]
      ring
    _ = ∫ q, f (Φ t q) * bornDensity ψ q ∂μ := hI t _ hf

end

end QuantumAdapter
