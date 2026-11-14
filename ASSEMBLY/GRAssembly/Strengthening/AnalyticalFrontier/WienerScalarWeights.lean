import GRAssembly.Strengthening.AnalyticalFrontier.WienerNumericalFoundation
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Scalar exponential-weight estimates used by the periodic Wiener/Gevrey
construction. These declarations contain no NSE premise.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

def analyticalWienerWeight (σ y : ℝ) : ℝ :=
  Real.exp (σ * y)

theorem analyticalWienerWeight_nonneg (σ y : ℝ) :
    0 ≤ analyticalWienerWeight σ y :=
  Real.exp_nonneg _

theorem analyticalWienerWeight_mono
    {σ τ y : ℝ} (hστ : σ ≤ τ) (hy : 0 ≤ y) :
    analyticalWienerWeight σ y ≤ analyticalWienerWeight τ y := by
  unfold analyticalWienerWeight
  exact Real.exp_monotone (mul_le_mul_of_nonneg_right hστ hy)

theorem analyticalWienerWeight_submultiplicative
    {σ y y₁ y₂ : ℝ} (hσ : 0 ≤ σ) (hy : y ≤ y₁ + y₂) :
    analyticalWienerWeight σ y ≤
      analyticalWienerWeight σ y₁ * analyticalWienerWeight σ y₂ := by
  unfold analyticalWienerWeight
  rw [← Real.exp_add]
  apply Real.exp_monotone
  calc
    σ * y ≤ σ * (y₁ + y₂) := mul_le_mul_of_nonneg_left hy hσ
    _ = σ * y₁ + σ * y₂ := by ring

theorem analyticalWiener_radiusLoss
    {δ y : ℝ} (hδ : 0 < δ) :
    y * Real.exp (-(δ * y)) ≤ Real.exp (-1) / δ := by
  apply (le_div_iff₀ hδ).2
  calc
    y * Real.exp (-(δ * y)) * δ =
        (δ * y) * Real.exp (-(δ * y)) := by ring
    _ ≤ Real.exp (-1) :=
      Real.mul_exp_neg_le_exp_neg_one (δ * y)

theorem analyticalWiener_momentFactorial
    (y : ℝ) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n ≤ (n.factorial : ℝ) * Real.exp y := by
  have h :=
    Real.pow_div_factorial_le_exp y hy n
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have h' : y ^ n ≤ Real.exp y * (n.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp h
  simpa [mul_comm] using h'

theorem analyticalWiener_scaledMomentFactorial
    {σ y : ℝ} (hσ : 0 < σ) (hy : 0 ≤ y) (n : ℕ) :
    y ^ n ≤
      (n.factorial : ℝ) * σ⁻¹ ^ n * Real.exp (σ * y) := by
  have h :=
    analyticalWiener_momentFactorial (σ * y)
      (mul_nonneg hσ.le hy) n
  have hpow : 0 ≤ σ⁻¹ ^ n := by positivity
  calc
    y ^ n = σ⁻¹ ^ n * (σ * y) ^ n := by
      symm
      rw [← mul_pow]
      simp [mul_assoc, hσ.ne']
    _ ≤ σ⁻¹ ^ n *
        ((n.factorial : ℝ) * Real.exp (σ * y)) :=
      mul_le_mul_of_nonneg_left h hpow
    _ = (n.factorial : ℝ) * σ⁻¹ ^ n *
        Real.exp (σ * y) := by ring

def ANALYTICAL_WIENER_SCALAR_WEIGHT_CHECKPOINT : Prop :=
  (∀ {σ τ y : ℝ}, σ ≤ τ → 0 ≤ y →
    analyticalWienerWeight σ y ≤ analyticalWienerWeight τ y) ∧
  (∀ {σ y y₁ y₂ : ℝ}, 0 ≤ σ → y ≤ y₁ + y₂ →
    analyticalWienerWeight σ y ≤
      analyticalWienerWeight σ y₁ * analyticalWienerWeight σ y₂) ∧
  (∀ {δ y : ℝ}, 0 < δ →
    y * Real.exp (-(δ * y)) ≤ Real.exp (-1) / δ) ∧
  (∀ (y : ℝ), 0 ≤ y → ∀ n : ℕ,
    y ^ n ≤ (n.factorial : ℝ) * Real.exp y)

theorem ANALYTICAL_WIENER_SCALAR_WEIGHT_CHECKPOINT_NATIVE :
    ANALYTICAL_WIENER_SCALAR_WEIGHT_CHECKPOINT := by
  exact ⟨
    fun hστ hy => analyticalWienerWeight_mono hστ hy,
    fun hσ hy => analyticalWienerWeight_submultiplicative hσ hy,
    fun hδ => analyticalWiener_radiusLoss hδ,
    fun y hy n => analyticalWiener_momentFactorial y hy n⟩

end
end NSEGR.Strengthening
