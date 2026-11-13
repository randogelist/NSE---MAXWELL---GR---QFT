import Mathlib

/-!
Actual complex wave functions, Born densities and real multiplier expectations.
Integrability and normalization are explicit; no totalized integral is used as
evidence for an observable domain. This module makes no generator-existence or
selfadjointness assertion.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory

namespace QuantumAdapter

noncomputable section

abbrev Wave (E : Type*) := E → ℂ

def bornDensity {E : Type*} (ψ : Wave E) (q : E) : ℝ :=
  Complex.normSq (ψ q)

def expectation {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (ψ : Wave E) : ℝ :=
  ∫ q, f q * bornDensity ψ q ∂μ

/-- Square integrability and actual Born normalization. -/
structure WaveAdmissible {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (ψ : Wave E) : Prop where
  memLp : MemLp ψ 2 μ
  normalized : (∫ q, bornDensity ψ q ∂μ) = 1

/-- The actual multiplication-expectation integrand is Bochner integrable. -/
def ObservableIntegrable {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (ψ : Wave E) : Prop :=
  Integrable (fun q => f q * bornDensity ψ q) μ

/-- Domain of the actual unbounded multiplication operator, stronger than
mere integrability of its scalar quadratic form. -/
structure MultiplierDomain {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (ψ : Wave E) : Prop where
  state_memLp : MemLp ψ 2 μ
  product_memLp : MemLp (fun q => (f q : ℂ) * ψ q) 2 μ

theorem bornDensity_nonneg {E : Type*} (ψ : Wave E) (q : E) :
    0 ≤ bornDensity ψ q :=
  Complex.normSq_nonneg (ψ q)

@[simp]
theorem bornDensity_zero {E : Type*} (q : E) :
    bornDensity (fun _ : E => (0 : ℂ)) q = 0 := by
  simp [bornDensity]

theorem bornDensity_const_mul {E : Type*} (c : ℂ) (ψ : Wave E) (q : E) :
    bornDensity (fun x => c * ψ x) q =
      Complex.normSq c * bornDensity ψ q := by
  exact Complex.normSq_mul c (ψ q)

theorem bornDensity_unit_phase {E : Type*} (c : ℂ) (hc : Complex.normSq c = 1)
    (ψ : Wave E) (q : E) :
    bornDensity (fun x => c * ψ x) q = bornDensity ψ q := by
  rw [bornDensity_const_mul, hc, one_mul]

theorem WaveAdmissible.density_integrable {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : WaveAdmissible μ ψ) :
    Integrable (bornDensity ψ) μ := by
  by_contra hi
  have hn := hψ.normalized
  rw [integral_undef hi] at hn
  norm_num at hn

theorem not_waveAdmissible_zero {E : Type*} [MeasurableSpace E]
    (μ : Measure E) : ¬ WaveAdmissible μ (fun _ : E => (0 : ℂ)) := by
  intro h
  have hn := h.normalized
  simp [bornDensity] at hn

/-- The native L2 equivalence class, formed only after MemLp is established. -/
def WaveAdmissible.toL2 {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : WaveAdmissible μ ψ) : Lp ℂ 2 μ :=
  hψ.memLp.toLp ψ

theorem WaveAdmissible.coe_toL2 {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : WaveAdmissible μ ψ) :
    (hψ.toL2 : E → ℂ) =ᵐ[μ] ψ :=
  hψ.memLp.coeFn_toLp

theorem expectation_congr_ae {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) {ψ χ : Wave E}
    (h : ψ =ᵐ[μ] χ) : expectation μ f ψ = expectation μ f χ := by
  unfold expectation
  apply integral_congr_ae
  filter_upwards [h] with q hq
  simp only [bornDensity, hq]

theorem WaveAdmissible.expectation_toL2 {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : WaveAdmissible μ ψ) (f : E → ℝ) :
    expectation μ f (hψ.toL2 : E → ℂ) = expectation μ f ψ :=
  expectation_congr_ae μ f hψ.coe_toL2

theorem expectation_nonneg {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (ψ : Wave E)
    (hf : ∀ q, 0 ≤ f q) : 0 ≤ expectation μ f ψ := by
  unfold expectation
  exact integral_nonneg (fun q => mul_nonneg (hf q) (bornDensity_nonneg ψ q))

theorem expectation_const_mul_wave {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (c : ℂ) (ψ : Wave E) :
    expectation μ f (fun q => c * ψ q) =
      Complex.normSq c * expectation μ f ψ := by
  unfold expectation
  calc
    (∫ q, f q * bornDensity (fun x => c * ψ x) q ∂μ) =
        ∫ q, Complex.normSq c * (f q * bornDensity ψ q) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [bornDensity_const_mul]
      ring
    _ = Complex.normSq c * ∫ q, f q * bornDensity ψ q ∂μ :=
      integral_const_mul _ _

theorem expectation_unit_phase {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (c : ℂ) (hc : Complex.normSq c = 1)
    (ψ : Wave E) : expectation μ f (fun q => c * ψ q) = expectation μ f ψ := by
  rw [expectation_const_mul_wave, hc, one_mul]

theorem expectation_const {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : WaveAdmissible μ ψ) (c : ℝ) :
    expectation μ (fun _ => c) ψ = c := by
  unfold expectation
  rw [integral_const_mul, hψ.normalized, mul_one]

theorem expectation_mono {E : Type*} [MeasurableSpace E]
    (μ : Measure E) {f g : E → ℝ} (ψ : Wave E)
    (hf : ObservableIntegrable μ f ψ) (hg : ObservableIntegrable μ g ψ)
    (hfg : ∀ q, f q ≤ g q) : expectation μ f ψ ≤ expectation μ g ψ := by
  exact integral_mono hf hg
    (fun q => mul_le_mul_of_nonneg_right (hfg q) (bornDensity_nonneg ψ q))

theorem expectation_add {E : Type*} [MeasurableSpace E]
    (μ : Measure E) {f g : E → ℝ} (ψ : Wave E)
    (hf : ObservableIntegrable μ f ψ) (hg : ObservableIntegrable μ g ψ) :
    expectation μ (fun q => f q + g q) ψ =
      expectation μ f ψ + expectation μ g ψ := by
  simp only [expectation, add_mul]
  exact integral_add hf hg

theorem expectation_le_bound {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : WaveAdmissible μ ψ)
    {f : E → ℝ} (hf : ObservableIntegrable μ f ψ)
    {C : ℝ} (hC : ∀ q, f q ≤ C) : expectation μ f ψ ≤ C := by
  have hconst : ObservableIntegrable μ (fun _ : E => C) ψ :=
    hψ.density_integrable.const_mul C
  calc
    expectation μ f ψ ≤ expectation μ (fun _ : E => C) ψ :=
      expectation_mono μ ψ hf hconst hC
    _ = C := expectation_const hψ C

theorem bound_le_expectation {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {ψ : Wave E} (hψ : WaveAdmissible μ ψ)
    {f : E → ℝ} (hf : ObservableIntegrable μ f ψ)
    {C : ℝ} (hC : ∀ q, C ≤ f q) : C ≤ expectation μ f ψ := by
  have hconst : ObservableIntegrable μ (fun _ : E => C) ψ :=
    hψ.density_integrable.const_mul C
  calc
    C = expectation μ (fun _ : E => C) ψ := (expectation_const hψ C).symm
    _ ≤ expectation μ f ψ := expectation_mono μ ψ hconst hf hC

end

end QuantumAdapter
