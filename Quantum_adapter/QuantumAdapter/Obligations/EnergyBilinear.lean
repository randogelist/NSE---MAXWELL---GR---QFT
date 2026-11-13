import QuantumAdapter.Assembly.Flow
import QuantumAdapter.Assembly.Fourier

/-! The actual full-mode convolution as a continuous real bilinear phase map. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

def fullBilinearTransport (N : ℕ) (a b : FourierCoeff) (k : Frequency)
    (i : Fin 3) : ℂ :=
  ∑ p ∈ fullModes N,
    (∑ j : Fin 3, a p j * derivativeSymbol j (k - p)) * b (k - p) i

theorem fullBilinearTransport_self (N : ℕ) (a : FourierCoeff) :
    fullBilinearTransport N a a = fullTransport N a := by
  funext k i
  simp only [fullBilinearTransport, fullTransport, derivativeSymbol, Pi.sub_apply]

theorem fullBilinearTransport_add_left (N : ℕ) (a b c : FourierCoeff) :
    fullBilinearTransport N (a + b) c =
      fullBilinearTransport N a c + fullBilinearTransport N b c := by
  funext k i
  simp only [fullBilinearTransport, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem fullBilinearTransport_add_right (N : ℕ) (a b c : FourierCoeff) :
    fullBilinearTransport N a (b + c) =
      fullBilinearTransport N a b + fullBilinearTransport N a c := by
  funext k i
  simp only [fullBilinearTransport, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem fullBilinearTransport_smul_left (N : ℕ) (s : ℝ) (a b : FourierCoeff) :
    fullBilinearTransport N (s • a) b = s • fullBilinearTransport N a b := by
  funext k i
  simp only [fullBilinearTransport, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum]

theorem fullBilinearTransport_smul_right (N : ℕ) (s : ℝ) (a b : FourierCoeff) :
    fullBilinearTransport N a (s • b) = s • fullBilinearTransport N a b := by
  funext k i
  simp only [fullBilinearTransport, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum]

theorem fullBilinearTransport_sub_left (N : ℕ) (a b c : FourierCoeff) :
    fullBilinearTransport N (a - b) c =
      fullBilinearTransport N a c - fullBilinearTransport N b c := by
  funext k i
  simp only [fullBilinearTransport, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem fullBilinearTransport_sub_right (N : ℕ) (a b c : FourierCoeff) :
    fullBilinearTransport N a (b - c) =
      fullBilinearTransport N a b - fullBilinearTransport N a c := by
  funext k i
  simp only [fullBilinearTransport, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem phaseCoeff_sub (N : ℕ) (q r : Phase N) :
    phaseCoeff (q - r) = phaseCoeff q - phaseCoeff r := by
  funext k i
  by_cases hk : k ∈ fullModes N <;> simp [phaseCoeff, extendCoeff, hk]

theorem fullTransport_difference (N : ℕ) (q r : Phase N) :
    fullTransport N (phaseCoeff q) - fullTransport N (phaseCoeff r) =
      fullBilinearTransport N (phaseCoeff q) (phaseCoeff (q - r)) +
        fullBilinearTransport N (phaseCoeff (q - r)) (phaseCoeff r) := by
  rw [phaseCoeff_sub, fullBilinearTransport_sub_right, fullBilinearTransport_sub_left,
    fullBilinearTransport_self, fullBilinearTransport_self]
  abel

theorem coefficientLeray_add_native (k : Frequency) (a b : Fin 3 → ℂ) :
    coefficientLeray k (a + b) = coefficientLeray k a + coefficientLeray k b := by
  classical
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, hk, if_false, Pi.add_apply, mul_add,
      Finset.sum_add_distrib, add_div]
    ring

theorem coefficientLeray_real_smul_native (k : Frequency) (s : ℝ) (a : Fin 3 → ℂ) :
    coefficientLeray k (s • a) = s • coefficientLeray k a := by
  classical
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, hk, if_false, Pi.smul_apply, Complex.real_smul]
    have hsum : (∑ j : Fin 3, (k j : ℂ) * ((s : ℂ) * a j)) =
        (s : ℂ) * ∑ j : Fin 3, (k j : ℂ) * a j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring

theorem coefficientLeray_sub_native (k : Frequency) (a b : Fin 3 → ℂ) :
    coefficientLeray k (a - b) = coefficientLeray k a - coefficientLeray k b := by
  classical
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, hk, if_false, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib, sub_div]
    ring

/-- Signed nonlinear ambient vector field; the zero mode is fixed. -/
def bilinearAmbient (N : ℕ) (q r : Phase N) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => if ki.1.val = 0 then 0 else
    -coefficientLeray ki.1.val
      (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) ki.1.val) ki.2)

theorem bilinearAmbient_add_left (N : ℕ) (q r s : Phase N) :
    bilinearAmbient N (q + r) s = bilinearAmbient N q s + bilinearAmbient N r s := by
  ext ki
  change (if ki.1.val = 0 then 0 else -coefficientLeray ki.1.val
      (fullBilinearTransport N (phaseCoeff (q + r)) (phaseCoeff s) ki.1.val) ki.2) =
    (if ki.1.val = 0 then 0 else -coefficientLeray ki.1.val
      (fullBilinearTransport N (phaseCoeff q) (phaseCoeff s) ki.1.val) ki.2) +
    (if ki.1.val = 0 then 0 else -coefficientLeray ki.1.val
      (fullBilinearTransport N (phaseCoeff r) (phaseCoeff s) ki.1.val) ki.2)
  simp only [Assembly.phaseCoeff_add, fullBilinearTransport_add_left, Pi.add_apply]
  by_cases hk : ki.1.val = 0
  · simp [hk]
  · simp only [hk, if_false, coefficientLeray_add_native, Pi.add_apply, neg_add_rev]
    ring

theorem bilinearAmbient_add_right (N : ℕ) (q r s : Phase N) :
    bilinearAmbient N q (r + s) = bilinearAmbient N q r + bilinearAmbient N q s := by
  ext ki
  change (if ki.1.val = 0 then 0 else -coefficientLeray ki.1.val
      (fullBilinearTransport N (phaseCoeff q) (phaseCoeff (r + s)) ki.1.val) ki.2) =
    (if ki.1.val = 0 then 0 else -coefficientLeray ki.1.val
      (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) ki.1.val) ki.2) +
    (if ki.1.val = 0 then 0 else -coefficientLeray ki.1.val
      (fullBilinearTransport N (phaseCoeff q) (phaseCoeff s) ki.1.val) ki.2)
  simp only [Assembly.phaseCoeff_add, fullBilinearTransport_add_right, Pi.add_apply]
  by_cases hk : ki.1.val = 0
  · simp [hk]
  · simp only [hk, if_false, coefficientLeray_add_native, Pi.add_apply, neg_add_rev]
    ring

theorem bilinearAmbient_smul_left (N : ℕ) (s : ℝ) (q r : Phase N) :
    bilinearAmbient N (s • q) r = s • bilinearAmbient N q r := by
  ext ki
  simp only [bilinearAmbient, Assembly.phaseCoeff_smul, fullBilinearTransport_smul_left,
    Pi.smul_apply]
  by_cases hk : ki.1.val = 0
  · simp [hk]
  · simp [hk, coefficientLeray_real_smul_native, smul_neg]

theorem bilinearAmbient_smul_right (N : ℕ) (s : ℝ) (q r : Phase N) :
    bilinearAmbient N q (s • r) = s • bilinearAmbient N q r := by
  ext ki
  simp only [bilinearAmbient, Assembly.phaseCoeff_smul, fullBilinearTransport_smul_right,
    Pi.smul_apply]
  by_cases hk : ki.1.val = 0
  · simp [hk]
  · simp [hk, coefficientLeray_real_smul_native, smul_neg]

/-- Actual projected signed convection. No tangency premise is introduced. -/
def bilinearConvection (N : ℕ) (q r : Phase N) : Phase N :=
  (phaseSubmodule N).orthogonalProjectionOnto (bilinearAmbient N q r)

theorem bilinearConvection_add_left (N : ℕ) (q r s : Phase N) :
    bilinearConvection N (q + r) s = bilinearConvection N q s + bilinearConvection N r s := by
  simp [bilinearConvection, bilinearAmbient_add_left]

theorem bilinearConvection_add_right (N : ℕ) (q r s : Phase N) :
    bilinearConvection N q (r + s) = bilinearConvection N q r + bilinearConvection N q s := by
  simp [bilinearConvection, bilinearAmbient_add_right]

theorem bilinearConvection_smul_left (N : ℕ) (s : ℝ) (q r : Phase N) :
    bilinearConvection N (s • q) r = s • bilinearConvection N q r := by
  simp [bilinearConvection, bilinearAmbient_smul_left]

theorem bilinearConvection_smul_right (N : ℕ) (s : ℝ) (q r : Phase N) :
    bilinearConvection N q (s • r) = s • bilinearConvection N q r := by
  simp [bilinearConvection, bilinearAmbient_smul_right]

def bilinearConvectionRight (N : ℕ) (q : Phase N) : Phase N →ₗ[ℝ] Phase N where
  toFun := bilinearConvection N q
  map_add' := bilinearConvection_add_right N q
  map_smul' := by intro s r; exact bilinearConvection_smul_right N s q r

def bilinearConvectionRightCLM (N : ℕ) (q : Phase N) : Phase N →L[ℝ] Phase N :=
  { toLinearMap := bilinearConvectionRight N q
    cont := (bilinearConvectionRight N q).continuous_of_finiteDimensional }

def bilinearConvectionLinear (N : ℕ) : Phase N →ₗ[ℝ] Phase N →L[ℝ] Phase N where
  toFun := bilinearConvectionRightCLM N
  map_add' := by
    intro q r
    apply ContinuousLinearMap.ext
    intro s
    exact bilinearConvection_add_left N q r s
  map_smul' := by
    intro a q
    apply ContinuousLinearMap.ext
    intro r
    exact bilinearConvection_smul_left N a q r

def bilinearConvectionCLM (N : ℕ) : Phase N →L[ℝ] Phase N →L[ℝ] Phase N :=
  { toLinearMap := bilinearConvectionLinear N
    cont := (bilinearConvectionLinear N).continuous_of_finiteDimensional }

@[simp] theorem bilinearConvectionCLM_apply (N : ℕ) (q r : Phase N) :
    bilinearConvectionCLM N q r = bilinearConvection N q r := rfl

theorem bilinearAmbient_self (N : ℕ) (q : Phase N) :
    bilinearAmbient N q q = rawRhs 0 N q := by
  ext ki
  simp [bilinearAmbient, fullBilinearTransport_self, rawRhs]

theorem bilinearConvection_self (N : ℕ) (q : Phase N) :
    bilinearConvection N q q = drift 0 N q := by
  simp only [bilinearConvection, bilinearAmbient_self, drift]

theorem complex_normSq_add_native (z w : ℂ) :
    Complex.normSq (z + w) = Complex.normSq z +
      2 * (star z * w).re + Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The real constrained phase pairing is exactly the full Fourier pairing. -/
theorem phase_inner_eq_sum (N : ℕ) (q r : Phase N) :
    inner ℝ q r = ∑ k ∈ fullModes N, ∑ i : Fin 3,
      (star (phaseCoeff q k i) * phaseCoeff r k i).re := by
  have h := norm_add_sq_real q r
  rw [← Assembly.energy0_eq_norm_sq N (q + r),
    ← Assembly.energy0_eq_norm_sq N q, ← Assembly.energy0_eq_norm_sq N r] at h
  have he : energy0 N (q + r) = energy0 N q +
      2 * (∑ k ∈ fullModes N, ∑ i : Fin 3,
        (star (phaseCoeff q k i) * phaseCoeff r k i).re) + energy0 N r := by
    simp only [energy0, Assembly.phaseCoeff_add, Pi.add_apply,
      complex_normSq_add_native, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [he] at h
  linarith

theorem inner_self_drift_zero (N : ℕ) (q : Phase N) :
    inner ℝ q (drift 0 N q) = 0 := by
  have h := rawRhs_energy_rate 0 N q
  simp only [mul_zero, zero_mul] at h
  simp only [← Finset.mul_sum] at h
  rw [phase_inner_eq_sum]
  simp only [phaseCoeff, drift_eq_rawRhs]
  simp only [phaseCoeff] at h
  linarith

theorem inner_mean_drift_zero (ν : ℝ) (N : ℕ) (m : Vec) (q : Phase N) :
    inner ℝ (meanPhase N m) (drift ν N q) = 0 := by
  rw [phase_inner_eq_sum]
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro i hi
  rw [meanPhase_coeff]
  by_cases hk0 : k = 0
  · subst k
    simp [drift_mean]
  · simp [hk0]

def mixedTriadPower (a b : FourierCoeff) (p k : Frequency) : ℂ :=
  ∑ i : Fin 3, star (b k i) *
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I * transportFrequencyPairing a p (k - p)) *
      b (k - p) i

theorem mixedTriadPower_swap (a b : FourierCoeff) (p k : Frequency)
    (hreal : SpectralReality b)
    (hsol : (∑ j : Fin 3, (p j : ℂ) * a p j) = 0) :
    mixedTriadPower a b p (p - k) = -mixedTriadPower a b p k := by
  have hsub : p - k - p = -k := by abel
  have hswap : p - k = -(k - p) := by abel
  have hpair : transportFrequencyPairing a p (k - p) =
      transportFrequencyPairing a p k := by
    rw [transportFrequencyPairing_sub, transportFrequencyPairing_self a p hsol,
      sub_zero]
  unfold mixedTriadPower
  rw [hsub, transportFrequencyPairing_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hswap, hreal, star_star, hreal, hpair]
  ring

/-- Transport by any solenoidal phase is skew for the transported phase. -/
theorem fullBilinearTransport_energy_zero (N : ℕ) (a b : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ fullModes N → ∀ i : Fin 3, b k i = 0)
    (hreal : SpectralReality b) (hsol : SpectralSolenoidal a) :
    (∑ k ∈ fullModes N, ∑ i : Fin 3,
      star (b k i) * fullBilinearTransport N a b k i) = 0 := by
  classical
  have hinner (p : Frequency) :
      (∑ k ∈ fullModes N, mixedTriadPower a b p k) = 0 := by
    let s := (fullModes N).filter (fun k => k - p ∈ fullModes N)
    have hfilter : (∑ k ∈ s, mixedTriadPower a b p k) =
        ∑ k ∈ fullModes N, mixedTriadPower a b p k := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hnot
      have hkp : k - p ∉ fullModes N := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hk, h⟩)
      simp [mixedTriadPower, hsupp (k - p) hkp]
    have hmem (k : Frequency) (hk : k ∈ s) : p - k ∈ s := by
      rcases Finset.mem_filter.mp hk with ⟨hk, hkp⟩
      apply Finset.mem_filter.mpr
      constructor
      · have heq : p - k = -(k - p) := by abel
        rw [heq]
        exact fullModes_neg_mem hkp
      · have heq : p - k - p = -k := by abel
        rw [heq]
        exact fullModes_neg_mem hk
    have hsum : (∑ k ∈ s, mixedTriadPower a b p k) =
        ∑ k ∈ s, -mixedTriadPower a b p k := by
      apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k) hmem hmem
      · intro k hk; abel
      · intro k hk; abel
      · intro k hk
        rw [mixedTriadPower_swap a b p k hreal (hsol p), neg_neg]
    rw [Finset.sum_neg_distrib] at hsum
    have hz : (∑ k ∈ s, mixedTriadPower a b p k) = 0 := by
      have hr := congrArg Complex.re hsum
      have hi := congrArg Complex.im hsum
      apply Complex.ext <;> simp only [Complex.neg_re, Complex.neg_im,
        Complex.zero_re, Complex.zero_im] at * <;> linarith
    rwa [hfilter] at hz
  have hpoint (p k : Frequency) (i : Fin 3) :
      star (b k i) *
          ((∑ j : Fin 3, a p j * derivativeSymbol j (k - p)) * b (k - p) i) =
        star (b k i) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          transportFrequencyPairing a p (k - p)) * b (k - p) i := by
    have hfreq : (∑ j : Fin 3, a p j * derivativeSymbol j (k - p)) =
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I * transportFrequencyPairing a p (k - p) := by
      unfold transportFrequencyPairing derivativeSymbol
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring
    rw [hfreq]
    ring
  simp only [fullBilinearTransport, Finset.mul_sum]
  simp_rw [hpoint]
  conv_lhs =>
    arg 2
    ext k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  change (∑ p ∈ fullModes N, ∑ k ∈ fullModes N, mixedTriadPower a b p k) = 0
  simp [hinner]

end
end QuantumAdapter.Obligations
