import SingularClosure.GalerkinAlgebra

/-!
# Exact nonlinear cancellation in the concrete Galerkin energy

The nonlinear cancellation is proved by the finite triad involution
`(p,k) ↦ (p,p-k)`. It uses only the concrete support, reality, and solenoidality
conditions of `GalerkinSolution`. No cancellation premise is introduced.
Physical Parseval identification and the uniform enstrophy estimate are separate.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem mem_cutoffModes_iff (N : ℕ) (k : Frequency) :
    k ∈ cutoffModes N ↔
      (∀ i : Fin 3, -(N : ℤ) ≤ k i ∧ k i ≤ (N : ℤ)) ∧
      k ≠ 0 ∧ galerkinFreqSq k ≤ (N : ℤ) ^ 2 := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_filter.mp hk with ⟨himage, hne, hsq⟩
    rcases Finset.mem_image.mp himage with ⟨q, hq, rfl⟩
    rcases Finset.mem_product.mp hq with ⟨hq12, hq3⟩
    rcases Finset.mem_product.mp hq12 with ⟨hq1, hq2⟩
    refine ⟨?_, hne, hsq⟩
    intro i
    fin_cases i
    · exact Finset.mem_Icc.mp hq1
    · exact Finset.mem_Icc.mp hq2
    · exact Finset.mem_Icc.mp hq3
  · rintro ⟨hcoord, hne, hsq⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hne, hsq⟩
    apply Finset.mem_image.mpr
    refine ⟨((k 0, k 1), k 2), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr (hcoord 0), Finset.mem_Icc.mpr (hcoord 1)⟩,
          Finset.mem_Icc.mpr (hcoord 2)⟩
    · ext i
      fin_cases i <;> rfl

theorem cutoffModes_neg_mem {N : ℕ} {k : Frequency}
    (hk : k ∈ cutoffModes N) : -k ∈ cutoffModes N := by
  rcases (mem_cutoffModes_iff N k).mp hk with ⟨hcoord, hne, hsq⟩
  apply (mem_cutoffModes_iff N (-k)).mpr
  refine ⟨?_, neg_ne_zero.mpr hne, ?_⟩
  · intro i
    have hi := hcoord i
    change -(N : ℤ) ≤ -(k i) ∧ -(k i) ≤ (N : ℤ)
    omega
  · simpa [galerkinFreqSq] using hsq

/-- Complex frequency pairing without the common derivative multiplier. -/
def transportFrequencyPairing (c : FourierCoeff) (p q : Frequency) : ℂ :=
  ∑ j : Fin 3, c p j * (q j : ℂ)

theorem transportFrequencyPairing_sub (c : FourierCoeff) (p q r : Frequency) :
    transportFrequencyPairing c p (q - r) =
      transportFrequencyPairing c p q - transportFrequencyPairing c p r := by
  simp [transportFrequencyPairing, mul_sub, Finset.sum_sub_distrib]

theorem transportFrequencyPairing_neg (c : FourierCoeff) (p q : Frequency) :
    transportFrequencyPairing c p (-q) = -transportFrequencyPairing c p q := by
  simp [transportFrequencyPairing]

theorem transportFrequencyPairing_self (c : FourierCoeff) (p : Frequency)
    (hsol : (∑ j : Fin 3, (p j : ℂ) * c p j) = 0) :
    transportFrequencyPairing c p p = 0 := by
  simpa [transportFrequencyPairing, mul_comm] using hsol

/-- The full complex contribution of one energy triad. -/
def coefficientTriadPower (c : FourierCoeff) (p k : Frequency) : ℂ :=
  ∑ i : Fin 3,
    star (c k i) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      transportFrequencyPairing c p (k - p)) * c (k - p) i

theorem coefficientTriadPower_eq_zero_of_not_mem
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (p k : Frequency) (hk : k - p ∉ cutoffModes N) :
    coefficientTriadPower c p k = 0 := by
  simp [coefficientTriadPower, hsupp (k - p) hk]

/-- Pairing triads exchanged by `k ↦ p-k` cancel before taking real parts. -/
theorem coefficientTriadPower_swap (c : FourierCoeff) (p k : Frequency)
    (hreal : ∀ q : Frequency, ∀ i : Fin 3, c (-q) i = star (c q i))
    (hsol : (∑ j : Fin 3, (p j : ℂ) * c p j) = 0) :
    coefficientTriadPower c p (p - k) = -coefficientTriadPower c p k := by
  have hsub : p - k - p = -k := by abel
  have hswap : p - k = -(k - p) := by abel
  have hpair : transportFrequencyPairing c p (k - p) =
      transportFrequencyPairing c p k := by
    rw [transportFrequencyPairing_sub, transportFrequencyPairing_self c p hsol,
      sub_zero]
  unfold coefficientTriadPower
  rw [hsub, transportFrequencyPairing_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hswap, hreal, star_star, hreal, hpair]
  ring

/-- The complete finite convolution has zero complex energy pairing. -/
theorem coefficientTransport_complex_energy_zero
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : ∀ k : Frequency, ∀ i : Fin 3, c (-k) i = star (c k i))
    (hsol : ∀ k : Frequency, (∑ i : Fin 3, (k i : ℂ) * c k i) = 0) :
    (∑ k ∈ cutoffModes N, ∑ i : Fin 3,
      star (c k i) * coefficientTransport N c k i) = 0 := by
  classical
  have hinner (p : Frequency) :
      (∑ k ∈ cutoffModes N, coefficientTriadPower c p k) = 0 := by
    let s := (cutoffModes N).filter (fun k => k - p ∈ cutoffModes N)
    have hfilter : (∑ k ∈ s, coefficientTriadPower c p k) =
        ∑ k ∈ cutoffModes N, coefficientTriadPower c p k := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hnot
      apply coefficientTriadPower_eq_zero_of_not_mem N c hsupp p k
      intro hkp
      exact hnot (Finset.mem_filter.mpr ⟨hk, hkp⟩)
    have hmem (k : Frequency) (hk : k ∈ s) : p - k ∈ s := by
      rcases Finset.mem_filter.mp hk with ⟨hk, hkp⟩
      apply Finset.mem_filter.mpr
      constructor
      · have heq : p - k = -(k - p) := by abel
        rw [heq]
        exact cutoffModes_neg_mem hkp
      · have heq : p - k - p = -k := by abel
        rw [heq]
        exact cutoffModes_neg_mem hk
    have hsum : (∑ k ∈ s, coefficientTriadPower c p k) =
        ∑ k ∈ s, -coefficientTriadPower c p k := by
      apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
        hmem hmem
      · intro k hk
        abel
      · intro k hk
        abel
      · intro k hk
        rw [coefficientTriadPower_swap c p k hreal (hsol p), neg_neg]
    rw [Finset.sum_neg_distrib] at hsum
    have hz : (∑ k ∈ s, coefficientTriadPower c p k) = 0 := by
      have hr := congrArg Complex.re hsum
      have hi := congrArg Complex.im hsum
      apply Complex.ext <;> simp only [Complex.neg_re, Complex.neg_im,
        Complex.zero_re, Complex.zero_im] at * <;> linarith
    rwa [hfilter] at hz
  have hpoint (p k : Frequency) (i : Fin 3) :
      star (c k i) *
          ((∑ j : Fin 3, c p j *
            (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) *
            c (k - p) i) =
        star (c k i) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          transportFrequencyPairing c p (k - p)) * c (k - p) i := by
    have hfreq : (∑ j : Fin 3, c p j *
        (((2 * Real.pi * ((k j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) =
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
          transportFrequencyPairing c p (k - p) := by
      unfold transportFrequencyPairing
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Pi.sub_apply]
      push_cast
      ring
    rw [hfreq]
    ring
  simp only [coefficientTransport, Finset.mul_sum]
  simp_rw [hpoint]
  conv_lhs =>
    arg 2
    ext k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  change (∑ p ∈ cutoffModes N, ∑ k ∈ cutoffModes N,
    coefficientTriadPower c p k) = 0
  simp [hinner]

/-- Actual Leray-projected nonlinear energy cancellation. -/
theorem coefficientNonlinearPower_eq_zero
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : ∀ k : Frequency, ∀ i : Fin 3, c (-k) i = star (c k i))
    (hsol : ∀ k : Frequency, (∑ i : Fin 3, (k i : ℂ) * c k i) = 0) :
    coefficientNonlinearPower N c = 0 := by
  have h := congrArg Complex.re
    (coefficientTransport_complex_energy_zero N c hsupp hreal hsol)
  unfold coefficientNonlinearPower
  simp only [Complex.re_sum, Complex.zero_re] at h
  calc
    _ = ∑ k ∈ cutoffModes N,
        (∑ i : Fin 3, star (c k i) *
          coefficientLeray k (coefficientTransport N c k) i).re := by
            simp only [Complex.re_sum]
    _ = ∑ k ∈ cutoffModes N,
        (∑ i : Fin 3, star (c k i) * coefficientTransport N c k i).re := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [coefficientLeray_pairing k (c k) (coefficientTransport N c k) (hsol k)]
    _ = 0 := by simpa only [Complex.re_sum] using h

/-- Exact finite-dimensional energy identity, with no nonlinear remainder. -/
theorem GalerkinSolution.coefficientEnergy_identity
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => coefficientEnergy N (g.coeff r))
      ((-2 * ν) * coefficientDissipation N (g.coeff t)) (Ici 0) t := by
  have hzero := coefficientNonlinearPower_eq_zero N (g.coeff t)
    (g.mode_support t ht) (g.real_symmetry t ht) (g.solenoidal t ht)
  simpa only [hzero, mul_zero, sub_zero] using
    g.coefficientEnergy_balance_with_remainder ht

/-- Coefficient dissipation is nonnegative for every finite state. -/
theorem coefficientDissipation_nonneg (N : ℕ) (c : FourierCoeff) :
    0 ≤ coefficientDissipation N c := by
  unfold coefficientDissipation
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro i hi
  have hfreqZ : (0 : ℤ) ≤ galerkinFreqSq k := by
    unfold galerkinFreqSq
    exact Finset.sum_nonneg (fun j hj => sq_nonneg (k j))
  have hfreq : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by exact_mod_cast hfreqZ
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) hfreq) (sq_nonneg _)

/-- Actual Galerkin coefficient energy is nonincreasing at forward times. -/
theorem GalerkinSolution.coefficientEnergy_antitoneOn
    {ν : ℝ} (hν : 0 ≤ ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) :
    AntitoneOn (fun t => coefficientEnergy N (g.coeff t)) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (f' := fun t => (-2 * ν) * coefficientDissipation N (g.coeff t))
  · intro t ht
    exact (g.coefficientEnergy_identity ht).continuousWithinAt
  · intro t ht
    exact (g.coefficientEnergy_identity (interior_subset ht)).mono interior_subset
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hν)
      (coefficientDissipation_nonneg N (g.coeff t))

/-- Uniform finite-dimensional coefficient energy bound. -/
theorem GalerkinSolution.coefficientEnergy_le_initial
    {ν : ℝ} (hν : 0 ≤ ν) {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) {t : ℝ} (ht : 0 ≤ t) :
    coefficientEnergy N (g.coeff t) ≤ coefficientEnergy N (g.coeff 0) := by
  exact g.coefficientEnergy_antitoneOn hν (by simp) ht ht

end

end SingularClosure
