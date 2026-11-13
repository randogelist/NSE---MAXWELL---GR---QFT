import QuantumAdapter.Tangency
import SingularClosure.GalerkinEnergy

/-!
# Arbitrary-mean finite Galerkin energy

The native triad involution is reused on the full sign-symmetric set including
zero. Thus mean advection cancels in the actual energy pairing. These results
apply to the explicit phase drift and its actual ODE trajectories; no flow
existence or continuum estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators

namespace QuantumAdapter

noncomputable section

open SingularClosure

theorem fullTransport_complex_energy_zero
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ fullModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : ∀ k : Frequency, ∀ i : Fin 3, c (-k) i = star (c k i))
    (hsol : ∀ k : Frequency, (∑ i : Fin 3, (k i : ℂ) * c k i) = 0) :
    (∑ k ∈ fullModes N, ∑ i : Fin 3,
      star (c k i) * fullTransport N c k i) = 0 := by
  classical
  have hinner (p : Frequency) :
      (∑ k ∈ fullModes N, coefficientTriadPower c p k) = 0 := by
    let s := (fullModes N).filter (fun k => k - p ∈ fullModes N)
    have hfilter : (∑ k ∈ s, coefficientTriadPower c p k) =
        ∑ k ∈ fullModes N, coefficientTriadPower c p k := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hnot
      have hkp : k - p ∉ fullModes N := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hk, h⟩)
      simp [coefficientTriadPower, hsupp (k - p) hkp]
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
  simp only [fullTransport, Finset.mul_sum]
  simp_rw [hpoint]
  conv_lhs =>
    arg 2
    ext k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  change (∑ p ∈ fullModes N, ∑ k ∈ fullModes N,
    coefficientTriadPower c p k) = 0
  simp [hinner]

theorem fullLerayTransport_complex_energy_zero (N : ℕ) (q : Phase N) :
    (∑ k ∈ fullModes N, ∑ i : Fin 3,
      star (phaseCoeff q k i) *
        coefficientLeray k (fullTransport N (phaseCoeff q) k) i) = 0 := by
  calc
    _ = ∑ k ∈ fullModes N, ∑ i : Fin 3,
        star (phaseCoeff q k i) * fullTransport N (phaseCoeff q) k i := by
      apply Finset.sum_congr rfl
      intro k hk
      exact coefficientLeray_pairing k (phaseCoeff q k)
        (fullTransport N (phaseCoeff q) k) (phaseCoeff_solenoidal q k)
    _ = 0 := fullTransport_complex_energy_zero N (phaseCoeff q)
      (phaseCoeff_support q) (phaseCoeff_reality q) (phaseCoeff_solenoidal q)

theorem fullLerayTransport_real_energy_zero (N : ℕ) (q : Phase N) :
    (∑ k ∈ fullModes N, ∑ i : Fin 3,
      (star (phaseCoeff q k i) *
        coefficientLeray k (fullTransport N (phaseCoeff q) k) i).re) = 0 := by
  simpa only [Complex.re_sum, Complex.zero_re] using
    congrArg Complex.re (fullLerayTransport_complex_energy_zero N q)

def energy0 (N : ℕ) (q : Phase N) : ℝ :=
  ∑ k ∈ fullModes N, ∑ i : Fin 3, Complex.normSq (phaseCoeff q k i)

def dissipation (N : ℕ) (q : Phase N) : ℝ :=
  ∑ k ∈ fullModes N, ∑ i : Fin 3,
    laplaceSymbol k * Complex.normSq (phaseCoeff q k i)

theorem energy0_nonneg (N : ℕ) (q : Phase N) : 0 ≤ energy0 N q := by
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.normSq_eq_norm_sq]
  exact sq_nonneg _

theorem dissipation_nonneg (N : ℕ) (q : Phase N) : 0 ≤ dissipation N q := by
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg (laplaceSymbol_nonneg k) (sq_nonneg _)

/-- Exact unweighted energy rate of the actual full Fourier RHS. -/
theorem rawRhs_energy_rate (ν : ℝ) (N : ℕ) (q : Phase N) :
    (∑ k ∈ fullModes N, ∑ i : Fin 3,
      2 * (star (phaseCoeff q k i) * extendCoeff (rawRhs ν N q) k i).re) =
      (-2 * ν) * dissipation N q := by
  have hpoint (k : Frequency) (hk : k ∈ fullModes N) (i : Fin 3) :
      2 * (star (phaseCoeff q k i) * extendCoeff (rawRhs ν N q) k i).re =
        (-2 * ν) * (laplaceSymbol k * Complex.normSq (phaseCoeff q k i)) -
          2 * (star (phaseCoeff q k i) *
            coefficientLeray k (fullTransport N (phaseCoeff q) k) i).re := by
    rw [rawRhs_all_modes, if_pos hk, complex_viscous_pairing]
    ring
  calc
    _ = ∑ k ∈ fullModes N, ∑ i : Fin 3,
        ((-2 * ν) * (laplaceSymbol k * Complex.normSq (phaseCoeff q k i)) -
          2 * (star (phaseCoeff q k i) *
            coefficientLeray k (fullTransport N (phaseCoeff q) k) i).re) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint k hk i
    _ = (-2 * ν) * dissipation N q := by
      simp only [dissipation, Finset.sum_sub_distrib, ← Finset.mul_sum,
        fullLerayTransport_real_energy_zero, mul_zero, sub_zero]

theorem rawRhs_energy_rate_nonpos {ν : ℝ} (hν : 0 ≤ ν)
    (N : ℕ) (q : Phase N) :
    (∑ k ∈ fullModes N, ∑ i : Fin 3,
      2 * (star (phaseCoeff q k i) * extendCoeff (rawRhs ν N q) k i).re) ≤ 0 := by
  rw [rawRhs_energy_rate]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hν) (dissipation_nonneg N q)

/-- Actual coefficient evaluation as a real continuous linear map. -/
def phaseCoordinate (N : ℕ) (k : Frequency) (i : Fin 3) :
    Phase N →L[ℝ] ℂ :=
  if hk : k ∈ fullModes N then
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : PhaseIndex N => ℂ) (⟨k, hk⟩, i)).comp
      (phaseSubmodule N).subtypeL
  else 0

@[simp]
theorem phaseCoordinate_apply (N : ℕ) (k : Frequency) (i : Fin 3) (q : Phase N) :
    phaseCoordinate N k i q = phaseCoeff q k i := by
  by_cases hk : k ∈ fullModes N <;>
    simp [phaseCoordinate, phaseCoeff, extendCoeff, hk]

theorem IsTrajectory.coefficient_hasDerivWithinAt
    {ν : ℝ} {N : ℕ} {q₀ : Phase N} {q : ℝ → Phase N}
    (g : IsTrajectory ν N q₀ q) {t : ℝ} (ht : 0 ≤ t)
    (k : Frequency) (i : Fin 3) :
    HasDerivWithinAt (fun s => phaseCoeff (q s) k i)
      (phaseCoeff (drift ν N (q t)) k i) (Ici 0) t := by
  simpa only [Function.comp_def, phaseCoordinate_apply] using
    (phaseCoordinate N k i).hasFDerivAt.comp_hasDerivWithinAt t (g.equation t ht)

theorem IsTrajectory.energy0_identity
    {ν : ℝ} {N : ℕ} {q₀ : Phase N} {q : ℝ → Phase N}
    (g : IsTrajectory ν N q₀ q) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => energy0 N (q s))
      ((-2 * ν) * dissipation N (q t)) (Ici 0) t := by
  rw [← rawRhs_energy_rate ν N (q t)]
  unfold energy0
  apply HasDerivWithinAt.fun_sum
  intro k hk
  apply HasDerivWithinAt.fun_sum
  intro i hi
  simpa only [phaseCoeff, drift_eq_rawRhs] using
    hasDerivWithinAt_complex_normSq (g.coefficient_hasDerivWithinAt ht k i)

theorem IsTrajectory.energy0_antitoneOn
    {ν : ℝ} (hν : 0 ≤ ν) {N : ℕ} {q₀ : Phase N} {q : ℝ → Phase N}
    (g : IsTrajectory ν N q₀ q) :
    AntitoneOn (fun t => energy0 N (q t)) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (f' := fun t => (-2 * ν) * dissipation N (q t))
  · intro t ht
    exact (g.energy0_identity ht).continuousWithinAt
  · intro t ht
    exact (g.energy0_identity (interior_subset ht)).mono interior_subset
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hν) (dissipation_nonneg N (q t))

theorem IsTrajectory.energy0_le_initial
    {ν : ℝ} (hν : 0 ≤ ν) {N : ℕ} {q₀ : Phase N} {q : ℝ → Phase N}
    (g : IsTrajectory ν N q₀ q) {t : ℝ} (ht : 0 ≤ t) :
    energy0 N (q t) ≤ energy0 N q₀ := by
  have h := g.energy0_antitoneOn hν (by simp) ht ht
  rwa [g.initial] at h

end

end QuantumAdapter

