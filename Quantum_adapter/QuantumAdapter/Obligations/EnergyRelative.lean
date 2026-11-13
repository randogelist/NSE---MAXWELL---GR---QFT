import QuantumAdapter.Obligations.EnergyPhysical
import QuantumAdapter.Obligations.ScalarGrowth
import QuantumAdapter.Assembly.PacketEstimates

/-! The exact reference-gradient relative L2 estimate for actual native orbits. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

theorem phaseCoeff_drift_difference (ν : ℝ) (N : ℕ) (q r : Phase N)
    (k : Frequency) (hk : k ∈ fullModes N) (i : Fin 3) :
    phaseCoeff (drift ν N q - drift ν N r) k i =
      -((ν * laplaceSymbol k : ℝ) : ℂ) * phaseCoeff (q - r) k i -
        coefficientLeray k (fullTransport N (phaseCoeff q) k -
          fullTransport N (phaseCoeff r) k) i := by
  rw [phaseCoeff_sub, phaseCoeff_sub]
  simp only [Pi.sub_apply]
  change extendCoeff (drift ν N q).val k i - extendCoeff (drift ν N r).val k i = _
  rw [drift_eq_rawRhs, drift_eq_rawRhs, rawRhs_all_modes, rawRhs_all_modes,
    if_pos hk, if_pos hk, coefficientLeray_sub_native]
  simp only [Pi.sub_apply]
  ring

theorem relative_drift_inner_identity (ν : ℝ) (N : ℕ) (q r : Phase N) :
    inner ℝ (q - r) (drift ν N q - drift ν N r) =
      -ν * dissipation N (q - r) -
        (∫ x in unitCube, inner ℝ (synthesis (q - r) x)
          (mixedConvection (synthesis (q - r)) (synthesis r) x)) := by
  let c := phaseCoeff (q - r)
  let T : FourierCoeff := fullTransport N (phaseCoeff q) - fullTransport N (phaseCoeff r)
  have hc : SpectralSolenoidal c := phaseCoeff_solenoidal (q - r)
  have hpoint (k : Frequency) (hk : k ∈ fullModes N) (i : Fin 3) :
      (star (phaseCoeff (q - r) k i) *
        phaseCoeff (drift ν N q - drift ν N r) k i).re =
          (-ν) * (laplaceSymbol k * Complex.normSq (c k i)) -
            (star (c k i) * coefficientLeray k (T k) i).re := by
    rw [phaseCoeff_drift_difference ν N q r k hk i]
    change (star (c k i) * (-((ν * laplaceSymbol k : ℝ) : ℂ) * c k i -
      coefficientLeray k (T k) i)).re = _
    rw [complex_viscous_pairing]
    ring
  have hproj (k : Frequency) :
      (∑ i : Fin 3, (star (c k i) * coefficientLeray k (T k) i).re) =
        ∑ i : Fin 3, (star (c k i) * T k i).re := by
    simpa only [Complex.re_sum] using congrArg Complex.re
      (coefficientLeray_pairing k (c k) (T k) (hc k))
  have hzero : (∑ k ∈ fullModes N, ∑ i : Fin 3,
      (star (c k i) * fullBilinearTransport N (phaseCoeff q) c k i).re) = 0 := by
    simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re
      (fullBilinearTransport_energy_zero N (phaseCoeff q) c
        (phaseCoeff_support (q - r)) (phaseCoeff_reality (q - r))
        (phaseCoeff_solenoidal q))
  have hT : T = fullBilinearTransport N (phaseCoeff q) c +
      fullBilinearTransport N c (phaseCoeff r) := fullTransport_difference N q r
  have hnonlin : (∑ k ∈ fullModes N, ∑ i : Fin 3, (star (c k i) * T k i).re) =
      (∫ x in unitCube, inner ℝ (synthesis (q - r) x)
        (mixedConvection (synthesis (q - r)) (synthesis r) x)) := by
    rw [hT]
    simp only [Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib, hzero,
      zero_add]
    exact (integral_synthesis_mixedConvection N (q - r) (q - r) r).symm
  rw [phase_inner_eq_sum]
  calc
    _ = ∑ k ∈ fullModes N, ∑ i : Fin 3,
        ((-ν) * (laplaceSymbol k * Complex.normSq (c k i)) -
          (star (c k i) * coefficientLeray k (T k) i).re) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      exact hpoint k hk i
    _ = -ν * dissipation N (q - r) -
        ∑ k ∈ fullModes N, ∑ i : Fin 3, (star (c k i) * T k i).re := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hproj, dissipation, c]
    _ = _ := by rw [hnonlin]

theorem relative_drift_inner_le {ν : ℝ} (hν : 0 ≤ ν)
    (N : ℕ) (q r : Phase N) :
    inner ℝ (q - r) (drift ν N q - drift ν N r) ≤
      gradientObservable r * ‖q - r‖ ^ 2 := by
  rw [relative_drift_inner_identity]
  have hd : -ν * dissipation N (q - r) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hν) (dissipation_nonneg N (q - r))
  have hp := synthesis_relative_transport_integral N (q - r) r
  linarith

theorem phaseFlow_relative_energy_hasDerivAt {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q r : Phase N) (t : ℝ) :
    HasDerivAt (fun s => ‖F.map N s q - F.map N s r‖ ^ 2)
      (2 * inner ℝ (F.map N t q - F.map N t r)
        (drift ν N (F.map N t q) - drift ν N (F.map N t r))) t := by
  exact ((F.orbit_derivative N q t).sub (F.orbit_derivative N r t)).norm_sq

/-- P4, without any analytic premise: exact gradient cost and coefficient one. -/
theorem phaseFlow_relative_l2 {ν : ℝ} (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (N : ℕ) (q r : Phase N) (t : ℝ) (ht : 0 ≤ t) :
    ‖F.map N t q - F.map N t r‖ ≤
      ‖q - r‖ * Real.exp (Assembly.orbitGradientCost F N r t) := by
  let y : ℝ → ℝ := fun s => ‖F.map N s q - F.map N s r‖ ^ 2
  let dy : ℝ → ℝ := fun s => 2 * inner ℝ (F.map N s q - F.map N s r)
    (drift ν N (F.map N s q) - drift ν N (F.map N s r))
  let g : ℝ → ℝ := fun s => gradientObservable (F.map N s r)
  have hg : Continuous g := (Assembly.continuous_gradientObservable N).comp
    (Assembly.phaseFlow_orbit_continuous F N r)
  have hd (s : ℝ) : HasDerivAt y (dy s) s :=
    phaseFlow_relative_energy_hasDerivAt F N q r s
  have hb := sqrt_energy_growth_bound y dy g 1 hg hd
    (fun s hs => sq_nonneg _) (by
      intro s hs
      have hh := relative_drift_inner_le hν N (F.map N s q) (F.map N s r)
      change 2 * inner ℝ _ _ ≤ (2 * 1) * g s * y s
      dsimp [g, y]
      linarith) ht
  simpa only [y, g, F.map_zero, Real.sqrt_sq (norm_nonneg _), one_mul,
    Assembly.orbitGradientCost] using hb

end
end QuantumAdapter.Obligations
