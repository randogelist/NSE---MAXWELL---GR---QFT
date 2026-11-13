import QuantumAdapter.Obligations.EnergyCommutator
import QuantumAdapter.Obligations.TraceViscous
import QuantumAdapter.Obligations.ScalarGrowth
import QuantumAdapter.Assembly.PacketEstimates

/-! Exact native H3 growth, with no analytic certificate premise. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

theorem phaseDerivative_laplacian (N : ℕ) (i : Fin 3) (q : Phase N) :
    phaseDerivative N i (phaseLaplacian N q) =
      phaseLaplacian N (phaseDerivative N i q) := by
  apply Subtype.ext
  apply extendCoeff_injective N
  change phaseCoeff (phaseDerivative N i (phaseLaplacian N q)) =
    phaseCoeff (phaseLaplacian N (phaseDerivative N i q))
  funext k j
  simp only [phaseCoeff_phaseDerivative, phaseLaplacian_coeff, spectralMultiplier]
  ring

theorem inner_phaseLaplacian (N : ℕ) (q : Phase N) :
    inner ℝ q (phaseLaplacian N q) = dissipation N q := by
  rw [phase_inner_eq_sum]
  unfold dissipation
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [phaseLaplacian_coeff]
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.normSq_apply]
  ring

theorem orderedPairing_laplacian_nonneg (m N : ℕ) (q : Phase N) :
    0 ≤ orderedPairing m N q (phaseLaplacian N q) := by
  induction m generalizing q with
  | zero =>
    change 0 ≤ inner ℝ q (phaseLaplacian N q)
    rw [inner_phaseLaplacian]
    exact dissipation_nonneg N q
  | succ m ih =>
    simp only [orderedPairing, phaseDerivative_laplacian]
    exact Finset.sum_nonneg (fun i hi => ih _)

theorem h3Pairing_laplacian_nonneg (N : ℕ) (q : Phase N) :
    0 ≤ h3Pairing N q (phaseLaplacian N q) := by
  have h0 := orderedPairing_laplacian_nonneg 0 N q
  have h1 := orderedPairing_laplacian_nonneg 1 N q
  have h2 := orderedPairing_laplacian_nonneg 2 N q
  have h3 := orderedPairing_laplacian_nonneg 3 N q
  unfold h3Pairing
  positivity

theorem h3Pairing_add_right (N : ℕ) (q a b : Phase N) :
    h3Pairing N q (a + b) = h3Pairing N q a + h3Pairing N q b := by
  simp only [h3Pairing, orderedPairing_add_right]
  ring

theorem h3Pairing_smul_right (N : ℕ) (q a : Phase N) (s : ℝ) :
    h3Pairing N q (s • a) = s * h3Pairing N q a := by
  simp only [h3Pairing, orderedPairing_smul_right]
  ring

theorem h3Pairing_drift_le {ν : ℝ} (hν : 0 ≤ ν) (N : ℕ) (q : Phase N) :
    h3Pairing N q (drift ν N q) ≤ 512 * gradientObservable q * energy3 N q := by
  rw [drift_eq_inviscid_sub_laplacian, ← bilinearConvection_self,
    sub_eq_add_neg, ← neg_smul, h3Pairing_add_right, h3Pairing_smul_right]
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hν)
    (h3Pairing_laplacian_nonneg N q)
  have hbound := h3Pairing_convection_le N q
  linarith

theorem frequencyEnergy_hasDerivAt (m N : ℕ) {f : ℝ → Phase N}
    {f' : Phase N} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => frequencyEnergy m N (f s))
      (2 * orderedPairing m N (f t) f') t := by
  induction m generalizing f f' with
  | zero => simpa only [frequencyEnergy_zero, orderedPairing] using hf.norm_sq
  | succ m ih =>
    have hd (i : Fin 3) : HasDerivAt (fun s => phaseDerivative N i (f s))
        (phaseDerivative N i f') t := by
      simpa only [Function.comp_def, phaseDerivativeCLM_apply] using
        (phaseDerivativeCLM N i).hasFDerivAt.comp_hasDerivAt t hf
    have hs : HasDerivAt (fun s => ∑ i : Fin 3,
        frequencyEnergy m N (phaseDerivative N i (f s)))
      (∑ i : Fin 3, 2 * orderedPairing m N
        (phaseDerivative N i (f t)) (phaseDerivative N i f')) t := by
      apply HasDerivAt.fun_sum
      intro i hi
      exact ih (hd i)
    simpa only [frequencyEnergy_derivative_sum, orderedPairing, Finset.mul_sum] using hs

theorem energy3_hasDerivAt (N : ℕ) {f : ℝ → Phase N}
    {f' : Phase N} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => energy3 N (f s)) (2 * h3Pairing N (f t) f') t := by
  have h0 := frequencyEnergy_hasDerivAt 0 N hf
  have h1 := (frequencyEnergy_hasDerivAt 1 N hf).const_mul 3
  have h2 := (frequencyEnergy_hasDerivAt 2 N hf).const_mul 3
  have h3 := frequencyEnergy_hasDerivAt 3 N hf
  have h := ((h0.add h1).add h2).add h3
  have he : (fun s => frequencyEnergy 0 N (f s) + 3 * frequencyEnergy 1 N (f s) +
      3 * frequencyEnergy 2 N (f s) + frequencyEnergy 3 N (f s)) =
      (fun s => energy3 N (f s)) := by
    funext s
    exact (energy3_eq_frequencyEnergy N (f s)).symm
  rw [he] at h
  convert h using 1 <;> unfold h3Pairing <;> ring

theorem phaseFlow_energy3_hasDerivAt {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (t : ℝ) :
    HasDerivAt (fun s => energy3 N (F.map N s q))
      (2 * h3Pairing N (F.map N t q) (drift ν N (F.map N t q))) t :=
  energy3_hasDerivAt N (F.orbit_derivative N q t)

/-- P5: the exact native norm, prefactor one, and a uniform explicit constant. -/
theorem phaseFlow_h3_tame {ν : ℝ} (hν : 0 ≤ ν) (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (energy3 N (F.map N t q)) ≤ Real.sqrt (energy3 N q) *
      Real.exp (512 * Assembly.orbitGradientCost F N q t) := by
  let y : ℝ → ℝ := fun s => energy3 N (F.map N s q)
  let dy : ℝ → ℝ := fun s => 2 * h3Pairing N (F.map N s q) (drift ν N (F.map N s q))
  let g : ℝ → ℝ := fun s => gradientObservable (F.map N s q)
  have hg : Continuous g := (Assembly.continuous_gradientObservable N).comp
    (Assembly.phaseFlow_orbit_continuous F N q)
  have hd (s : ℝ) : HasDerivAt y (dy s) s := phaseFlow_energy3_hasDerivAt F N q s
  have hb := sqrt_energy_growth_bound y dy g 512 hg hd
    (fun s hs => energy3_nonneg N (F.map N s q)) (by
      intro s hs
      have hh := h3Pairing_drift_le hν N (F.map N s q)
      change 2 * h3Pairing N _ _ ≤ (2 * 512) * g s * y s
      dsimp [g, y]
      linarith) ht
  simpa only [y, g, F.map_zero, Assembly.orbitGradientCost] using hb

end
end QuantumAdapter.Obligations
