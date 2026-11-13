import QuantumAdapter.Obligations.EnergyDerivatives

/-! Exact ordered H3 polarization and differentiation, independent of analytic bounds. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

def orderedPairing : ℕ → (N : ℕ) → Phase N → Phase N → ℝ
  | 0, _, q, r => inner ℝ q r
  | m + 1, N, q, r => ∑ i : Fin 3,
      orderedPairing m N (phaseDerivative N i q) (phaseDerivative N i r)

def h3Pairing (N : ℕ) (q r : Phase N) : ℝ :=
  orderedPairing 0 N q r + 3 * orderedPairing 1 N q r +
    3 * orderedPairing 2 N q r + orderedPairing 3 N q r

theorem orderedPairing_self (m N : ℕ) (q : Phase N) :
    orderedPairing m N q q = frequencyEnergy m N q := by
  induction m generalizing q with
  | zero => simp only [orderedPairing, real_inner_self_eq_norm_sq, frequencyEnergy_zero]
  | succ m ih =>
    simp_rw [orderedPairing, ih]
    exact frequencyEnergy_derivative_sum m N q

theorem orderedPairing_add_right (m N : ℕ) (q a b : Phase N) :
    orderedPairing m N q (a + b) =
      orderedPairing m N q a + orderedPairing m N q b := by
  induction m generalizing q a b with
  | zero => exact inner_add_right _ _ _
  | succ m ih => simp only [orderedPairing, phaseDerivative_add, ih, Finset.sum_add_distrib]

theorem orderedPairing_smul_right (m N : ℕ) (q a : Phase N) (s : ℝ) :
    orderedPairing m N q (s • a) = s * orderedPairing m N q a := by
  induction m generalizing q a with
  | zero => exact inner_smul_right _ _ _
  | succ m ih => simp only [orderedPairing, phaseDerivative_smul, ih, Finset.mul_sum]

theorem h3Pairing_self (N : ℕ) (q : Phase N) :
    h3Pairing N q q = energy3 N q := by
  simp only [h3Pairing, orderedPairing_self, energy3_eq_frequencyEnergy]

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

end
end QuantumAdapter.Obligations
