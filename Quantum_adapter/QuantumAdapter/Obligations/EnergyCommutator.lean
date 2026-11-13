import QuantumAdapter.Obligations.EnergyCoarse

/-! Finite ordered commutator assembly for the native H3 energy. -/
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

theorem first_commutator_bound (N : ℕ) (q : Phase N) (i : Fin 3) :
    inner ℝ (phaseDerivative N i q)
      (phaseDerivative N i (bilinearConvection N q q)) ≤
        gradientObservable q * ‖phaseDerivative N i q‖^2 := by
  rw [phaseDerivative_bilinearConvection, inner_add_right,
    inner_bilinearConvection_self_zero, add_zero]
  exact inner_bilinearConvection_relative_le N _ q

theorem second_commutator_bound (N : ℕ) (q : Phase N) (i j : Fin 3) :
    inner ℝ (phaseDerivative N j (phaseDerivative N i q))
      (phaseDerivative N j (phaseDerivative N i (bilinearConvection N q q))) ≤
        3 * gradientObservable q * frequencyEnergy 2 N q := by
  have h0 := inner_bilinearConvection_relative_le N
    (phaseDerivative N j (phaseDerivative N i q)) q
  have hnorm := mul_le_mul_of_nonneg_left (norm_second_phase_sq_le N q i j)
    (Assembly.gradientObservable_nonneg N q)
  have h1 := second_first_first_bound N q i j i j
  have h2 := second_first_first_bound N q i j j i
  simp only [phaseDerivative_bilinearConvection, phaseDerivative_add, inner_add_right,
    inner_bilinearConvection_self_zero, add_zero]
  linarith

theorem third_commutator_bound (N : ℕ) (q : Phase N) (i j k : Fin 3) :
    inner ℝ (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q)))
      (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i
        (bilinearConvection N q q)))) ≤
          16 * gradientObservable q * frequencyEnergy 3 N q := by
  have h0 := inner_bilinearConvection_relative_le N
    (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q))) q
  have hnorm := mul_le_mul_of_nonneg_left (norm_third_phase_sq_le N q i j k)
    (Assembly.gradientObservable_nonneg N q)
  have h1 := third_second_first_bound N q i j k i j k
  have h2 := third_second_first_bound N q i j k i k j
  have h3 := third_first_second_bound N q i j k i j k
  have h4 := third_second_first_bound N q i j k j k i
  have h5 := third_first_second_bound N q i j k j i k
  have h6 := third_first_second_bound N q i j k k i j
  simp only [phaseDerivative_bilinearConvection, phaseDerivative_add, inner_add_right,
    inner_bilinearConvection_self_zero, add_zero]
  linarith

theorem orderedPairing_one_convection_le (N : ℕ) (q : Phase N) :
    orderedPairing 1 N q (bilinearConvection N q q) ≤
      gradientObservable q * frequencyEnergy 1 N q := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i hi => first_commutator_bound N q i)
  simpa only [orderedPairing, ← Finset.mul_sum, ← frequencyEnergy_zero,
    frequencyEnergy_derivative_sum] using h

theorem orderedPairing_two_convection_le (N : ℕ) (q : Phase N) :
    orderedPairing 2 N q (bilinearConvection N q q) ≤
      27 * gradientObservable q * frequencyEnergy 2 N q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i hi =>
    Finset.sum_le_sum (s := Finset.univ) (fun j hj => second_commutator_bound N q i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  simpa only [orderedPairing] using (show
    (∑ i : Fin 3, ∑ j : Fin 3, inner ℝ (phaseDerivative N j (phaseDerivative N i q))
      (phaseDerivative N j (phaseDerivative N i (bilinearConvection N q q)))) ≤
        27 * gradientObservable q * frequencyEnergy 2 N q by nlinarith [h])

theorem orderedPairing_three_convection_le (N : ℕ) (q : Phase N) :
    orderedPairing 3 N q (bilinearConvection N q q) ≤
      432 * gradientObservable q * frequencyEnergy 3 N q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i hi =>
    Finset.sum_le_sum (s := Finset.univ) (fun j hj =>
      Finset.sum_le_sum (s := Finset.univ) (fun k hk => third_commutator_bound N q i j k)))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  simp only [orderedPairing]
  nlinarith [h]

/-- A concrete cutoff-independent constant for the exact native H3 pairing. -/
theorem h3Pairing_convection_le (N : ℕ) (q : Phase N) :
    h3Pairing N q (bilinearConvection N q q) ≤
      512 * gradientObservable q * energy3 N q := by
  have h1 := orderedPairing_one_convection_le N q
  have h2 := orderedPairing_two_convection_le N q
  have h3 := orderedPairing_three_convection_le N q
  have hg := Assembly.gradientObservable_nonneg N q
  have h0n := mul_nonneg hg (frequencyEnergy_nonneg 0 N q)
  have h1n := mul_nonneg hg (frequencyEnergy_nonneg 1 N q)
  have h2n := mul_nonneg hg (frequencyEnergy_nonneg 2 N q)
  have h3n := mul_nonneg hg (frequencyEnergy_nonneg 3 N q)
  unfold h3Pairing
  rw [show orderedPairing 0 N q (bilinearConvection N q q) = 0 from
    inner_bilinearConvection_self_zero N q q, energy3_eq_frequencyEnergy]
  nlinarith

end
end QuantumAdapter.Obligations
