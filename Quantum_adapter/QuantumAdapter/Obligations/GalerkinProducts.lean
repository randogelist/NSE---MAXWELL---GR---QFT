import QuantumAdapter.Obligations.GalerkinConvolution

/-! Finite weighted product estimates with constants independent of the cutoff. -/
set_option autoImplicit false
set_option Elab.async true
open scoped BigOperators
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

theorem torusSobolevWeight_sq_product (k : Frequency) :
    torusSobolevWeight k ^ 2 = 1 + laplaceSymbol k := by
  change Real.sqrt (1 + laplaceSymbol k) ^ 2 = _
  exact Real.sq_sqrt (by linarith [laplaceSymbol_nonneg k])

theorem laplaceSymbol_split_bound (k p : Frequency) :
    laplaceSymbol k ≤ 2 * laplaceSymbol p + 2 * laplaceSymbol (k-p) := by
  have hsum : (∑ i : Fin 3, (k i : ℝ)^2) ≤
      2 * (∑ i : Fin 3, (p i : ℝ)^2) +
      2 * (∑ i : Fin 3, ((k-p) i : ℝ)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have he : (k i : ℝ) = (p i : ℝ) + ((k-p) i : ℝ) := by
      simp [Pi.sub_apply]
    rw [he]
    nlinarith [sq_nonneg ((p i : ℝ) - ((k-p) i : ℝ))]
  have h := mul_le_mul_of_nonneg_left hsum (sq_nonneg (2 * Real.pi))
  simpa [laplaceSymbol, galerkinFreqSq, mul_add, mul_left_comm, mul_assoc] using h

theorem torusSobolevWeight_pow_split_bound (m : ℕ) (k p : Frequency) :
    torusSobolevWeight k ^ m ≤ (2 : ℝ)^m *
      (torusSobolevWeight p ^ m + torusSobolevWeight (k-p) ^ m) := by
  have hsq : torusSobolevWeight k ^ 2 ≤
      2 * torusSobolevWeight p ^ 2 + 2 * torusSobolevWeight (k-p) ^ 2 := by
    rw [torusSobolevWeight_sq_product, torusSobolevWeight_sq_product,
      torusSobolevWeight_sq_product]
    linarith [laplaceSymbol_split_bound k p]
  rcases le_total (torusSobolevWeight p) (torusSobolevWeight (k-p)) with h | h
  · have hs := pow_le_pow_left₀ (torusSobolevWeight_pos p).le h 2
    have hk : torusSobolevWeight k ≤ 2 * torusSobolevWeight (k-p) := by
      nlinarith [torusSobolevWeight_pos k, torusSobolevWeight_pos (k-p)]
    calc
      _ ≤ (2 * torusSobolevWeight (k-p))^m :=
        pow_le_pow_left₀ (torusSobolevWeight_pos k).le hk m
      _ = (2:ℝ)^m * torusSobolevWeight (k-p)^m := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (pow_nonneg (torusSobolevWeight_pos p).le m)) (by positivity)
  · have hs := pow_le_pow_left₀ (torusSobolevWeight_pos (k-p)).le h 2
    have hk : torusSobolevWeight k ≤ 2 * torusSobolevWeight p := by
      nlinarith [torusSobolevWeight_pos k, torusSobolevWeight_pos p]
    calc
      _ ≤ (2 * torusSobolevWeight p)^m :=
        pow_le_pow_left₀ (torusSobolevWeight_pos k).le hk m
      _ = (2:ℝ)^m * torusSobolevWeight p^m := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (pow_nonneg (torusSobolevWeight_pos (k-p)).le m))
        (by positivity)

/-- Weighted finite Young estimate for a polynomially moderate weight. -/
theorem finite_weighted_product_square_sum_le
    (S : Finset Frequency) (a b : Frequency → ℂ)
    (hb : ∀ k, k ∉ S → b k = 0)
    (w : Frequency → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ k p, w k ≤ K * (w p + w (k-p))) :
    (∑ k ∈ S, (w k * ‖∑ p ∈ S, a p * b (k-p)‖)^2) ≤
      2*K^2 * ((∑ p ∈ S, ‖b p‖)^2 * ∑ p ∈ S, (w p * ‖a p‖)^2 +
        (∑ p ∈ S, ‖a p‖)^2 * ∑ p ∈ S, (w p * ‖b p‖)^2) := by
  let U : Frequency → ℝ := fun k => ∑ p ∈ S, (w p * ‖a p‖) * ‖b (k-p)‖
  let V : Frequency → ℝ := fun k => ∑ p ∈ S, ‖a p‖ * (w (k-p) * ‖b (k-p)‖)
  have hU (k : Frequency) : 0 ≤ U k :=
    Finset.sum_nonneg (fun p hp => mul_nonneg (mul_nonneg (hw0 p) (norm_nonneg _))
      (norm_nonneg _))
  have hV (k : Frequency) : 0 ≤ V k :=
    Finset.sum_nonneg (fun p hp => mul_nonneg (norm_nonneg _)
      (mul_nonneg (hw0 _) (norm_nonneg _)))
  have hpoint (k : Frequency) :
      w k * ‖∑ p ∈ S, a p * b (k-p)‖ ≤ K*(U k + V k) := by
    calc
      _ ≤ w k * ∑ p ∈ S, ‖a p * b (k-p)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hw0 k)
      _ = ∑ p ∈ S, w k * (‖a p‖ * ‖b (k-p)‖) := by
        rw [Finset.mul_sum]
        simp only [norm_mul]
      _ ≤ ∑ p ∈ S, K*(w p + w (k-p)) * (‖a p‖ * ‖b (k-p)‖) :=
        Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right
          (hw k p) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ = K*(U k + V k) := by
        simp only [U, V, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hsquare (k : Frequency) :
      (w k * ‖∑ p ∈ S, a p * b (k-p)‖)^2 ≤ 2*K^2*(U k^2+V k^2) := by
    have h := pow_le_pow_left₀ (mul_nonneg (hw0 k) (norm_nonneg _)) (hpoint k) 2
    have hdiff := mul_nonneg (sq_nonneg K) (sq_nonneg (U k - V k))
    nlinarith
  have hUS := finite_convolution_square_sum_le_right S
    (fun p => w p * ‖a p‖) (fun p => ‖b p‖) (fun p => norm_nonneg _)
    (fun p hp => by rw [hb p hp, norm_zero])
  have hVS := finite_convolution_square_sum_le S
    (fun p => ‖a p‖) (fun p => w p * ‖b p‖) (fun p => norm_nonneg _)
    (fun p hp => by rw [hb p hp, norm_zero, mul_zero])
  calc
    _ ≤ ∑ k ∈ S, 2*K^2*(U k^2+V k^2) := Finset.sum_le_sum (fun k hk => hsquare k)
    _ = 2*K^2*((∑ k ∈ S, U k^2)+(∑ k ∈ S, V k^2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hUS hVS) (by positivity)

def fullTensorProduct (N : ℕ) (q r : Phase N) (k : Frequency) (i j : Fin 3) : ℂ :=
  ∑ p ∈ fullModes N, phaseCoeff q p j * phaseCoeff r (k-p) i

def componentSobolevEnergy (s N : ℕ) (q : Phase N) (i : Fin 3) : ℝ :=
  ∑ k ∈ fullModes N, ‖sobolevWeightedCoeff s (phaseCoeff q) (k,i)‖^2

theorem componentSobolevEnergy_nonneg (s N : ℕ) (q : Phase N) (i : Fin 3) :
    0 ≤ componentSobolevEnergy s N q i := Finset.sum_nonneg (fun k hk => sq_nonneg _)

theorem componentSobolevEnergy_le (s N : ℕ) (q : Phase N) (i : Fin 3) :
    componentSobolevEnergy s N q i ≤ sobolevEnergy s N q := by
  apply Finset.sum_le_sum
  intro k hk
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 3 => ‖sobolevWeightedCoeff s (phaseCoeff q) (k,j)‖^2)
    (fun j hj => sq_nonneg _) (Finset.mem_univ i)

/-- One literal tensor coefficient product has the Hm tame estimate. -/
theorem fullTensorProduct_energy_bound (m N : ℕ) (q r : Phase N) (i j : Fin 3) :
    (∑ k ∈ fullModes N,
      (torusSobolevWeight k^m * ‖fullTensorProduct N q r k i j‖)^2) ≤
      2 * ((2:ℝ)^m)^2 * latticeSobolevConstant *
        (sobolevEnergy 2 N r * sobolevEnergy m N q +
          sobolevEnergy 2 N q * sobolevEnergy m N r) := by
  have h := finite_weighted_product_square_sum_le (fullModes N)
    (fun p => phaseCoeff q p j) (fun p => phaseCoeff r p i)
    (fun p hp => phaseCoeff_support r p hp i)
    (fun p => torusSobolevWeight p^m)
    (fun p => pow_nonneg (torusSobolevWeight_pos p).le m)
    ((2:ℝ)^m) (by positivity) (torusSobolevWeight_pow_split_bound m)
  have hq := weighted_component_l1_sq_le 0 N q j
  have hr := weighted_component_l1_sq_le 0 N r i
  simp only [pow_zero, one_mul, Nat.zero_add] at hq hr
  have hq' : (∑ p ∈ fullModes N, ‖phaseCoeff q p j‖)^2 ≤
      latticeSobolevConstant * sobolevEnergy 2 N q :=
    hq.trans (mul_le_mul_of_nonneg_left (componentSobolevEnergy_le 2 N q j)
      latticeSobolevConstant_pos.le)
  have hr' : (∑ p ∈ fullModes N, ‖phaseCoeff r p i‖)^2 ≤
      latticeSobolevConstant * sobolevEnergy 2 N r :=
    hr.trans (mul_le_mul_of_nonneg_left (componentSobolevEnergy_le 2 N r i)
      latticeSobolevConstant_pos.le)
  have heq : (∑ p ∈ fullModes N, (torusSobolevWeight p^m * ‖phaseCoeff q p j‖)^2) =
      componentSobolevEnergy m N q j := by simp only [componentSobolevEnergy,
        sobolevWeightedCoeff_norm_eq]
  have her : (∑ p ∈ fullModes N, (torusSobolevWeight p^m * ‖phaseCoeff r p i‖)^2) =
      componentSobolevEnergy m N r i := by simp only [componentSobolevEnergy,
        sobolevWeightedCoeff_norm_eq]
  rw [heq, her] at h
  calc
    _ ≤ _ := h
    _ ≤ 2*((2:ℝ)^m)^2 *
        ((latticeSobolevConstant * sobolevEnergy 2 N r)*sobolevEnergy m N q +
         (latticeSobolevConstant * sobolevEnergy 2 N q)*sobolevEnergy m N r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul hr' (componentSobolevEnergy_le m N q j)
          (componentSobolevEnergy_nonneg m N q j)
          (mul_nonneg latticeSobolevConstant_pos.le (sobolevEnergy_nonneg 2 N r)))
        (mul_le_mul hq' (componentSobolevEnergy_le m N r i)
          (componentSobolevEnergy_nonneg m N r i)
          (mul_nonneg latticeSobolevConstant_pos.le (sobolevEnergy_nonneg 2 N q)))
    _ = _ := by ring

end
end QuantumAdapter.Obligations
