import SingularClosure.InfiniteScalarProduct
import SingularClosure.FourierTransport
import SingularClosure.FourierSobolevOperators
import SingularClosure.HighOrderEstimate

/-! The actual infinite divergence product maps H^(r+2) times H^(r+2) to H^r.
The inputs are arbitrary coefficient arrays in these spaces. In particular,
neither solenoidality nor a finite-support premise is used. -/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators ENNReal

namespace SingularClosure

noncomputable section

theorem torusSobolev_component_moment_sum_le (q s : ℕ) (hqs : q ≤ s)
    (c : TorusSobolev s) (i : Fin 3) (S : Finset Frequency) :
    (∑ k ∈ S, (torusSobolevWeight k ^ q * ‖c.val k i‖) ^ 2) ≤ ‖c‖ ^ 2 := by
  classical
  have h := torusSobolev_finite_weighted_sum_le q (torusSobolevLower q s hqs c)
    (S.product {i})
  simp only [torusSobolev_weightedCoeff_norm, torusSobolevLower_coeff] at h
  have hsum :
      (∑ ki ∈ S.product {i}, (torusSobolevWeight ki.1 ^ q * ‖c.val ki.1 ki.2‖) ^ 2) =
        ∑ k ∈ S, (torusSobolevWeight k ^ q * ‖c.val k i‖) ^ 2 := by
    calc
      _ = ∑ k ∈ S, ∑ j ∈ ({i} : Finset (Fin 3)),
          (torusSobolevWeight k ^ q * ‖c.val k j‖) ^ 2 :=
        Finset.sum_product S {i}
          (fun ki : FourierIndex => (torusSobolevWeight ki.1 ^ q * ‖c.val ki.1 ki.2‖) ^ 2)
      _ = _ := by simp only [Finset.sum_singleton]
  exact hsum.symm.trans_le (h.trans (pow_le_pow_left₀ (norm_nonneg _)
    (torusSobolevLower_norm_le q s hqs c) 2))

/-- The actual output-frequency derivative of the infinite tensor convolution. -/
def sobolevDivergenceProductCoeff (r : ℕ) (c d : TorusSobolev (r + 2)) : FourierCoeff :=
  fun k i => divergenceTransportCoefficient k i
    (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
    (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d)

theorem sobolevDivergenceProductCoeff_apply (r : ℕ)
    (c d : TorusSobolev (r + 2)) (k : Frequency) (i : Fin 3) :
    sobolevDivergenceProductCoeff r c d k i =
      ∑ j : Fin 3, derivativeSymbol j k *
        (∑' p : Frequency, c.val p j * d.val (k - p) i) := by
  simp only [sobolevDivergenceProductCoeff, divergenceTransportCoefficient_apply,
    torusSobolevLower_coeff]

theorem sobolev_tensor_coefficient_summable (r : ℕ)
    (c d : TorusSobolev (r + 2)) (k : Frequency) (j i : Fin 3) :
    Summable (fun p : Frequency => c.val p j * d.val (k - p) i) := by
  simpa only [torusSobolevLower_coeff] using fourierTensorCoefficient_summable k j i
    (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
    (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d)

theorem sobolevDivergenceProductCoeff_weighted_sq_le (r : ℕ)
    (c d : TorusSobolev (r + 2)) (k : Frequency) (i : Fin 3) :
    (torusSobolevWeight k ^ r * ‖sobolevDivergenceProductCoeff r c d k i‖) ^ 2 ≤
      3 * ∑ j : Fin 3, (torusSobolevWeight k ^ (r + 1) *
        ‖∑' p : Frequency, c.val p j * d.val (k - p) i‖) ^ 2 := by
  let A : Fin 3 → ℝ := fun j => torusSobolevWeight k ^ (r + 1) *
    ‖∑' p : Frequency, c.val p j * d.val (k - p) i‖
  have hnorm : torusSobolevWeight k ^ r * ‖sobolevDivergenceProductCoeff r c d k i‖ ≤
      ∑ j : Fin 3, A j := by
    rw [sobolevDivergenceProductCoeff_apply]
    calc
      _ ≤ torusSobolevWeight k ^ r * ∑ j : Fin 3,
          ‖derivativeSymbol j k * (∑' p : Frequency, c.val p j * d.val (k - p) i)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _)
          (pow_nonneg (torusSobolevWeight_pos k).le r)
      _ = ∑ j : Fin 3, torusSobolevWeight k ^ r *
          (‖derivativeSymbol j k‖ * ‖∑' p : Frequency, c.val p j * d.val (k - p) i‖) := by
        rw [Finset.mul_sum]
        simp only [norm_mul]
      _ ≤ ∑ j : Fin 3, A j := by
        apply Finset.sum_le_sum
        intro j _
        dsimp only [A]
        rw [pow_succ]
        calc
          _ ≤ torusSobolevWeight k ^ r * (torusSobolevWeight k *
              ‖∑' p : Frequency, c.val p j * d.val (k - p) i‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (derivativeSymbol_norm_le_weight k j)
                (norm_nonneg _)) (pow_nonneg (torusSobolevWeight_pos k).le r)
          _ = _ := by ring
  have hCS : (∑ j : Fin 3, A j) ^ 2 ≤ 3 * ∑ j : Fin 3, (A j) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
      (fun _ => (1 : ℝ)) A
  exact (pow_le_pow_left₀
    (mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le r) (norm_nonneg _))
    hnorm 2).trans hCS

/-- Uniform weighted finite sums for the actual infinite product. -/
theorem SOBOLEV_DIVERGENCE_PRODUCT_FINITE_BOUND (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c d : TorusSobolev (r + 2), ∀ S : Finset FourierIndex,
      (∑ ki ∈ S, ‖sobolevWeightedCoeff r (sobolevDivergenceProductCoeff r c d) ki‖ ^ 2) ≤
        C * ‖c‖ ^ 2 * ‖d‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hprod⟩ := INFINITE_SCALAR_FOURIER_PRODUCT_BOUND (r + 1)
  refine ⟨27 * C, by positivity, ?_⟩
  intro c d S
  let R : Finset Frequency := S.image Prod.fst
  have hsub : S ⊆ R.product (Finset.univ : Finset (Fin 3)) := by
    intro ki hki
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨ki, hki, rfl⟩, Finset.mem_univ _⟩
  have hpair (i j : Fin 3) :
      (∑ k ∈ R, (torusSobolevWeight k ^ (r + 1) *
        ‖∑' p : Frequency, c.val p j * d.val (k - p) i‖) ^ 2) ≤
          C * ‖c‖ ^ 2 * ‖d‖ ^ 2 := by
    exact hprod (fun p => c.val p j) (fun q => d.val q i) (‖c‖ ^ 2) (‖d‖ ^ 2)
      (sq_nonneg _) (sq_nonneg _)
      (torusSobolev_component_moment_sum_le 2 (r + 2) (by omega) c j)
      (torusSobolev_component_moment_sum_le (r + 1) (r + 2) (by omega) c j)
      (torusSobolev_component_moment_sum_le 2 (r + 2) (by omega) d i)
      (torusSobolev_component_moment_sum_le (r + 1) (r + 2) (by omega) d i)
      (fun k => sobolev_tensor_coefficient_summable r c d k j i) R
  calc
    _ ≤ ∑ ki ∈ R.product (Finset.univ : Finset (Fin 3)),
        ‖sobolevWeightedCoeff r (sobolevDivergenceProductCoeff r c d) ki‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ki _ _ => sq_nonneg _)
    _ ≤ ∑ ki ∈ R.product (Finset.univ : Finset (Fin 3)),
        3 * ∑ j : Fin 3, (torusSobolevWeight ki.1 ^ (r + 1) *
          ‖∑' p : Frequency, c.val p j * d.val (ki.1 - p) ki.2‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro ki _
      rw [torusSobolev_weightedCoeff_norm]
      exact sobolevDivergenceProductCoeff_weighted_sq_le r c d ki.1 ki.2
    _ = 3 * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k ∈ R,
        (torusSobolevWeight k ^ (r + 1) *
          ‖∑' p : Frequency, c.val p j * d.val (k - p) i‖) ^ 2 := by
      calc
        _ = ∑ k ∈ R, ∑ i : Fin 3, 3 * ∑ j : Fin 3,
            (torusSobolevWeight k ^ (r + 1) *
              ‖∑' p : Frequency, c.val p j * d.val (k - p) i‖) ^ 2 :=
          Finset.sum_product R Finset.univ (fun ki : FourierIndex =>
            3 * ∑ j : Fin 3, (torusSobolevWeight ki.1 ^ (r + 1) *
              ‖∑' p : Frequency, c.val p j * d.val (ki.1 - p) ki.2‖) ^ 2)
        _ = _ := by
          simp only [← Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ ≤ 3 * ∑ i : Fin 3, ∑ j : Fin 3, C * ‖c‖ ^ 2 * ‖d‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
    _ = (27 * C) * ‖c‖ ^ 2 * ‖d‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Membership and a uniform bilinear norm estimate, with no finite-support restriction. -/
theorem SOBOLEV_DIVERGENCE_PRODUCT_MEM_NORM_BOUND (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c d : TorusSobolev (r + 2),
      ∃ hc : Memℓp (sobolevWeightedCoeff r (sobolevDivergenceProductCoeff r c d)) 2,
        @norm (TorusSobolev r) inferInstance ⟨sobolevDivergenceProductCoeff r c d, hc⟩ ≤
          C * ‖c‖ * ‖d‖ := by
  obtain ⟨C, hC, hbound⟩ := SOBOLEV_DIVERGENCE_PRODUCT_FINITE_BOUND r
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro c d
  have hc : Memℓp (sobolevWeightedCoeff r (sobolevDivergenceProductCoeff r c d)) 2 := by
    apply memℓp_gen' (C := C * ‖c‖ ^ 2 * ‖d‖ ^ 2)
    intro S
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hbound c d S
  refine ⟨hc, ?_⟩
  change ‖torusSobolevRepr r (⟨sobolevDivergenceProductCoeff r c d, hc⟩ : TorusSobolev r)‖ ≤ _
  apply lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) (by norm_num) (by positivity)
  intro S
  have hsquare : (Real.sqrt C * ‖c‖ * ‖d‖) ^ 2 = C * ‖c‖ ^ 2 * ‖d‖ ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC.le]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hsquare]
  calc
    _ = ∑ ki ∈ S, ‖sobolevWeightedCoeff r (sobolevDivergenceProductCoeff r c d) ki‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro ki _
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
        (torusSobolevRepr_apply r
          (⟨sobolevDivergenceProductCoeff r c d, hc⟩ : TorusSobolev r) ki)
    _ ≤ _ := hbound c d S

theorem sobolevDivergenceProductCoeff_mem (r : ℕ) (c d : TorusSobolev (r + 2)) :
    Memℓp (sobolevWeightedCoeff r (sobolevDivergenceProductCoeff r c d)) 2 := by
  obtain ⟨C, hC, hbound⟩ := SOBOLEV_DIVERGENCE_PRODUCT_MEM_NORM_BOUND r
  exact (hbound c d).choose

def sobolevDivergenceProduct (r : ℕ) (c d : TorusSobolev (r + 2)) : TorusSobolev r :=
  ⟨sobolevDivergenceProductCoeff r c d, sobolevDivergenceProductCoeff_mem r c d⟩

@[simp]
theorem sobolevDivergenceProduct_coeff (r : ℕ) (c d : TorusSobolev (r + 2)) :
    (sobolevDivergenceProduct r c d).val = sobolevDivergenceProductCoeff r c d := rfl

theorem SOBOLEV_DIVERGENCE_PRODUCT_NORM_BOUND (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c d : TorusSobolev (r + 2),
      ‖sobolevDivergenceProduct r c d‖ ≤ C * ‖c‖ * ‖d‖ := by
  obtain ⟨C, hC, hbound⟩ := SOBOLEV_DIVERGENCE_PRODUCT_MEM_NORM_BOUND r
  refine ⟨C, hC, ?_⟩
  intro c d
  exact (hbound c d).choose_spec

end

end SingularClosure
