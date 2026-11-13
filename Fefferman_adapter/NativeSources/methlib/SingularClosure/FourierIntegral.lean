import SingularClosure.PhysicalEnstrophy

/-!
# Fourier orthogonality on the actual physical fundamental cube

All integrals below use the physical Euclidean Lebesgue measure specified by
`Contracts.lean`.  The measure change to a product cube is proved by the
measure-preserving Euclidean coordinate equivalence.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem integral_unitCube_product (f : Fin 3 → ℝ → ℂ) :
    (∫ x in unitCube, ∏ i : Fin 3, f i (x i)) =
      ∏ i : Fin 3, ∫ t in Icc (0 : ℝ) 1, f i t := by
  have hchange := (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    (fun x : Vec => ∏ i : Fin 3, f i (x i)) unitCube
  have hpre : (@WithLp.toLp 2 (Fin 3 → ℝ)) ⁻¹' unitCube =
      Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
    ext x
    change (∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1) ↔
      (∀ i : Fin 3, i ∈ Set.univ → 0 ≤ x i ∧ x i ≤ 1)
    exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩
  rw [hpre] at hchange
  rw [← hchange]
  change (∫ x : Fin 3 → ℝ, ∏ i : Fin 3, f i (x i)
    ∂((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1)))) = _
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod f

theorem integral_oneDimensional_character (n : ℤ) :
    (∫ t in Icc (0 : ℝ) 1,
      fourier n (t : UnitAddCircle)) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  rw [fourierCoeff_eq_intervalIntegral _ 0 0] at h
  simp only [one_div_one, one_smul, neg_zero, zero_add,
    fourier_zero, one_smul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  rw [integral_Icc_eq_integral_Ioc]
  simpa [Pi.single_apply, eq_comm] using h

theorem fourierCharacter_eq_product (k : Frequency) (x : Vec) :
    fourierCharacter k x =
      ∏ i : Fin 3, fourier (k i) (x i : UnitAddCircle) := by
  simp only [fourier_coe_apply, div_one, ← Complex.exp_sum]
  unfold fourierCharacter
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integral_fourierCharacter (k : Frequency) :
    (∫ x in unitCube, fourierCharacter k x) = if k = 0 then 1 else 0 := by
  classical
  simp_rw [fourierCharacter_eq_product]
  rw [integral_unitCube_product (fun i t => fourier (k i) (t : UnitAddCircle))]
  simp_rw [integral_oneDimensional_character]
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [Pi.zero_apply] at hi
    simp [hi]

theorem fourierCharacter_mul (k l : Frequency) (x : Vec) :
    fourierCharacter k x * fourierCharacter l x = fourierCharacter (k + l) x := by
  simp only [fourierCharacter_eq_product, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (fourier_add (m := k i) (n := l i)).symm

theorem fourierCharacter_neg (k : Frequency) (x : Vec) :
    fourierCharacter (-k) x = star (fourierCharacter k x) := by
  simp only [fourierCharacter_eq_product, Pi.neg_apply, fourier_neg,
    map_prod, Complex.star_def]

theorem INTEGRAL_FOURIER_CHARACTER_ORTHOGONALITY (k l : Frequency) :
    (∫ x in unitCube, star (fourierCharacter k x) * fourierCharacter l x) =
      if k = l then 1 else 0 := by
  classical
  simp_rw [← fourierCharacter_neg, fourierCharacter_mul]
  rw [integral_fourierCharacter]
  have heq : (-k + l = 0) ↔ k = l := by
    constructor
    · intro h
      have hlk : l - k = 0 := by simpa [sub_eq_add_neg, add_comm] using h
      exact (sub_eq_zero.mp hlk).symm
    · intro h
      simp [h]
  simp only [heq]

end

end SingularClosure
