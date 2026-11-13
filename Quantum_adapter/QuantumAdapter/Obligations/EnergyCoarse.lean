import QuantumAdapter.Obligations.EnergyTrilinear
import QuantumAdapter.Obligations.EnergyGradientTensor

/-! Uniform coarse commutator component estimates for the exact H3 energy. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

theorem norm_synthesis_first_le (N : ℕ) (q : Phase N) (i : Fin 3) (x : Vec) :
    ‖synthesis (phaseDerivative N i q) x‖ ≤ gradientObservable q := by
  have h : ‖synthesis (phaseDerivative N i q) x‖^2 ≤ gradientSquare q x := by
    rw [synthesis_phaseDerivative]
    exact Finset.single_le_sum (fun j hj => sq_nonneg _) (Finset.mem_univ i)
  have hs : ‖synthesis (phaseDerivative N i q) x‖ ≤ Real.sqrt (gradientSquare q x) :=
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rwa [Real.sq_sqrt (Assembly.gradientSquare_nonneg N q x)])
  exact hs.trans (le_csSup (Assembly.gradientObservable_range_bddAbove N q)
    (Set.mem_range_self x))

theorem norm_synthesis_second_le (N : ℕ) (q : Phase N) (i j : Fin 3) (x : Vec) :
    ‖synthesis (phaseDerivative N j (phaseDerivative N i q)) x‖ ≤
      Real.sqrt (gradientSecondDensity N q x) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (gradientSecondDensity_nonneg N q x)]
  exact (Finset.single_le_sum (fun l hl => sq_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum
      (fun k hk => Finset.sum_nonneg (fun l hl => sq_nonneg _)) (Finset.mem_univ i))

theorem norm_synthesis_third_le (N : ℕ) (q : Phase N) (i j k : Fin 3) (x : Vec) :
    ‖synthesis (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q))) x‖ ≤
      Real.sqrt (gradientThirdDensity N q x) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (gradientThirdDensity_nonneg N q x)]
  exact (Finset.single_le_sum (fun l hl => sq_nonneg _) (Finset.mem_univ k)).trans
    ((Finset.single_le_sum
      (fun l hl => Finset.sum_nonneg (fun m hm => sq_nonneg _)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun l hl => Finset.sum_nonneg (fun m hm =>
        Finset.sum_nonneg (fun n hn => sq_nonneg _))) (Finset.mem_univ i)))

theorem sqrt_gradient_first_le_second (N : ℕ) (q : Phase N) (i : Fin 3) (x : Vec) :
    Real.sqrt (gradientSquare (phaseDerivative N i q) x) ≤
      Real.sqrt (gradientSecondDensity N q x) := by
  apply Real.sqrt_le_sqrt
  rw [gradientSecondDensity_eq_sum_gradientSquare]
  exact Finset.single_le_sum
    (fun j hj => Assembly.gradientSquare_nonneg N _ x) (Finset.mem_univ i)

theorem sqrt_gradient_second_le_third (N : ℕ) (q : Phase N) (i j : Fin 3) (x : Vec) :
    Real.sqrt (gradientSquare (phaseDerivative N j (phaseDerivative N i q)) x) ≤
      Real.sqrt (gradientThirdDensity N q x) := by
  apply Real.sqrt_le_sqrt
  rw [gradientThirdDensity_eq_sum_second]
  have hs : gradientSquare (phaseDerivative N j (phaseDerivative N i q)) x ≤
      gradientSecondDensity N (phaseDerivative N i q) x := by
    rw [gradientSecondDensity_eq_sum_gradientSquare]
    exact Finset.single_le_sum (fun l hl => Assembly.gradientSquare_nonneg N _ x)
      (Finset.mem_univ j)
  exact hs.trans (Finset.single_le_sum
    (fun l hl => gradientSecondDensity_nonneg N _ x) (Finset.mem_univ i))

theorem norm_second_phase_sq_le (N : ℕ) (q : Phase N) (i j : Fin 3) :
    ‖phaseDerivative N j (phaseDerivative N i q)‖^2 ≤ frequencyEnergy 2 N q := by
  have hs : (∑ a : Fin 3, ∑ b : Fin 3,
      ‖phaseDerivative N b (phaseDerivative N a q)‖^2) = frequencyEnergy 2 N q := by
    simp_rw [← frequencyEnergy_zero N, frequencyEnergy_derivative_sum]
  rw [← hs]
  exact (Finset.single_le_sum (fun b hb => sq_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a ha => Finset.sum_nonneg (fun b hb => sq_nonneg _))
      (Finset.mem_univ i))

theorem norm_third_phase_sq_le (N : ℕ) (q : Phase N) (i j k : Fin 3) :
    ‖phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q))‖^2 ≤
      frequencyEnergy 3 N q := by
  have hs : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      ‖phaseDerivative N c (phaseDerivative N b (phaseDerivative N a q))‖^2) =
        frequencyEnergy 3 N q := by
    simp_rw [← frequencyEnergy_zero N, frequencyEnergy_derivative_sum]
  rw [← hs]
  exact (Finset.single_le_sum (fun c hc => sq_nonneg _) (Finset.mem_univ k)).trans
    ((Finset.single_le_sum (fun b hb => Finset.sum_nonneg (fun c hc => sq_nonneg _))
      (Finset.mem_univ j)).trans (Finset.single_le_sum (fun a ha =>
        Finset.sum_nonneg (fun b hb => Finset.sum_nonneg (fun c hc => sq_nonneg _)))
          (Finset.mem_univ i)))

theorem trilinear_le_of_square_density (N : ℕ) (z a b : Phase N) (G : ℝ)
    (H : Vec → ℝ) (hG : 0 ≤ G) (hH : Continuous H) (hH0 : ∀ x, 0 ≤ H x)
    (hz : ∀ x, ‖synthesis z x‖ ≤ Real.sqrt (H x))
    (ha : ∀ x, ‖synthesis a x‖ ≤ G)
    (hb : ∀ x, Real.sqrt (gradientSquare b x) ≤ Real.sqrt (H x)) :
    inner ℝ z (bilinearConvection N a b) ≤ G * ∫ x in unitCube, H x := by
  have hpoint (x : Vec) :
      ‖synthesis z x‖ * ‖synthesis a x‖ * Real.sqrt (gradientSquare b x) ≤ G * H x := by
    calc
      _ ≤ (Real.sqrt (H x) * G) * Real.sqrt (H x) :=
        mul_le_mul (mul_le_mul (hz x) (ha x) (norm_nonneg _) (Real.sqrt_nonneg _))
          (hb x) (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hG)
      _ = G * (Real.sqrt (H x))^2 := by ring
      _ = G * H x := by rw [Real.sq_sqrt (hH0 x)]
  have h := inner_bilinearConvection_le_of_pointwise N z a b
    (fun x => G * H x) (hH.const_mul G) hpoint
  rwa [integral_const_mul] at h

theorem second_first_first_bound (N : ℕ) (q : Phase N) (i j a b : Fin 3) :
    inner ℝ (phaseDerivative N j (phaseDerivative N i q))
      (bilinearConvection N (phaseDerivative N a q) (phaseDerivative N b q)) ≤
        gradientObservable q * frequencyEnergy 2 N q := by
  have h := trilinear_le_of_square_density N _ _ _ (gradientObservable q)
    (gradientSecondDensity N q) (Assembly.gradientObservable_nonneg N q)
    (gradientSecondDensity_continuous N q) (gradientSecondDensity_nonneg N q)
    (norm_synthesis_second_le N q i j) (norm_synthesis_first_le N q a)
    (sqrt_gradient_first_le_second N q b)
  rwa [integral_gradientSecondDensity] at h

theorem third_first_second_bound (N : ℕ) (q : Phase N) (i j k a b c : Fin 3) :
    inner ℝ (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q)))
      (bilinearConvection N (phaseDerivative N a q)
        (phaseDerivative N c (phaseDerivative N b q))) ≤
          gradientObservable q * frequencyEnergy 3 N q := by
  have h := trilinear_le_of_square_density N _ _ _ (gradientObservable q)
    (gradientThirdDensity N q) (Assembly.gradientObservable_nonneg N q)
    (gradientThirdDensity_continuous N q) (gradientThirdDensity_nonneg N q)
    (norm_synthesis_third_le N q i j k) (norm_synthesis_first_le N q a)
    (sqrt_gradient_second_le_third N q b c)
  rwa [integral_gradientThirdDensity] at h

theorem third_second_first_bound (N : ℕ) (q : Phase N) (i j k a b c : Fin 3) :
    inner ℝ (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q)))
      (bilinearConvection N (phaseDerivative N b (phaseDerivative N a q))
        (phaseDerivative N c q)) ≤
          4 * gradientObservable q * frequencyEnergy 3 N q := by
  let H2 := gradientSecondDensity N q
  let H3 := gradientThirdDensity N q
  have hpoint (x : Vec) :
      ‖synthesis (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q))) x‖ *
      ‖synthesis (phaseDerivative N b (phaseDerivative N a q)) x‖ *
      Real.sqrt (gradientSquare (phaseDerivative N c q) x) ≤ Real.sqrt (H3 x) * H2 x := by
    calc
      _ ≤ (Real.sqrt (H3 x) * Real.sqrt (H2 x)) * Real.sqrt (H2 x) :=
        mul_le_mul
          (mul_le_mul (norm_synthesis_third_le N q i j k x)
            (norm_synthesis_second_le N q a b x) (norm_nonneg _) (Real.sqrt_nonneg _))
          (sqrt_gradient_first_le_second N q c x) (Real.sqrt_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = _ := by rw [mul_assoc, ← pow_two, Real.sq_sqrt (gradientSecondDensity_nonneg N q x)]
  have hbase := inner_bilinearConvection_le_of_pointwise N _ _ _
    (fun x => Real.sqrt (H3 x) * H2 x)
    ((gradientThirdDensity_continuous N q).sqrt.mul (gradientSecondDensity_continuous N q))
    hpoint
  have hcs := integral_unitCube_mul_le_sqrt (fun x => Real.sqrt (H3 x)) H2
    (gradientThirdDensity_continuous N q).sqrt (gradientSecondDensity_continuous N q)
    (fun x => Real.sqrt_nonneg _) (gradientSecondDensity_nonneg N q)
  have hsq : (fun x => Real.sqrt (H3 x)^2) = H3 := by
    funext x
    exact Real.sq_sqrt (gradientThirdDensity_nonneg N q x)
  rw [hsq, integral_gradientThirdDensity] at hcs
  have hti := synthesis_second_derivative_interpolation N q
  have hmul := mul_le_mul_of_nonneg_left hti (Real.sqrt_nonneg (frequencyEnergy 3 N q))
  have hfinal : Real.sqrt (frequencyEnergy 3 N q) *
      Real.sqrt (∫ x in unitCube, H2 x^2) ≤
        4 * gradientObservable q * frequencyEnergy 3 N q := by
    calc
      _ ≤ Real.sqrt (frequencyEnergy 3 N q) *
          (4 * gradientObservable q * Real.sqrt (frequencyEnergy 3 N q)) := hmul
      _ = (4 * gradientObservable q) * (Real.sqrt (frequencyEnergy 3 N q))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (frequencyEnergy_nonneg 3 N q)]
  exact hbase.trans (hcs.trans hfinal)

end
end QuantumAdapter.Obligations
