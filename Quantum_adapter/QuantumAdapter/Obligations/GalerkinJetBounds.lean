import QuantumAdapter.Obligations.GalerkinJet
import QuantumAdapter.Obligations.GalerkinBilinearNorm
import QuantumAdapter.Obligations.GalerkinPropagation

/-! Cutoff-uniform Sobolev bounds for every actual finite time jet. -/
set_option autoImplicit false
set_option Elab.async true
open Set
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure QuantumAdapter.Assembly

theorem sobolevEnergy_add_le (m N : ℕ) (q r : Phase N) :
    sobolevEnergy m N (q + r) ≤ 2 * sobolevEnergy m N q + 2 * sobolevEnergy m N r := by
  rw [← sobolevWeightedPhase_norm_sq, map_add,
    ← sobolevWeightedPhase_norm_sq, ← sobolevWeightedPhase_norm_sq]
  have h := pow_le_pow_left₀
    (norm_nonneg (sobolevWeightedPhaseCLM m N q + sobolevWeightedPhaseCLM m N r))
    (norm_add_le (sobolevWeightedPhaseCLM m N q) (sobolevWeightedPhaseCLM m N r)) 2
  nlinarith [sq_nonneg (‖sobolevWeightedPhaseCLM m N q‖ - ‖sobolevWeightedPhaseCLM m N r‖)]

theorem sobolevEnergy_smul (m N : ℕ) (q : Phase N) (a : ℝ) :
    sobolevEnergy m N (a • q) = a^2 * sobolevEnergy m N q := by
  rw [← sobolevWeightedPhase_norm_sq, map_smul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, sobolevWeightedPhase_norm_sq]

theorem sobolevEnergy_laplacian_le (m N : ℕ) (q : Phase N) :
    sobolevEnergy m N (phaseLaplacianCLM N q) ≤ sobolevEnergy (m+2) N q := by
  unfold sobolevEnergy sobolevEnergyDensity
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro i hi
  rw [sobolevWeightedCoeff_norm_eq, sobolevWeightedCoeff_norm_eq]
  change (torusSobolevWeight k^m * ‖phaseCoeff (phaseLaplacian N q) k i‖)^2 ≤ _
  rw [phaseLaplacian_coeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (laplaceSymbol_nonneg k)]
  apply pow_le_pow_left₀ (mul_nonneg (pow_nonneg (torusSobolevWeight_pos k).le m)
    (mul_nonneg (laplaceSymbol_nonneg k) (norm_nonneg _)))
  have hl : laplaceSymbol k ≤ torusSobolevWeight k^2 := by
    rw [torusSobolevWeight_sq_native]
    linarith
  calc
    _ = (torusSobolevWeight k^m * laplaceSymbol k) * ‖phaseCoeff q k i‖ := by ring
    _ ≤ (torusSobolevWeight k^m * torusSobolevWeight k^2) * ‖phaseCoeff q k i‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hl (pow_nonneg (torusSobolevWeight_pos k).le m))
        (norm_nonneg _)
    _ = _ := by rw [pow_add]

/-- Uniform bounds on the actual phase family propagate through every finite
expression built from addition, scalar multiplication, the Laplacian and convection. -/
theorem GalerkinExpr.uniform_sobolev_bounds {ι : Type*}
    (e : GalerkinExpr) (q : (N : ℕ) → ι → Phase N) (P : ℕ → ι → Prop)
    (hq : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, ∀ x : ι, P N x → sobolevEnergy m N (q N x) ≤ C) :
    ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, ∀ x : ι, P N x → sobolevEnergy m N (e.eval N (q N x)) ≤ C := by
  induction e with
  | id => exact hq
  | add e f he hf =>
    intro m
    obtain ⟨A,hA,hAe⟩ := he m
    obtain ⟨B,hB,hBf⟩ := hf m
    refine ⟨2*A+2*B, by positivity, ?_⟩
    intro N x hx
    change sobolevEnergy m N (e.eval N (q N x) + f.eval N (q N x)) ≤ _
    exact (sobolevEnergy_add_le m N _ _).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hAe N x hx) (by norm_num))
        (mul_le_mul_of_nonneg_left (hBf N x hx) (by norm_num)))
  | smul a e he =>
    intro m
    obtain ⟨A,hA,hAe⟩ := he m
    refine ⟨a^2*A, mul_nonneg (sq_nonneg a) hA, ?_⟩
    intro N x hx
    change sobolevEnergy m N (a • e.eval N (q N x)) ≤ _
    rw [sobolevEnergy_smul]
    exact mul_le_mul_of_nonneg_left (hAe N x hx) (sq_nonneg a)
  | laplace e he =>
    intro m
    obtain ⟨A,hA,hAe⟩ := he (m+2)
    refine ⟨A,hA,?_⟩
    intro N x hx
    exact (sobolevEnergy_laplacian_le m N (e.eval N (q N x))).trans (hAe N x hx)
  | bilinear e f he hf =>
    intro m
    obtain ⟨A,hA,hAe⟩ := he 2
    obtain ⟨B,hB,hBe⟩ := he (m+1)
    obtain ⟨C,hC,hCf⟩ := hf 2
    obtain ⟨D,hD,hDf⟩ := hf (m+1)
    let K : ℝ := 54*((2:ℝ)^(m+1))^2*latticeSobolevConstant
    have hK : 0 ≤ K := mul_nonneg (by positivity) latticeSobolevConstant_pos.le
    refine ⟨K*(C*B+A*D), mul_nonneg hK (add_nonneg (mul_nonneg hC hB) (mul_nonneg hA hD)), ?_⟩
    intro N x hx
    change sobolevEnergy m N (bilinearConvection N (e.eval N (q N x))
      (f.eval N (q N x))) ≤ _
    apply (bilinearConvection_sobolevEnergy_le m N _ _).trans
    apply mul_le_mul_of_nonneg_left _ hK
    apply add_le_add
    · exact mul_le_mul (hCf N x hx) (hBe N x hx)
        (sobolevEnergy_nonneg (m+1) N _) hC
    · exact mul_le_mul (hAe N x hx) (hDf N x hx)
        (sobolevEnergy_nonneg (m+1) N _) hA

/-- Every mixed-order time jet of the actual smooth Galerkin orbit has a
cutoff-independent bound on each finite forward time interval. -/
theorem galerkin_all_timeJet_sobolev_bounds {ν : ℝ} (hν : 0 < ν) (F : PhaseFlow ν)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a)
    (h3 : ∀ T : ℝ, 0 < T → GalerkinBoundAt F a ha T) :
    ∀ n m : ℕ, ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
        sobolevEnergy m N (phaseTimeJet F N (initialPhaseData N a ha) n t) ≤ C := by
  intro n m T hT
  have hq : ∀ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, ∀ t : ℝ, (1 ≤ N ∧ 0 ≤ t ∧ t ≤ T) →
        sobolevEnergy s N (F.map N t (initialPhaseData N a ha)) ≤ C := by
    intro s
    obtain ⟨C,hC,hbound⟩ := galerkin_all_sobolev_bounds hν F a ha h3 s T hT
    exact ⟨C,hC,fun N t ht => hbound N ht.1 t ht.2.1 ht.2.2⟩
  obtain ⟨C,hC,hbound⟩ := GalerkinExpr.uniform_sobolev_bounds
    (GalerkinExpr.jetExpr ν n) (fun N t => F.map N t (initialPhaseData N a ha))
    (fun N t => 1 ≤ N ∧ 0 ≤ t ∧ t ≤ T) hq m
  exact ⟨C,hC,fun N hN t ht htT => hbound N t ⟨hN,ht,htT⟩⟩

end
end QuantumAdapter.Obligations
