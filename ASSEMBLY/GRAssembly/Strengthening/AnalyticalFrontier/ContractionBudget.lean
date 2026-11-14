import GRAssembly.Strengthening.AnalyticalFrontier.ScalarHeatEstimates

/-!
Exact numerical budget for the fixed-`A₀` Duhamel contraction.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

def analyticalWienerRadius (L M : ℝ) : ℝ := 2 * L * M

def analyticalWienerLipschitzBudget (L M : ℝ) : ℝ :=
  (8 * L * M)⁻¹

theorem analyticalWienerRadius_pos {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) :
    0 < analyticalWienerRadius L M := by
  unfold analyticalWienerRadius
  positivity

theorem analyticalWienerLipschitzBudget_pos {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) :
    0 < analyticalWienerLipschitzBudget L M := by
  unfold analyticalWienerLipschitzBudget
  positivity

theorem analyticalWiener_budget_mul_radius {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) :
    analyticalWienerLipschitzBudget L M *
        analyticalWienerRadius L M = (1 : ℝ) / 4 := by
  unfold analyticalWienerLipschitzBudget analyticalWienerRadius
  field_simp [hL.ne', hM.ne']
  <;> ring

theorem analyticalWiener_two_budget_mul_radius {L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) :
    2 * analyticalWienerLipschitzBudget L M *
        analyticalWienerRadius L M = (1 : ℝ) / 2 := by
  rw [mul_assoc, analyticalWiener_budget_mul_radius hL hM]
  ring

/-- The exact radius and contraction constants used by the fixed-point step. -/
def ANALYTICAL_CONTRACTION_BUDGET_CHECKPOINT : Prop :=
  ∀ L M : ℝ, 0 < L → 0 < M →
    0 < analyticalWienerRadius L M ∧
    0 < analyticalWienerLipschitzBudget L M ∧
    analyticalWienerLipschitzBudget L M *
        analyticalWienerRadius L M = (1 : ℝ) / 4 ∧
    2 * analyticalWienerLipschitzBudget L M *
        analyticalWienerRadius L M = (1 : ℝ) / 2

theorem ANALYTICAL_CONTRACTION_BUDGET_CHECKPOINT_NATIVE :
    ANALYTICAL_CONTRACTION_BUDGET_CHECKPOINT := by
  intro L M hL hM
  exact ⟨analyticalWienerRadius_pos hL hM,
    analyticalWienerLipschitzBudget_pos hL hM,
    analyticalWiener_budget_mul_radius hL hM,
    analyticalWiener_two_budget_mul_radius hL hM⟩

end
end NSEGR.Strengthening
