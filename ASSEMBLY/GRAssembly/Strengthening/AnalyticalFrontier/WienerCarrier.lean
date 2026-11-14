import GRAssembly.Strengthening.AnalyticalFrontier.WienerElementaryFoundation
import SingularClosure.TorusSobolev
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
The fixed unweighted Fourier-Wiener carrier used for the complex-time
contraction. This module contains no nonlinear NSE estimate.
-/

set_option autoImplicit false
set_option Elab.async true

open SingularClosure
open scoped ENNReal

namespace NSEGR.Strengthening
noncomputable section

/-- Complex scalar Fourier coefficients with absolutely summable norm. -/
abbrev AnalyticalWienerSequence :=
  lp (fun _ : FourierIndex => ℂ) 1

theorem analyticalWienerSequence_complete :
    CompleteSpace AnalyticalWienerSequence := by
  infer_instance

/-- Coordinate evaluation on the fixed `ℓ¹` Wiener carrier. -/
def analyticalWienerEval (ki : FourierIndex) :
    AnalyticalWienerSequence →L[ℂ] ℂ :=
  lp.evalCLM (𝕜 := ℂ) (E := fun _ : FourierIndex => ℂ)
    (p := (1 : ℝ≥0∞)) ki

@[simp]
theorem analyticalWienerEval_apply
    (ki : FourierIndex) (c : AnalyticalWienerSequence) :
    analyticalWienerEval ki c = c ki := rfl

theorem analyticalWiener_eval_norm_le
    (c : AnalyticalWienerSequence) (ki : FourierIndex) :
    ‖analyticalWienerEval ki c‖ ≤ ‖c‖ := by
  exact lp.norm_apply_le_norm
    (by norm_num : (1 : ℝ≥0∞) ≠ 0) c ki

/-- One-frequency insertion into the fixed `ℓ¹` carrier. -/
def analyticalWienerSingle (ki : FourierIndex) (z : ℂ) :
    AnalyticalWienerSequence :=
  lp.single (E := fun _ : FourierIndex => ℂ) 1 ki z

@[simp]
theorem analyticalWienerSingle_norm
    (ki : FourierIndex) (z : ℂ) :
    ‖analyticalWienerSingle ki z‖ = ‖z‖ := by
  simpa only [analyticalWienerSingle] using
    (lp.norm_single (E := fun _ : FourierIndex => ℂ)
      (p := (1 : ℝ≥0∞))
      (by norm_num : (0 : ℝ≥0∞) < 1) ki z)

@[simp]
theorem analyticalWienerSingle_eval_self
    (ki : FourierIndex) (z : ℂ) :
    analyticalWienerEval ki (analyticalWienerSingle ki z) = z := by
  simp [analyticalWienerEval, analyticalWienerSingle]

/-- Exact fixed-carrier interface consumed by the nonlinear Wiener stage. -/
def ANALYTICAL_WIENER_CARRIER_CHECKPOINT : Prop :=
  CompleteSpace AnalyticalWienerSequence ∧
  (∀ (c : AnalyticalWienerSequence) (ki : FourierIndex),
    ‖analyticalWienerEval ki c‖ ≤ ‖c‖) ∧
  (∀ (ki : FourierIndex) (z : ℂ),
    ‖analyticalWienerSingle ki z‖ = ‖z‖ ∧
    analyticalWienerEval ki (analyticalWienerSingle ki z) = z)

theorem ANALYTICAL_WIENER_CARRIER_CHECKPOINT_NATIVE :
    ANALYTICAL_WIENER_CARRIER_CHECKPOINT := by
  refine ⟨analyticalWienerSequence_complete, ?_, ?_⟩
  · exact fun c ki => analyticalWiener_eval_norm_le c ki
  · exact fun ki z =>
      ⟨analyticalWienerSingle_norm ki z,
        analyticalWienerSingle_eval_self ki z⟩

end
end NSEGR.Strengthening
