import QuantumAdapter.Assembly.Galerkin
import Mathlib

/-! Generic spatial differentiation on the closed forward halfspace. -/
set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
namespace QuantumAdapter.Obligations
open SingularClosure QuantumAdapter.Assembly
noncomputable section

theorem uniqueDiffOn_forwardSpacetime : UniqueDiffOn ℝ forwardSpacetime := by
  have heq : forwardSpacetime = (Ici (0 : ℝ)) ×ˢ (univ : Set Vec) := by
    ext z
    simp [forwardSpacetime]
  rw [heq]
  exact (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ

/-- Spatial differentiation of a joint field within the closed forward domain. -/
def forwardSpatialDerivative (F : (ℝ × Vec) → Vec) (j : Fin 3) (z : ℝ × Vec) : Vec :=
  fderivWithin ℝ F forwardSpacetime z (0, unitVector j)

theorem forwardSpatialDerivative_smooth {F : (ℝ × Vec) → Vec}
    (hF : ContDiffOn ℝ ∞ F forwardSpacetime) (j : Fin 3) :
    ContDiffOn ℝ ∞ (forwardSpatialDerivative F j) forwardSpacetime := by
  exact (hF.fderivWithin uniqueDiffOn_forwardSpacetime (by simp)).clm_apply contDiffOn_const

/-- Restricting a joint spatial derivative gives the ordinary full slice derivative. -/
theorem forwardSpatialDerivative_slice {F : (ℝ × Vec) → Vec}
    (hF : ContDiffOn ℝ ∞ F forwardSpacetime) (j : Fin 3)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    forwardSpatialDerivative F j (t, x) =
      coordinateDerivative (fun y : Vec => F (t, y)) j x := by
  have hd := (hF.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt
  have hi := (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hc := hd.comp_hasFDerivAt x hi (Eventually.of_forall (fun _ => ht))
  have he := congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector j)) hc.fderiv
  simpa only [forwardSpatialDerivative, coordinateDerivative, Function.comp_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply] using! he.symm

def forwardIteratedSpatialDerivative (j : Fin 3) :
    ℕ → ((ℝ × Vec) → Vec) → ((ℝ × Vec) → Vec)
  | 0, F => F
  | m + 1, F => forwardSpatialDerivative (forwardIteratedSpatialDerivative j m F) j

theorem forwardIteratedSpatialDerivative_smooth {F : (ℝ × Vec) → Vec}
    (hF : ContDiffOn ℝ ∞ F forwardSpacetime) (j : Fin 3) (m : ℕ) :
    ContDiffOn ℝ ∞ (forwardIteratedSpatialDerivative j m F) forwardSpacetime := by
  induction m with
  | zero => exact hF
  | succ m ih => exact forwardSpatialDerivative_smooth ih j

theorem forwardIteratedSpatialDerivative_slice {F : (ℝ × Vec) → Vec}
    (hF : ContDiffOn ℝ ∞ F forwardSpacetime) (j : Fin 3) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    forwardIteratedSpatialDerivative j m F (t, x) =
      iteratedCoordinateDerivative j m (fun y : Vec => F (t, y)) x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [forwardIteratedSpatialDerivative,
      forwardSpatialDerivative_slice (forwardIteratedSpatialDerivative_smooth hF j m) j t ht]
    have heq : (fun y : Vec => forwardIteratedSpatialDerivative j m F (t, y)) =
        iteratedCoordinateDerivative j m (fun y : Vec => F (t, y)) := by
      funext y
      exact ih y
    rw [heq]
    rfl

end
end QuantumAdapter.Obligations
