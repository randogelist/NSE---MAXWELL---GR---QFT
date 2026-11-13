import QuantumAdapter.Obligations.GalerkinReference
import Mathlib

/-!
# Uniform spatial smoothness bounds for the actual reference solution

The closed time boundary is retained. Spatial derivatives are restrictions of
joint derivatives within the forward halfspace, and compactness is applied on
the literal time interval times the physical unit cube.
-/

set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly NSEMaxwell.Classical

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
  have hi := (hasFDerivAt_const x t).prodMk (hasFDerivAt_id x)
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

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

theorem NSSolution.iteratedCoordinateDerivative_continuousOn
    (h : NSSolution ν a u p) (j : Fin 3) (m : ℕ) :
    ContinuousOn (fun z : ℝ × Vec => iteratedCoordinateDerivative j m (u z.1) z.2)
      forwardSpacetime := by
  apply (forwardIteratedSpatialDerivative_smooth h.velocity_smooth j m).continuousOn.congr
  intro z hz
  exact (forwardIteratedSpatialDerivative_slice h.velocity_smooth j m z.1 hz z.2).symm

/-- Every fixed coordinate derivative has one physical L1 bound on the full time interval. -/
theorem NSSolution.exists_uniform_coordinateDerivativeL1
    (h : NSSolution ν a u p) (j : Fin 3) (m : ℕ) (i : Fin 3) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T →
      coordinateDerivativeL1 j m (u t) i ≤ C := by
  have hcont := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
    (h.iteratedCoordinateDerivative_continuousOn j m)
  have hcompact : IsCompact ((Icc (0 : ℝ) T) ×ˢ unitCube) :=
    isCompact_Icc.prod isCompact_unitCube
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hcont.mono (fun z hz => hz.1.1))
  let D : ℝ := max C 0
  refine ⟨volume.real unitCube * D, mul_nonneg (measureReal_nonneg) (le_max_right _ _), ?_⟩
  intro t ht hT
  have hint := iteratedCoordinateDerivative_component_integrable j m (u t)
    (h.spatial_data t ht).smooth i
  have hconst : IntegrableOn (fun _ : Vec => D) unitCube volume :=
    continuousOn_const.integrableOn_compact isCompact_unitCube
  have hpoint : ∀ᵐ x ∂volume.restrict unitCube,
      ‖iteratedCoordinateDerivative j m (u t) x i‖ ≤ D := by
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    exact (hC (t, x) ⟨⟨ht, hT⟩, hx⟩).trans (le_max_left C 0)
  have hle := integral_mono_ae hint hconst hpoint
  simpa only [coordinateDerivativeL1, setIntegral_const, smul_eq_mul] using hle

/-- The actual Methlib Fourier decay constant is uniformly bounded on compact time intervals. -/
theorem NSSolution.exists_uniform_fourierDecayConstant
    (h : NSSolution ν a u p) (m : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T → fourierDecayConstant m (u t) ≤ C := by
  choose C₀ hC₀ hb₀ using (fun i : Fin 3 =>
    h.exists_uniform_coordinateDerivativeL1 (0 : Fin 3) 0 i T)
  choose C hC hb using (fun j i : Fin 3 => h.exists_uniform_coordinateDerivativeL1 j m i T)
  refine ⟨∑ i : Fin 3, (C₀ i + ∑ j : Fin 3, C j i), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => add_nonneg (hC₀ i)
      (Finset.sum_nonneg (fun j _ => hC j i)))
  · intro t ht hT
    apply Finset.sum_le_sum
    intro i hi
    apply add_le_add
    · simpa only [coordinateDerivativeL1, iteratedCoordinateDerivative] using hb₀ i t ht hT
    · exact Finset.sum_le_sum (fun j _ => hb j i t ht hT)

theorem NSSolution.exists_uniform_smoothDatumDecayConstant
    (h : NSSolution ν a u p) (s : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T →
      smoothDatumDecayConstant s (u t) ≤ C := by
  obtain ⟨C, hC, hb⟩ := h.exists_uniform_fourierDecayConstant (2 * (s + 2)) T
  refine ⟨(4 : ℝ) ^ (s + 2) * C, mul_nonneg (by positivity) hC, ?_⟩
  intro t ht hT
  exact mul_le_mul_of_nonneg_left (hb t ht hT) (by positivity)

/-- The native projected reference has a single bound at every Sobolev order. -/
theorem NSSolution.exists_uniform_referenceProjection_sobolevEnergy
    (h : NSSolution ν a u p) (s : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      sobolevEnergy s N (referenceProjection h N t) ≤ C := by
  obtain ⟨C, hC, hb⟩ := h.exists_uniform_smoothDatumDecayConstant s T
  let W : ℝ := ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4
  have hW : 0 ≤ W := tsum_nonneg (fun _ => by positivity)
  refine ⟨3 * C ^ 2 * W, by positivity, ?_⟩
  intro N t ht hT
  refine (referenceProjection_sobolevEnergy_le h s N t ht).trans ?_
  apply mul_le_mul_of_nonneg_right _ hW
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  exact pow_le_pow_left₀ (smoothDatumDecayConstant_nonneg s (u t)) (hb t ht hT) 2

end
end QuantumAdapter.Obligations
