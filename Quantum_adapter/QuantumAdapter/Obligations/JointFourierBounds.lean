import QuantumAdapter.Obligations.ForwardSpatial
import QuantumAdapter.Obligations.GalerkinSmoothTime

/-! Uniform Fourier decay of any actual jointly smooth forward periodic field. -/
set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations
open SingularClosure QuantumAdapter.Assembly
open NSEMaxwell.Classical (SmoothVelocity)
noncomputable section

variable {u : Velocity}

theorem SmoothVelocity.iteratedCoordinateDerivative_continuousOn
    (h : SmoothVelocity u) (j : Fin 3) (m : ℕ) :
    ContinuousOn (fun z : ℝ × Vec => iteratedCoordinateDerivative j m (u z.1) z.2)
      forwardSpacetime := by
  apply (forwardIteratedSpatialDerivative_smooth h j m).continuousOn.congr
  intro z hz
  exact (forwardIteratedSpatialDerivative_slice h j m z.1 hz z.2).symm

theorem SmoothVelocity.exists_uniform_coordinateDerivativeL1
    (h : SmoothVelocity u) (j : Fin 3) (m : ℕ) (i : Fin 3) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T →
      coordinateDerivativeL1 j m (u t) i ≤ C := by
  have hcont := (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
    (h.iteratedCoordinateDerivative_continuousOn j m)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_unitCube).exists_bound_of_continuousOn
    (hcont.mono (show (Icc (0 : ℝ) T) ×ˢ unitCube ⊆ forwardSpacetime from
      fun z hz => hz.1.1))
  let D : ℝ := max C 0
  refine ⟨volume.real unitCube * D, by positivity, ?_⟩
  intro t ht hT
  have hint := iteratedCoordinateDerivative_component_integrable j m (u t)
    (h.spatial_contDiff t ht) i
  have hconst : IntegrableOn (fun _ : Vec => D) unitCube volume :=
    continuousOn_const.integrableOn_compact isCompact_unitCube
  have hpoint : ∀ᵐ x ∂volume.restrict unitCube,
      ‖iteratedCoordinateDerivative j m (u t) x i‖ ≤ D := by
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    exact (hC (t, x) ⟨⟨ht, hT⟩, hx⟩).trans (le_max_left C 0)
  have hle := integral_mono_ae hint hconst hpoint
  simpa only [coordinateDerivativeL1, setIntegral_const, smul_eq_mul] using hle

theorem SmoothVelocity.exists_uniform_fourierDecayConstant
    (h : SmoothVelocity u) (m : ℕ) (T : ℝ) :
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

theorem SmoothVelocity.exists_uniform_smoothDatumDecayConstant
    (h : SmoothVelocity u) (s : ℕ) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T →
      smoothDatumDecayConstant s (u t) ≤ C := by
  obtain ⟨C, hC, hb⟩ := h.exists_uniform_fourierDecayConstant (2 * (s + 2)) T
  refine ⟨(4 : ℝ) ^ (s + 2) * C, mul_nonneg (by positivity) hC, ?_⟩
  intro t ht hT
  exact mul_le_mul_of_nonneg_left (hb t ht hT) (by positivity)

/-- A pointwise fourth-power lattice majorant controls every finite full-index sum. -/
theorem finite_fourierIndex_sum_le_lattice_majorant (g : FourierIndex → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hg : ∀ ki, g ki ≤ C * (torusSobolevWeight ki.1)⁻¹ ^ 4)
    (I : Finset FourierIndex) :
    (∑ ki ∈ I, g ki) ≤ 3 * C * ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4 := by
  classical
  have hsub : I ⊆ (I.image Prod.fst).product (Finset.univ : Finset (Fin 3)) := by
    intro ki hki
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨ki, hki, rfl⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ ki ∈ I, C * (torusSobolevWeight ki.1)⁻¹ ^ 4 :=
      Finset.sum_le_sum (fun ki _ => hg ki)
    _ ≤ ∑ ki ∈ (I.image Prod.fst).product (Finset.univ : Finset (Fin 3)),
        C * (torusSobolevWeight ki.1)⁻¹ ^ 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ki _ _ => by positivity)
    _ = 3 * C * ∑ k ∈ I.image Prod.fst, (torusSobolevWeight k)⁻¹ ^ 4 := by
      simp [Finset.sum_product, Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Summable.sum_le_tsum _ (fun k _ => by positivity) summable_torusSobolevWeight_inv_four)
      (by positivity)

end
end QuantumAdapter.Obligations
