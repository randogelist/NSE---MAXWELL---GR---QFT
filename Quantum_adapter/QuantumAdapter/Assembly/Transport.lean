import QuantumAdapter.Dynamics
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Actual phase transport from differentiability and its determinant identity.
The remaining premises are stated on the native time maps, not on integrals
or L2 transport. No existence of a differentiable complete flow is inferred.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory

namespace QuantumAdapter.Assembly

noncomputable section

variable {ν : ℝ}

theorem phaseFlow_timeMap_inverse (F : PhaseFlow ν) (N : ℕ) (t : ℝ)
    (q : Phase N) : F.map N (-t) (F.map N t q) = q := by
  rw [← F.map_add, neg_add_cancel, F.map_zero]

theorem phaseFlow_timeMap_bijective (F : PhaseFlow ν) (N : ℕ) (t : ℝ) :
    Function.Bijective (F.map N t) := by
  constructor
  · intro q r h
    have he := congrArg (F.map N (-t)) h
    simpa only [phaseFlow_timeMap_inverse] using he
  · intro q
    refine ⟨F.map N (-t) q, ?_⟩
    rw [← F.map_add, add_neg_cancel, F.map_zero]

def phaseFlow_timeHomeomorph (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t)) (N : ℕ) (t : ℝ) :
    Phase N ≃ₜ Phase N where
  toFun := F.map N t
  invFun := F.map N (-t)
  left_inv := phaseFlow_timeMap_inverse F N t
  right_inv := by
    intro q
    rw [← F.map_add, add_neg_cancel, F.map_zero]
  continuous_toFun := (hd N t).continuous
  continuous_invFun := (hd N (-t)).continuous

theorem phaseFlow_preimage_eq_inverse_image (F : PhaseFlow ν) (N : ℕ)
    (t : ℝ) (s : Set (Phase N)) :
    (F.map N t) ⁻¹' s = (F.map N (-t)) '' s := by
  ext q
  constructor
  · intro hq
    exact ⟨F.map N t q, hq, phaseFlow_timeMap_inverse F N t q⟩
  · rintro ⟨r, hr, rfl⟩
    simpa only [Set.mem_preimage, ← F.map_add, add_neg_cancel, F.map_zero] using hr

theorem phaseFlow_quasiMeasurePreserving (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t)) (N : ℕ) (t : ℝ) :
    QuasiMeasurePreserving (F.map N t) (phaseVolume N) (phaseVolume N) := by
  letI : (phaseVolume N).IsAddHaarMeasure := by
    unfold phaseVolume
    infer_instance
  refine ⟨(hd N t).continuous.measurable, ?_⟩
  intro s hs
  have hm : MeasurableEmbedding (F.map N t) :=
    (phaseFlow_timeHomeomorph F hd N t).toMeasurableEquiv.measurableEmbedding
  rw [hm.map_apply, phaseFlow_preimage_eq_inverse_image]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    (phaseVolume N) (hd N (-t)).differentiableOn hs

theorem phaseFlow_integralPullbackLaw_of_jacobian (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t)) (N : ℕ) :
    IntegralPullbackLaw (phaseVolume N) (phaseDecayRate ν N) (F.map N) := by
  letI : (phaseVolume N).IsAddHaarMeasure := by
    unfold phaseVolume
    infer_instance
  intro t f _hf
  have hder : ∀ q ∈ (Set.univ : Set (Phase N)),
      HasFDerivWithinAt (F.map N (-t))
        (fderiv ℝ (F.map N (-t)) q) Set.univ q := by
    intro q _
    exact (hd N (-t) q).hasFDerivAt.hasFDerivWithinAt
  have himage : F.map N (-t) '' Set.univ = Set.univ :=
    Set.image_univ.mpr (phaseFlow_timeMap_bijective F N (-t)).2
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (phaseVolume N) MeasurableSet.univ hder
    (phaseFlow_timeMap_bijective F N (-t)).1.injOn f
  have hdet' (q : Phase N) :
      |(fderiv ℝ (F.map N (-t)) q).det| = Real.exp (phaseDecayRate ν N * t) := by
    rw [hdet, neg_mul_neg, abs_of_pos (Real.exp_pos _)]
  simpa only [himage, integral_univ, hdet', smul_eq_mul] using hchange.symm

theorem phaseFlow_integrable_weighted_comp_of_jacobian (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t)) (N : ℕ) (t : ℝ)
    (f : Phase N → ℝ) (hf : Integrable f (phaseVolume N)) :
    Integrable (fun q => Real.exp (phaseDecayRate ν N * t) *
      f (F.map N (-t) q)) (phaseVolume N) := by
  letI : (phaseVolume N).IsAddHaarMeasure := by
    unfold phaseVolume
    infer_instance
  have hder : ∀ q ∈ (Set.univ : Set (Phase N)),
      HasFDerivWithinAt (F.map N (-t))
        (fderiv ℝ (F.map N (-t)) q) Set.univ q := by
    intro q _
    exact (hd N (-t) q).hasFDerivAt.hasFDerivWithinAt
  have himage : F.map N (-t) '' Set.univ = Set.univ :=
    Set.image_univ.mpr (phaseFlow_timeMap_bijective F N (-t)).2
  have hchange := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (phaseVolume N) MeasurableSet.univ hder
    (phaseFlow_timeMap_bijective F N (-t)).1.injOn f
  have hdet' (q : Phase N) :
      |(fderiv ℝ (F.map N (-t)) q).det| = Real.exp (phaseDecayRate ν N * t) := by
    rw [hdet, neg_mul_neg, abs_of_pos (Real.exp_pos _)]
  have hf' : IntegrableOn f (F.map N (-t) '' Set.univ) (phaseVolume N) := by
    simpa only [himage, integrableOn_univ] using hf
  simpa only [hdet', smul_eq_mul, integrableOn_univ] using hchange.mp hf'

theorem phaseFlow_memLpPullbackLaw_of_jacobian (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t)) (N : ℕ) :
    MemLpPullbackLaw (phaseVolume N) (phaseDecayRate ν N) (F.map N) := by
  intro t ψ hψ
  have hmeas := (hψ.aestronglyMeasurable.comp_quasiMeasurePreserving
    (phaseFlow_quasiMeasurePreserving F hd N (-t))).const_mul
      (Real.exp (phaseDecayRate ν N * t / 2) : ℂ)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hsq : Integrable (fun q => ‖ψ q‖ ^ 2) (phaseVolume N) :=
    (memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).1 hψ
  have hw := phaseFlow_integrable_weighted_comp_of_jacobian F hd hdet N t _ hsq
  convert hw using 1
  funext q
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  exact bornDensity_halfDensityPullback _ _ _ _ _

theorem phaseTransportLaws_of_jacobian (F : PhaseFlow ν)
    (hd : ∀ N t, Differentiable ℝ (F.map N t))
    (hdet : ∀ N t q, (fderiv ℝ (F.map N t) q).det =
      Real.exp (-(phaseDecayRate ν N) * t)) :
    PhaseTransportLaws F :=
  ⟨phaseFlow_integralPullbackLaw_of_jacobian F hd hdet,
    phaseFlow_memLpPullbackLaw_of_jacobian F hd hdet⟩

end
end QuantumAdapter.Assembly
