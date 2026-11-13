import SingularClosure.HilbertChannels
import SingularClosure.TorusSobolev

/-!
# Realization of actual Fourier Sobolev coefficients in physical torus L²

The measure is the normalized Haar measure used by `HilbertChannels`.
Square-summable coefficient vectors are separated into their three scalar
components and synthesized with Mathlib's concrete exponential Hilbert basis.
Fourier agreement and the physical L² isometry are proved, not assumed.
No compactness, nonlinear equation, or strong-solution endpoint is asserted.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory
open scoped BigOperators ENNReal lp

namespace SingularClosure

noncomputable section

local instance sobolevRealizationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance sobolevRealizationHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance sobolevRealizationProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fourierVectorSequence_summable_sq (c : FourierVectorSequence) :
    Summable (fun ki : FourierIndex => ‖c ki‖ ^ 2) := by
  have h := (lp.memℓp c).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- The component sequence is square summable by restriction to one product fiber. -/
def fourierVectorComponent (c : FourierVectorSequence) (i : Fin 3) : FourierSequenceL2 :=
  ⟨fun k => c (k, i), by
    apply memℓp_gen
    have h := (lp.memℓp c).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [Function.comp_def] using!
      (h.comp_injective (i := fun k : Frequency => (k, i))
        (fun k l hkl => congrArg Prod.fst hkl))⟩

@[simp]
theorem fourierVectorComponent_apply (c : FourierVectorSequence) (i : Fin 3)
    (k : Frequency) : fourierVectorComponent c i k = c (k, i) := rfl

theorem fourierVectorComponent_add (c d : FourierVectorSequence) (i : Fin 3) :
    fourierVectorComponent (c + d) i =
      fourierVectorComponent c i + fourierVectorComponent d i := by
  apply lp.ext
  funext k
  rfl

theorem fourierVectorComponent_smul (z : ℂ) (c : FourierVectorSequence) (i : Fin 3) :
    fourierVectorComponent (z • c) i = z • fourierVectorComponent c i := by
  apply lp.ext
  funext k
  rfl

theorem fourierVectorComponent_norm_sq (c : FourierVectorSequence) (i : Fin 3) :
    ‖fourierVectorComponent c i‖ ^ 2 = ∑' k : Frequency, ‖c (k, i)‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (fourierVectorComponent c i)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fourierVectorComponent_apply] using h

theorem fourierVectorComponent_sum_norm_sq (c : FourierVectorSequence) :
    (∑ i : Fin 3, ‖fourierVectorComponent c i‖ ^ 2) = ‖c‖ ^ 2 := by
  have hs : Summable (Function.uncurry (fun k i => ‖c (k, i)‖ ^ 2)) :=
    fourierVectorSequence_summable_sq c
  calc
    _ = ∑ i : Fin 3, ∑' k : Frequency, ‖c (k, i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact fourierVectorComponent_norm_sq c i
    _ = ∑' i : Fin 3, ∑' k : Frequency, ‖c (k, i)‖ ^ 2 := (tsum_fintype _).symm
    _ = ∑' k : Frequency, ∑' i : Fin 3, ‖c (k, i)‖ ^ 2 := hs.tsum_comm
    _ = ∑' ki : FourierIndex, ‖c ki‖ ^ 2 := hs.tsum_prod.symm
    _ = ‖c‖ ^ 2 := by
      have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) c
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h.symm

/-- Actual inverse Fourier synthesis into normalized physical torus L². -/
def fourierVectorL2Synthesis (c : FourierVectorSequence) : TorusVectorL2 :=
  WithLp.toLp 2 (fun i =>
    UnitAddTorus.mFourierBasis.repr.symm (fourierVectorComponent c i))

@[simp]
theorem fourierVectorL2Synthesis_repr (c : FourierVectorSequence) (i : Fin 3) :
    UnitAddTorus.mFourierBasis.repr (fourierVectorL2Synthesis c i) =
      fourierVectorComponent c i :=
  UnitAddTorus.mFourierBasis.repr.apply_symm_apply _

theorem fourierVectorL2Synthesis_add (c d : FourierVectorSequence) :
    fourierVectorL2Synthesis (c + d) =
      fourierVectorL2Synthesis c + fourierVectorL2Synthesis d := by
  apply PiLp.ext
  intro i
  change UnitAddTorus.mFourierBasis.repr.symm (fourierVectorComponent (c + d) i) =
    UnitAddTorus.mFourierBasis.repr.symm (fourierVectorComponent c i) +
      UnitAddTorus.mFourierBasis.repr.symm (fourierVectorComponent d i)
  rw [fourierVectorComponent_add, map_add]

theorem fourierVectorL2Synthesis_smul (z : ℂ) (c : FourierVectorSequence) :
    fourierVectorL2Synthesis (z • c) = z • fourierVectorL2Synthesis c := by
  apply PiLp.ext
  intro i
  change UnitAddTorus.mFourierBasis.repr.symm (fourierVectorComponent (z • c) i) =
    z • UnitAddTorus.mFourierBasis.repr.symm (fourierVectorComponent c i)
  rw [fourierVectorComponent_smul, map_smul]

theorem fourierVectorL2Synthesis_norm_sq (c : FourierVectorSequence) :
    ‖fourierVectorL2Synthesis c‖ ^ 2 = ‖c‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ = ∑ i : Fin 3, ‖fourierVectorComponent c i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have h := UnitAddTorus.mFourierBasis.repr.symm.norm_map (fourierVectorComponent c i)
      exact congrArg (fun r : ℝ => r ^ 2) h
    _ = _ := fourierVectorComponent_sum_norm_sq c

theorem fourierVectorL2Synthesis_norm (c : FourierVectorSequence) :
    ‖fourierVectorL2Synthesis c‖ = ‖c‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (fourierVectorL2Synthesis_norm_sq c)

def fourierVectorL2Isometry : FourierVectorSequence →ₗᵢ[ℂ] TorusVectorL2 where
  toFun := fourierVectorL2Synthesis
  map_add' := fourierVectorL2Synthesis_add
  map_smul' := fourierVectorL2Synthesis_smul
  norm_map' := fourierVectorL2Synthesis_norm

/-- Actual Fourier coefficients of the synthesized L² representative. -/
theorem fourierVectorL2Synthesis_fourierCoeff (c : FourierVectorSequence)
    (k : Frequency) (i : Fin 3) :
    torusVectorFourierCoeff (fourierVectorL2Synthesis c) k i = c (k, i) := by
  change UnitAddTorus.mFourierCoeff (fourierVectorL2Synthesis c i) k = _
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact congrArg (fun a : FourierSequenceL2 => a k) (fourierVectorL2Synthesis_repr c i)

/-- Isometric physical realization of the concrete order-zero Sobolev space. -/
def torusSobolevL2 : TorusSobolev 0 →ₗᵢ[ℂ] TorusVectorL2 :=
  fourierVectorL2Isometry.comp (torusSobolevRepr 0).toLinearIsometry

theorem torusSobolevL2_fourierCoeff (c : TorusSobolev 0) :
    torusVectorFourierCoeff (torusSobolevL2 c) = c.val := by
  funext k i
  change torusVectorFourierCoeff
    (fourierVectorL2Synthesis (torusSobolevRepr 0 c)) k i = c.val k i
  rw [fourierVectorL2Synthesis_fourierCoeff, torusSobolevRepr_apply]
  simp

theorem torusSobolevL2_norm (c : TorusSobolev 0) :
    ‖torusSobolevL2 c‖ = ‖c‖ := torusSobolevL2.norm_map c

theorem torusSobolevL2_isometry : Isometry torusSobolevL2 := torusSobolevL2.isometry

/-- Fourier agreement identifies an existing physical L² field uniquely. -/
theorem torusSobolevL2_eq_of_fourierCoeff (c : TorusSobolev 0) (u : TorusVectorL2)
    (hu : torusVectorFourierCoeff u = c.val) : torusSobolevL2 c = u := by
  apply torusVectorFourierCoeff_injective
  rw [torusSobolevL2_fourierCoeff, hu]

end

end SingularClosure
