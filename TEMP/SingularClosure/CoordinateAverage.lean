import SingularClosure.Contracts

/-!
# Actual coordinate averages of periodic lifts

The averaging variable replaces one coordinate and is integrated over the
unit interval with Lebesgue measure. This module gives concrete physical
averaging operators and their elementary projection identities. No Fourier
identification, cross-coordinate derivative interchange or smoothness theorem
for the average is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

def resetCoordinate (j : Fin 3) (s : ℝ) (x : Vec) : Vec :=
  WithLp.toLp 2 (fun i => if i = j then s else x i)

@[simp]
theorem resetCoordinate_apply (j : Fin 3) (s : ℝ) (x : Vec) (i : Fin 3) :
    resetCoordinate j s x i = if i = j then s else x i := rfl

@[simp]
theorem resetCoordinate_twice (j : Fin 3) (s t : ℝ) (x : Vec) :
    resetCoordinate j s (resetCoordinate j t x) = resetCoordinate j s x := by
  ext i
  by_cases h : i = j <;> simp [h]

theorem resetCoordinate_commute (i j : Fin 3) (hij : i ≠ j)
    (s t : ℝ) (x : Vec) :
    resetCoordinate i s (resetCoordinate j t x) =
      resetCoordinate j t (resetCoordinate i s x) := by
  ext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

theorem resetCoordinate_smooth (j : Fin 3) :
    ContDiff ℝ ∞ (fun z : Vec × ℝ => resetCoordinate j z.2 z.1) := by
  apply (contDiff_piLp 2).2
  intro i
  by_cases h : i = j
  · simpa [h] using (contDiff_snd : ContDiff ℝ ∞ (fun z : Vec × ℝ => z.2))
  · have hc : ContDiff ℝ ∞ (fun z : Vec × ℝ => z.1 i) := by fun_prop
    simpa [h] using hc

theorem resetCoordinate_continuous_slice (j : Fin 3) (x : Vec) :
    Continuous (fun s : ℝ => resetCoordinate j s x) := by
  exact (resetCoordinate_smooth j).continuous.comp (continuous_const.prodMk continuous_id)

def coordinateAverage (j : Fin 3) (a : Field) : Field :=
  fun x => ∫ s in Icc (0 : ℝ) 1, a (resetCoordinate j s x)

theorem coordinateAverage_slice_integrable (j : Fin 3) (a : Field)
    (ha : Continuous a) (x : Vec) :
    IntegrableOn (fun s : ℝ => a (resetCoordinate j s x)) (Icc (0 : ℝ) 1) volume :=
  (ha.comp (resetCoordinate_continuous_slice j x)).continuousOn.integrableOn_compact
    isCompact_Icc

theorem coordinateAverage_continuous (j : Fin 3) (a : Field)
    (ha : Continuous a) : Continuous (coordinateAverage j a) := by
  apply continuous_parametric_integral_of_continuous
    (f := fun x s => a (resetCoordinate j s x)) ?_ isCompact_Icc
  exact ha.comp (resetCoordinate_smooth j).continuous

theorem coordinateAverage_reset (j : Fin 3) (a : Field) (t : ℝ) (x : Vec) :
    coordinateAverage j a (resetCoordinate j t x) = coordinateAverage j a x := by
  simp only [coordinateAverage, resetCoordinate_twice]

theorem coordinateAverage_idempotent (j : Fin 3) (a : Field) :
    coordinateAverage j (coordinateAverage j a) = coordinateAverage j a := by
  funext x
  change (∫ s in Icc (0 : ℝ) 1,
    coordinateAverage j a (resetCoordinate j s x)) = coordinateAverage j a x
  simp only [coordinateAverage_reset]
  simp

theorem coordinateAverage_zero (j : Fin 3) : coordinateAverage j (0 : Field) = 0 := by
  funext x
  simp [coordinateAverage]

theorem coordinateAverage_add (j : Fin 3) (a b : Field)
    (ha : Continuous a) (hb : Continuous b) :
    coordinateAverage j (a + b) = coordinateAverage j a + coordinateAverage j b := by
  funext x
  exact integral_add (coordinateAverage_slice_integrable j a ha x)
    (coordinateAverage_slice_integrable j b hb x)

theorem coordinateAverage_smul (j : Fin 3) (r : ℝ) (a : Field) :
    coordinateAverage j (r • a) = r • coordinateAverage j a := by
  funext x
  exact integral_smul r (fun s : ℝ => a (resetCoordinate j s x))

theorem resetCoordinate_add_own_direction (j : Fin 3) (s t : ℝ) (x : Vec) :
    resetCoordinate j s (x + t • unitVector j) = resetCoordinate j s x := by
  ext i
  by_cases h : i = j
  · simp [h]
  · simp [h, unitVector]

theorem coordinateAverage_direction_invariant (j : Fin 3) (a : Field) (t : ℝ) (x : Vec) :
    coordinateAverage j a (x + t • unitVector j) = coordinateAverage j a x := by
  simp only [coordinateAverage, resetCoordinate_add_own_direction]

theorem resetCoordinate_add_other_direction (i j : Fin 3) (hij : i ≠ j)
    (s : ℝ) (x : Vec) :
    resetCoordinate j s (x + unitVector i) = resetCoordinate j s x + unitVector i := by
  ext k
  by_cases hkj : k = j
  · subst k
    simp [unitVector, Ne.symm hij]
  · simp [hkj]

theorem coordinateAverage_periodic (j : Fin 3) (a : Field)
    (ha : SpatialPeriodic a) : SpatialPeriodic (coordinateAverage j a) := by
  intro x i
  by_cases hij : i = j
  · subst i
    simpa using coordinateAverage_direction_invariant j a 1 x
  · unfold coordinateAverage
    apply integral_congr_ae
    filter_upwards with s
    rw [resetCoordinate_add_other_direction i j hij, ha]

/-- The literal Fréchet derivative annihilates the averaged coordinate. -/
theorem coordinateAverage_own_coordinateDerivative_zero (j : Fin 3) (a : Field)
    (x : Vec) : coordinateDerivative (coordinateAverage j a) j x = 0 := by
  by_cases hd : DifferentiableAt ℝ (coordinateAverage j a) x
  · have hl : HasDerivAt (fun t : ℝ => x + t • unitVector j) (unitVector j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (unitVector j)).const_add x
    have hc := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
    have hfun : (fun t : ℝ => coordinateAverage j a (x + t • unitVector j)) =
        (fun _ : ℝ => coordinateAverage j a x) := by
      funext t
      exact coordinateAverage_direction_invariant j a t x
    have hc' : HasDerivAt (fun _ : ℝ => coordinateAverage j a x)
        (fderiv ℝ (coordinateAverage j a) x (unitVector j)) 0 := by
      simpa only [Function.comp_def, zero_smul, add_zero, hfun] using hc
    exact hc'.unique (hasDerivAt_const 0 _)
  · simp only [coordinateDerivative, fderiv_zero_of_not_differentiableAt hd,
      ContinuousLinearMap.zero_apply]

end

end SingularClosure
