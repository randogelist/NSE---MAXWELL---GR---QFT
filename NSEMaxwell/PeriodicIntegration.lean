import NSEMaxwell.CurlCurl

/-!
# Periodic derivatives and exact cube integrals

The coordinate-periodicity lemmas use the total Mathlib Frechet derivative.
The integral of a periodic coordinate derivative is obtained from Mathlib's
Bochner divergence theorem, transported by the volume-preserving PiLp map.
No Fourier inversion or PDE identity is a premise.
-/

set_option autoImplicit false

namespace NSEMaxwell.PeriodicIntegration

open NSEMaxwell.Classical NSEMaxwell.CurlCurl
open Set MeasureTheory
open scoped BigOperators ContDiff

noncomputable section

theorem fderiv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec → E} (hp : SpatialPeriodic f) : SpatialPeriodic (fderiv ℝ f) := by
  intro x i
  have hfun : (fun y : Vec => f (y + unitVector i)) = f := funext (fun y => hp y i)
  rw [← fderiv_comp_add_right (unitVector i), hfun]

theorem coordinateDerivative_periodic {a : Field} (hp : SpatialPeriodic a)
    (i : Fin 3) : SpatialPeriodic (coordinateDerivative a i) := by
  intro x j
  exact congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector i)) (fderiv_periodic hp x j)

theorem spatialCurl_periodic {a : Field} (hp : SpatialPeriodic a) :
    SpatialPeriodic (spatialCurl a) := by
  intro x j
  have h0 := coordinateDerivative_periodic hp 0 x j
  have h1 := coordinateDerivative_periodic hp 1 x j
  have h2 := coordinateDerivative_periodic hp 2 x j
  ext i
  fin_cases i <;> simp [spatialCurl, PiLp.toLp_apply, h0, h1, h2]

theorem divergence_periodic {a : Field} (hp : SpatialPeriodic a) :
    SpatialPeriodic (NSEMaxwell.Classical.divergence a) := by
  intro x j
  unfold NSEMaxwell.Classical.divergence
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun v : Vec => v i) (coordinateDerivative_periodic hp i x j)

theorem gradient_periodic {f : ScalarField} (hp : SpatialPeriodic f) :
    SpatialPeriodic (NSEMaxwell.Classical.gradient f) := by
  intro x j
  ext i
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) (fderiv_periodic hp x j)

theorem laplacian_periodic {a : Field} (hp : SpatialPeriodic a) :
    SpatialPeriodic (NSEMaxwell.Classical.laplacian a) := by
  intro x j
  unfold NSEMaxwell.Classical.laplacian
  apply Finset.sum_congr rfl
  intro i hi
  exact coordinateDerivative_periodic (coordinateDerivative_periodic hp i) i x j

private abbrev PiVec := Fin 3 → ℝ

private def piToVec : PiVec ≃L[ℝ] Vec :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm

private theorem piToVec_preimage_cube :
    piToVec ⁻¹' unitCube = Icc (0 : PiVec) 1 := by
  ext x
  change (∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1) ↔
    ((∀ i : Fin 3, 0 ≤ x i) ∧ ∀ i : Fin 3, x i ≤ 1)
  exact forall_and

theorem integrableOn_unitCube_of_continuous
    {E : Type*} [NormedAddCommGroup E] {f : Vec → E} (hf : Continuous f) :
    IntegrableOn f unitCube := by
  have hm : MeasurePreserving piToVec := PiLp.volume_preserving_toLp (Fin 3)
  apply (hm.integrableOn_comp_preimage piToVec.toHomeomorph.measurableEmbedding).mp
  rw [piToVec_preimage_cube]
  exact (hf.comp piToVec.continuous).integrableOn_Icc

private theorem insertNth_front_eq_back_add (i : Fin 3) (y : Fin 2 → ℝ) :
    i.insertNth (1 : ℝ) y = i.insertNth (0 : ℝ) y + Pi.single i 1 := by
  have h : i.insertNth (1 : ℝ) y - i.insertNth (0 : ℝ) y = Pi.single i 1 := by
    simpa using Fin.insertNth_sub_same (α := fun _ : Fin 3 => ℝ) i 1 0 y
  calc
    i.insertNth (1 : ℝ) y =
        (i.insertNth (1 : ℝ) y - i.insertNth (0 : ℝ) y) +
          i.insertNth (0 : ℝ) y := (sub_add_cancel _ _).symm
    _ = Pi.single i 1 + i.insertNth (0 : ℝ) y := by rw [h]
    _ = i.insertNth (0 : ℝ) y + Pi.single i 1 := add_comm _ _

/-- The scalar-coordinate FTC, with arbitrary complete vector-valued output. -/
private theorem pi_integral_coordinateDerivative_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : PiVec → E) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ (x : PiVec) (i : Fin 3), f (x + Pi.single i 1) = f x)
    (i : Fin 3) :
    (∫ x in Icc (0 : PiVec) 1, fderiv ℝ f x (Pi.single i 1)) = 0 := by
  let F : Fin 3 → PiVec → E := fun j => if j = i then f else 0
  let F' : Fin 3 → PiVec → PiVec →L[ℝ] E :=
    fun j => if j = i then fderiv ℝ f else 0
  have hsum (x : PiVec) :
      (∑ j : Fin 3, F' j x (Pi.single j 1)) = fderiv ℝ f x (Pi.single i 1) := by
    simp [F']
  have hcont : ∀ j, ContinuousOn (F j) (Icc (0 : PiVec) 1) := by
    intro j
    by_cases hji : j = i
    · simpa [F, hji] using hf.continuous.continuousOn
    · simp only [F, if_neg hji]
      exact continuous_zero.continuousOn
  have hderiv : ∀ x ∈ (Set.pi Set.univ fun _ : Fin 3 => Ioo (0 : ℝ) 1) \ ∅,
      ∀ j, HasFDerivAt (F j) (F' j x) x := by
    intro x hx j
    by_cases hji : j = i
    · simpa [F, F', hji] using (hf.differentiable (by simp) x).hasFDerivAt
    · simp only [F, F', if_neg hji, Pi.zero_apply]
      exact hasFDerivAt_const (0 : E) x
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hint : IntegrableOn
      (fun x => ∑ j : Fin 3, F' j x (Pi.single j 1)) (Icc (0 : PiVec) 1) := by
    simp only [hsum]
    exact (hdf.continuous.clm_apply continuous_const).integrableOn_Icc
  have hd := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
    (0 : PiVec) 1 (by intro j; norm_num) F F' ∅ Set.countable_empty
    hcont hderiv hint
  have hfaces (j : Fin 3) :
      (fun y : Fin 2 → ℝ => F j (j.insertNth (1 : ℝ) y)) =
        (fun y : Fin 2 → ℝ => F j (j.insertNth (0 : ℝ) y)) := by
    funext y
    by_cases hji : j = i
    · subst j
      simp only [F, if_pos rfl]
      rw [insertNth_front_eq_back_add]
      exact hp _ _
    · simp [F, hji]
  have hr : (∑ j : Fin 3,
      ((∫ y in Icc ((0 : PiVec) ∘ j.succAbove) ((1 : PiVec) ∘ j.succAbove),
          F j (j.insertNth (1 : ℝ) y)) -
        ∫ y in Icc ((0 : PiVec) ∘ j.succAbove) ((1 : PiVec) ∘ j.succAbove),
          F j (j.insertNth (0 : ℝ) y))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hfaces j, sub_self]
  simpa only [hsum] using hd.trans hr

/-- Every smooth periodic coordinate derivative has exactly zero cube mean. -/
theorem spatialMean_coordinateDerivative_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i : Fin 3) :
    spatialMean (coordinateDerivative a i) = 0 := by
  let f : PiVec → Vec := fun x => a (piToVec x)
  have hf : ContDiff ℝ ∞ f := ha.comp piToVec.contDiff
  have hp' : ∀ (x : PiVec) (j : Fin 3), f (x + Pi.single j 1) = f x := by
    intro x j
    change a (piToVec (x + Pi.single j 1)) = a (piToVec x)
    rw [map_add]
    exact hp (piToVec x) j
  have hdf (x : PiVec) :
      fderiv ℝ f x (Pi.single i 1) = coordinateDerivative a i (piToVec x) := by
    have hd := ((ha.differentiable (by simp) (piToVec x)).hasFDerivAt.comp x
      piToVec.hasFDerivAt).fderiv
    exact congrArg (fun L : PiVec →L[ℝ] Vec => L (Pi.single i 1)) hd
  have hzero := pi_integral_coordinateDerivative_zero f hf hp' i
  simp only [hdf] at hzero
  have hm : MeasurePreserving piToVec := PiLp.volume_preserving_toLp (Fin 3)
  have hchange := hm.setIntegral_preimage_emb
    piToVec.toHomeomorph.measurableEmbedding (coordinateDerivative a i) unitCube
  rw [piToVec_preimage_cube] at hchange
  exact hchange.symm.trans hzero

theorem spatialMean_apply {a : Field} (ha : Continuous a) (i : Fin 3) :
    spatialMean a i = ∫ x in unitCube, a x i := by
  exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (𝕜 := ℝ) i).integral_comp_comm
    (integrableOn_unitCube_of_continuous ha)).symm

theorem integral_coordinate_component_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i j : Fin 3) :
    (∫ x in unitCube, coordinateDerivative a i x j) = 0 := by
  rw [← spatialMean_apply (coordinateDerivative_smooth ha i).continuous j,
    spatialMean_coordinateDerivative_zero ha hp i]
  rfl

/-- The vorticity of a smooth periodic velocity has zero spatial mean. -/
theorem spatialMean_curl_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    spatialMean (spatialCurl a) = 0 := by
  have hi (i j : Fin 3) : IntegrableOn
      (fun x => coordinateDerivative a i x j) unitCube :=
    integrableOn_unitCube_of_continuous (coordinate_component_smooth ha i j).continuous
  ext k
  rw [spatialMean_apply (spatialCurl_smooth ha).continuous k]
  fin_cases k <;>
    simp only [spatialCurl, PiLp.toLp_apply, Fin.reduceFinMk, ↓reduceIte]
  · rw [integral_sub (hi 1 2) (hi 2 1),
      integral_coordinate_component_zero ha hp, integral_coordinate_component_zero ha hp]
    rfl
  · rw [integral_sub (hi 2 0) (hi 0 2),
      integral_coordinate_component_zero ha hp, integral_coordinate_component_zero ha hp]
    rfl
  · rw [integral_sub (hi 0 1) (hi 1 0),
      integral_coordinate_component_zero ha hp, integral_coordinate_component_zero ha hp]
    rfl

end

end NSEMaxwell.PeriodicIntegration
