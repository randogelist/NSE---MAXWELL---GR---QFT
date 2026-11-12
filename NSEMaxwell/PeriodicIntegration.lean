import NSEMaxwell.CurlCurl
import NSEMaxwell.Lamb

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

theorem isCompact_unitCube : IsCompact unitCube := by
  have hset : unitCube = piToVec '' Icc (0 : PiVec) 1 := by
    rw [← piToVec_preimage_cube, Set.image_preimage_eq _ piToVec.surjective]
  rw [hset]
  exact isCompact_Icc.image piToVec.continuous

theorem integrableOn_unitCube_of_continuous
    {E : Type*} [NormedAddCommGroup E] {f : Vec → E} (hf : Continuous f) :
    IntegrableOn f unitCube := by
  have hm : MeasurePreserving piToVec := PiLp.volume_preserving_toLp (Fin 3)
  apply (hm.integrableOn_comp_preimage piToVec.toHomeomorph.measurableEmbedding).mp
  rw [piToVec_preimage_cube]
  exact (hf.comp piToVec.continuous).integrableOn_Icc

private theorem insertNth_front_eq_back_add (i : Fin 3) (y : Fin 2 → ℝ) :
    Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 1 y =
      Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 y + Pi.single i 1 := by
  have h : Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 1 y -
      Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 y = Pi.single i 1 := by
    simpa using Fin.insertNth_sub_same (α := fun _ : Fin 3 => ℝ) i 1 0 y
  calc
    Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 1 y =
        (Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 1 y -
          Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 y) +
            Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 y := (sub_add_cancel _ _).symm
    _ = Pi.single i 1 + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 y := by rw [h]
    _ = Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 y + Pi.single i 1 := add_comm _ _

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
    simp only [F']
    simp_rw [ite_apply]
    simp
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

/-- Exact coordinate FTC for the concrete unit cube. -/
theorem integral_fderiv_unitVector_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a : Vec → E} (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i : Fin 3) :
    (∫ x in unitCube, fderiv ℝ a x (unitVector i)) = 0 := by
  let f : PiVec → E := fun x => a (piToVec x)
  have hf : ContDiff ℝ ∞ f := ha.comp piToVec.contDiff
  have hp' : ∀ (x : PiVec) (j : Fin 3), f (x + Pi.single j 1) = f x := by
    intro x j
    change a (piToVec (x + Pi.single j 1)) = a (piToVec x)
    rw [map_add]
    exact hp (piToVec x) j
  have hdf (x : PiVec) :
      fderiv ℝ f x (Pi.single i 1) = fderiv ℝ a (piToVec x) (unitVector i) := by
    have hd := ((ha.differentiable (by simp) (piToVec x)).hasFDerivAt.comp x
      piToVec.hasFDerivAt).fderiv
    exact congrArg (fun L : PiVec →L[ℝ] E => L (Pi.single i 1)) hd
  have hzero := pi_integral_coordinateDerivative_zero f hf hp' i
  simp only [hdf] at hzero
  have hm : MeasurePreserving piToVec := PiLp.volume_preserving_toLp (Fin 3)
  have hchange := hm.setIntegral_preimage_emb
    piToVec.toHomeomorph.measurableEmbedding
      (fun x => fderiv ℝ a x (unitVector i)) unitCube
  rw [piToVec_preimage_cube] at hchange
  exact hchange.symm.trans hzero

/-- Every smooth periodic coordinate derivative has exactly zero cube mean. -/
theorem spatialMean_coordinateDerivative_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i : Fin 3) :
    spatialMean (coordinateDerivative a i) = 0 :=
  integral_fderiv_unitVector_zero ha hp i

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
    simp [spatialCurl, PiLp.toLp_apply]
  · rw [integral_sub (hi 1 2) (hi 2 1),
      integral_coordinate_component_zero ha hp, integral_coordinate_component_zero ha hp]
    simp
  · rw [integral_sub (hi 2 0) (hi 0 2),
      integral_coordinate_component_zero ha hp, integral_coordinate_component_zero ha hp]
    simp
  · rw [integral_sub (hi 0 1) (hi 1 0),
      integral_coordinate_component_zero ha hp, integral_coordinate_component_zero ha hp]
    simp

theorem gradient_smooth {f : ScalarField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (NSEMaxwell.Classical.gradient f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  apply (contDiff_piLp 2).mpr
  intro i
  exact hd.clm_apply contDiff_const

theorem spatialMean_gradient_zero {f : ScalarField}
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    spatialMean (NSEMaxwell.Classical.gradient f) = 0 := by
  ext i
  rw [spatialMean_apply (gradient_smooth hf).continuous i]
  exact integral_fderiv_unitVector_zero hf hp i

theorem laplacian_smooth {a : Field} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (NSEMaxwell.Classical.laplacian a) := by
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3,
    coordinateDerivative (coordinateDerivative a i) i x)
  exact ContDiff.sum fun i hi =>
    coordinateDerivative_smooth (coordinateDerivative_smooth ha i) i

theorem spatialMean_laplacian_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    spatialMean (NSEMaxwell.Classical.laplacian a) = 0 := by
  change (∫ x in unitCube,
    ∑ i : Fin 3, coordinateDerivative (coordinateDerivative a i) i x) = 0
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i hi
    exact spatialMean_coordinateDerivative_zero
      (coordinateDerivative_smooth ha i) (coordinateDerivative_periodic hp i) i
  · intro i hi
    exact integrableOn_unitCube_of_continuous
      (coordinateDerivative_smooth (coordinateDerivative_smooth ha i) i).continuous

def momentumFlux (a : Field) (i : Fin 3) : Field := fun x => a x i • a x

theorem momentumFlux_smooth {a : Field} (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    ContDiff ℝ ∞ (momentumFlux a i) :=
  ((contDiff_piLp 2).mp ha i).smul ha

theorem momentumFlux_periodic {a : Field} (hp : SpatialPeriodic a) (i : Fin 3) :
    SpatialPeriodic (momentumFlux a i) := by
  intro x j
  simp only [momentumFlux, hp x j]

theorem coordinateDerivative_momentumFlux {a : Field}
    (ha : ContDiff ℝ ∞ a) (i j : Fin 3) (x : Vec) :
    coordinateDerivative (momentumFlux a i) j x =
      a x i • coordinateDerivative a j x + coordinateDerivative a j x i • a x := by
  have hx := ha.differentiable (by simp) x
  have hc := ((contDiff_piLp 2).mp ha i).differentiable (by simp) x
  change fderiv ℝ (fun y : Vec => a y i • a y) x (unitVector j) = _
  rw [fderiv_fun_smul hc hx]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [fderiv_component_apply hx (unitVector j) i]
  rfl

/-- Divergence form of the convective term, including its compressible correction. -/
theorem momentumFlux_divergence {a : Field} (ha : ContDiff ℝ ∞ a) (x : Vec) :
    (∑ i : Fin 3, coordinateDerivative (momentumFlux a i) i x) =
      convection a x + NSEMaxwell.Classical.divergence a x • a x := by
  ext j
  simp [coordinateDerivative_momentumFlux ha, Fin.sum_univ_succ,
    NSEMaxwell.Lamb.convection_coordinate,
    NSEMaxwell.Classical.divergence, smul_eq_mul]
  ring

theorem convection_smooth {a : Field} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (convection a) :=
  (ha.fderiv_right (by simp)).clm_apply ha

/-- Smooth periodic divergence-free convection has zero cube integral. -/
theorem spatialMean_convection_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hdiv : ∀ x : Vec, NSEMaxwell.Classical.divergence a x = 0) :
    spatialMean (convection a) = 0 := by
  have heq : convection a =
      fun x => ∑ i : Fin 3, coordinateDerivative (momentumFlux a i) i x := by
    funext x
    rw [momentumFlux_divergence ha, hdiv x, zero_smul, add_zero]
  unfold spatialMean
  rw [heq, integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i hi
    exact spatialMean_coordinateDerivative_zero
      (momentumFlux_smooth ha i) (momentumFlux_periodic hp i) i
  · intro i hi
    exact integrableOn_unitCube_of_continuous
      (coordinateDerivative_smooth (momentumFlux_smooth ha i) i).continuous

end

end NSEMaxwell.PeriodicIntegration
