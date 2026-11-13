import FourierHodgeLaws.CosineMultiplier
import NSEMaxwell.CurlCurl

/-! Actual spatial differentiation commutes with the frozen inverse Laplacian. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical

noncomputable section

theorem scalarL_summable (f : ScalarField) (hf : ContDiff ℝ ∞ f)
    (hp : SpatialPeriodic f) (x : Vec) :
    Summable (fun k : Frequency => inverseLaplacianSymbol k *
      (∫ y in unitCube, cosineKernel k x y * f y)) := by
  have hs := (SingularClosure.scalarFourierSeries_summable
    (rapid_inverseScalarCoeff f hf hp).summable_norm x).mapL Complex.reCLM
  simp only [Complex.reCLM_apply] at hs
  exact hs.congr (fun k => (scalar_cosine_summand f hf.continuous k x).symm)

theorem cosine_mul_integrable (f : ScalarField) (hf : Continuous f)
    (k : Frequency) (x : Vec) :
    IntegrableOn (fun y : Vec => cosineKernel k x y * f y) unitCube volume := by
  have hc : Continuous (fun y : Vec => cosineKernel k x y) := by
    unfold cosineKernel
    fun_prop
  exact (hc.mul hf).continuousOn.integrableOn_compact
    NSEMaxwell.PeriodicIntegration.isCompact_unitCube

theorem scalarL_add (f g : ScalarField) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfp : SpatialPeriodic f) (hgp : SpatialPeriodic g) :
    scalarL (f + g) = scalarL f + scalarL g := by
  funext x
  calc
    scalarL (f + g) x = ∑' k : Frequency,
        (inverseLaplacianSymbol k * (∫ y in unitCube, cosineKernel k x y * f y) +
         inverseLaplacianSymbol k * (∫ y in unitCube, cosineKernel k x y * g y)) := by
      unfold scalarL
      apply tsum_congr
      intro k
      simp only [Pi.add_apply, mul_add]
      rw [integral_add (cosine_mul_integrable f hf.continuous k x)
        (cosine_mul_integrable g hg.continuous k x)]
      ring
    _ = scalarL f x + scalarL g x :=
      (scalarL_summable f hf hfp x).tsum_add (scalarL_summable g hg hgp x)

theorem scalarL_sub (f g : ScalarField) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfp : SpatialPeriodic f) (hgp : SpatialPeriodic g) :
    scalarL (f - g) = scalarL f - scalarL g := by
  funext x
  calc
    scalarL (f - g) x = ∑' k : Frequency,
        (inverseLaplacianSymbol k * (∫ y in unitCube, cosineKernel k x y * f y) -
         inverseLaplacianSymbol k * (∫ y in unitCube, cosineKernel k x y * g y)) := by
      unfold scalarL
      apply tsum_congr
      intro k
      simp only [Pi.sub_apply, mul_sub]
      rw [integral_sub (cosine_mul_integrable f hf.continuous k x)
        (cosine_mul_integrable g hg.continuous k x)]
      ring
    _ = scalarL f x - scalarL g x :=
      (scalarL_summable f hf hfp x).tsum_sub (scalarL_summable g hg hgp x)

theorem scalarL_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ScalarField)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hp : ∀ i, SpatialPeriodic (f i)) :
    scalarL (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, scalarL (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change scalarL (0 : ScalarField) = (0 : ScalarField)
      exact scalarL_zero
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hs : ContDiff ℝ ∞ (fun x => ∑ j ∈ s, f j x) :=
        ContDiff.sum (fun j _ => hf j)
      have hsp : SpatialPeriodic (fun x => ∑ j ∈ s, f j x) := by
        intro x l
        apply Finset.sum_congr rfl
        intro j _
        exact hp j x l
      have he := scalarL_add (f i) (fun x => ∑ j ∈ s, f j x)
        (hf i) hs (hp i) hsp
      change scalarL ((f i) + (fun x => ∑ j ∈ s, f j x)) = _
      rw [he, ih]
      rfl

theorem coordinateDerivative_vectorL_commute (F : Field)
    (hF : ContDiff ℝ ∞ F) (hp : SpatialPeriodic F) (j : Fin 3) :
    coordinateDerivative (vectorL F) j = vectorL (coordinateDerivative F j) := by
  have hD := NSEMaxwell.CurlCurl.coordinateDerivative_smooth hF j
  have hpD := NSEMaxwell.PeriodicIntegration.coordinateDerivative_periodic hp j
  change SingularClosure.coordinateDerivative (vectorL F) j = _
  rw [vectorL_eq_smoothFourierSynthesis F hF hp,
    SingularClosure.smoothFourierSynthesis_coordinateDerivative _
      (rapid_inverseLaplacianCoeff F hF hp) j,
    vectorL_eq_smoothFourierSynthesis (coordinateDerivative F j) hD hpD]
  congr 1
  funext k i
  unfold inverseVectorCoeff
  rw [datumFourierCoeff_coordinateDerivative F hF hp j]
  simp only [SingularClosure.spectralMultiplier]
  ring

theorem coordinate_component_periodic (F : Field) (hp : SpatialPeriodic F)
    (j i : Fin 3) : SpatialPeriodic (fun x => coordinateDerivative F j x i) := by
  intro x l
  exact congrArg (fun v : Vec => v i)
    (NSEMaxwell.PeriodicIntegration.coordinateDerivative_periodic hp j x l)

theorem scalarL_coordinateComponent (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) (j i : Fin 3) (x : Vec) :
    scalarL (fun y => coordinateDerivative F j y i) x =
      coordinateDerivative (vectorL F) j x i := by
  rw [← vectorL_component (coordinateDerivative F j)
    (NSEMaxwell.CurlCurl.coordinateDerivative_smooth hF j)
    (NSEMaxwell.PeriodicIntegration.coordinateDerivative_periodic hp j) i]
  rw [coordinateDerivative_vectorL_commute F hF hp j]

theorem divergence_vectorL_commute (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) :
    NSEMaxwell.Classical.divergence (vectorL F) =
      scalarL (NSEMaxwell.Classical.divergence F) := by
  have hsum := scalarL_finset_sum Finset.univ
    (fun j : Fin 3 => fun x => coordinateDerivative F j x j)
    (fun j => NSEMaxwell.CurlCurl.coordinate_component_smooth hF j j)
    (fun j => coordinate_component_periodic F hp j j)
  funext x
  change (∑ j : Fin 3, coordinateDerivative (vectorL F) j x j) = _
  rw [show NSEMaxwell.Classical.divergence F =
    (fun y => ∑ j : Fin 3, coordinateDerivative F j y j) from rfl, hsum]
  apply Finset.sum_congr rfl
  intro j _
  exact (scalarL_coordinateComponent F hF hp j j x).symm

theorem curl_vectorL_commute (F : Field) (hF : ContDiff ℝ ∞ F)
    (hp : SpatialPeriodic F) :
    spatialCurl (vectorL F) = vectorL (spatialCurl F) := by
  have hcurl := NSEMaxwell.CurlCurl.spatialCurl_smooth hF
  have hcurlp := NSEMaxwell.PeriodicIntegration.spatialCurl_periodic hp
  have hsub (j i l r : Fin 3) :
      scalarL ((fun x => coordinateDerivative F j x i) -
        (fun x => coordinateDerivative F l x r)) =
      scalarL (fun x => coordinateDerivative F j x i) -
        scalarL (fun x => coordinateDerivative F l x r) :=
    scalarL_sub _ _
      (NSEMaxwell.CurlCurl.coordinate_component_smooth hF j i)
      (NSEMaxwell.CurlCurl.coordinate_component_smooth hF l r)
      (coordinate_component_periodic F hp j i)
      (coordinate_component_periodic F hp l r)
  funext x
  ext i
  rw [congrFun (vectorL_component (spatialCurl F) hcurl hcurlp i) x]
  fin_cases i <;> simp only [spatialCurl, PiLp.toLp_apply] <;> norm_num
  · change _ = scalarL ((fun y => coordinateDerivative F 1 y 2) -
      (fun y => coordinateDerivative F 2 y 1)) x
    rw [hsub, Pi.sub_apply, scalarL_coordinateComponent F hF hp,
      scalarL_coordinateComponent F hF hp]
  · change _ = scalarL ((fun y => coordinateDerivative F 2 y 0) -
      (fun y => coordinateDerivative F 0 y 2)) x
    rw [hsub, Pi.sub_apply, scalarL_coordinateComponent F hF hp,
      scalarL_coordinateComponent F hF hp]
  · change _ = scalarL ((fun y => coordinateDerivative F 0 y 1) -
      (fun y => coordinateDerivative F 1 y 0)) x
    rw [hsub, Pi.sub_apply, scalarL_coordinateComponent F hF hp,
      scalarL_coordinateComponent F hF hp]

end

end NSEMaxwell.HodgeProof
