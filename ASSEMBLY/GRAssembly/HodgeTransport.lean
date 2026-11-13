import GRAdapter.FourierInversion
import ME02.Endpoint
import ME03.Endpoint
import ME04.Endpoint
import ME05.Endpoint
import ME07.Endpoint
import ME16.E01.Endpoint
import ME16.E02.Endpoint
import ME16.E03.Endpoint
import ML049.Endpoint

/-!
GC01--GC04. Transport of the actual retained Methlib cosine multiplier to
NSEGR's negative-symbol inverse. All conclusions concern the native operators.
No Fourier reconstruction, Hodge law, or literature-input witness is assumed.
External compiler and theorem-level axiom audit are required for promotion.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
open Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

/-- GC01: the native inverse has the opposite Fourier symbol. -/
theorem poissonSymbol_eq_neg_methlib (k : Frequency) :
    poissonSymbol k = -NSEMaxwell.Classical.inverseLaplacianSymbol k := by
  classical
  by_cases hk : k = 0 <;>
    simp [poissonSymbol, NSEMaxwell.Classical.inverseLaplacianSymbol, hk]

/-- GC01: totalized sums commute with negation; no summability assumption. -/
theorem poissonInverse_eq_neg_scalarL (f : ScalarField) :
    poissonInverse f = -NSEMaxwell.Classical.scalarL f := by
  funext x
  unfold poissonInverse
  simp only [poissonSymbol_eq_neg_methlib, neg_mul]
  change (∑' k : Frequency, -(NSEMaxwell.Classical.inverseLaplacianSymbol k *
    (∫ y in unitCube, cosineKernel k x y * f y))) =
    -(∑' k : Frequency, NSEMaxwell.Classical.inverseLaplacianSymbol k *
    (∫ y in unitCube, cosineKernel k x y * f y))
  exact GRTemp.ML049.endpoint

/-- GC01: regularity of the native scalar inverse. -/
theorem poissonInverse_smooth (f : ScalarField) (hf : ContDiff ℝ ∞ f)
    (hp : SpatialPeriodic f) : ContDiff ℝ ∞ (poissonInverse f) := by
  rw [poissonInverse_eq_neg_scalarL]
  exact (GRTemp.ME02.endpoint f hf hp).neg

theorem scalarLaplacian_component (a : Field) (ha : ContDiff ℝ ∞ a)
    (i : Fin 3) :
    scalarLaplacian (fun x => a x i) = fun x => laplacian a x i := by
  have hpartial (j : Fin 3) :
      (fun y => fderiv ℝ (fun z => a z i) y (unitVector j)) =
      (fun y => spatialPartial a j y i) := by
    funext y
    exact StressCalc.component_fderiv (ha.differentiable (by simp) y)
      (unitVector j) i
  funext x
  change (∑ j : Fin 3, fderiv ℝ
    (fun y => fderiv ℝ (fun z => a z i) y (unitVector j)) x (unitVector j)) = _
  simp only [hpartial, StressCalc.partial_component_fderiv ha]
  exact (StressCalc.laplacian_component ha x i).symm

theorem scalarLaplacian_neg (f : ScalarField) :
    scalarLaplacian (-f) = -scalarLaplacian f := by
  funext x
  simp [scalarLaplacian, fderiv_neg, Finset.sum_neg_distrib]

/-- GC02: the native scalar right inverse follows from the vector endpoint
by an actual scalar lift and an actual coordinate projection. -/
theorem scalarLaplacian_poissonInverse (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    scalarLaplacian (poissonInverse f) = f - (fun _ => scalarMean f) := by
  let F : Field := NSEMaxwell.HodgeProof.scalarLift f
  have hF : ContDiff ℝ ∞ F := GRTemp.ME16.E02.endpoint f hf
  have hpF : SpatialPeriodic F := GRTemp.ME16.E03.endpoint f hp
  have hLF : ContDiff ℝ ∞ (NSEMaxwell.Classical.vectorL F) :=
    GRTemp.ME03.endpoint F hF hpF
  have hcomp : (fun x => NSEMaxwell.Classical.vectorL F x (0 : Fin 3)) =
      NSEMaxwell.Classical.scalarL f := GRTemp.ME04.endpoint F hF hpF 0
  have hmean : spatialMean F (0 : Fin 3) = scalarMean f := by
    rw [spatialMean_apply hF.continuous]
    rfl
  have hlap : scalarLaplacian (NSEMaxwell.Classical.scalarL f) =
      fun x => laplacian (NSEMaxwell.Classical.vectorL F) x (0 : Fin 3) := by
    rw [← hcomp]
    exact scalarLaplacian_component _ hLF 0
  rw [poissonInverse_eq_neg_scalarL, scalarLaplacian_neg, hlap]
  funext x
  have hv := congrArg (fun a : Field => a x (0 : Fin 3))
    (GRTemp.ME07.endpoint F hF hpF)
  change -laplacian (NSEMaxwell.Classical.vectorL F) x (0 : Fin 3) =
    F x (0 : Fin 3) - spatialMean F (0 : Fin 3) at hv
  rw [hmean] at hv
  exact hv

/-- GC02: removal of the zero Fourier coefficient gives the actual zero mean. -/
theorem scalarMean_poissonInverse_zero (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    scalarMean (poissonInverse f) = 0 := by
  let F : Field := NSEMaxwell.HodgeProof.scalarLift f
  have hF : ContDiff ℝ ∞ F := GRTemp.ME16.E02.endpoint f hf
  have hpF : SpatialPeriodic F := GRTemp.ME16.E03.endpoint f hp
  have hLF : ContDiff ℝ ∞ (NSEMaxwell.Classical.vectorL F) :=
    GRTemp.ME03.endpoint F hF hpF
  have hcomp : (fun x => NSEMaxwell.Classical.vectorL F x (0 : Fin 3)) =
      NSEMaxwell.Classical.scalarL f := GRTemp.ME04.endpoint F hF hpF 0
  have hc := congrArg (fun C : SingularClosure.FourierCoeff => C 0 0)
    (NSEMaxwell.HodgeProof.datumFourierCoeff_vectorL F hF hpF)
  change SingularClosure.datumFourierCoeff (NSEMaxwell.Classical.vectorL F) 0 0 =
    NSEMaxwell.HodgeProof.inverseVectorCoeff F 0 0 at hc
  rw [SingularClosure.datumFourierCoeff_zero
    (integrableOn_unitCube_of_continuous hLF.continuous),
    NSEMaxwell.HodgeProof.inverseVectorCoeff_zero] at hc
  have hm : spatialMean (NSEMaxwell.Classical.vectorL F) (0 : Fin 3) = 0 := by
    exact_mod_cast hc
  rw [spatialMean_apply hLF.continuous] at hm
  change (∫ x in unitCube, (fun y => NSEMaxwell.Classical.vectorL F y 0) x) = 0 at hm
  rw [hcomp] at hm
  rw [poissonInverse_eq_neg_scalarL]
  change (∫ x in unitCube, -NSEMaxwell.Classical.scalarL f x) = 0
  rw [integral_neg, hm, neg_zero]

/-- Scalar spatial differentiation, obtained from ME05 through ME04. -/
theorem scalarPartial_scalarL_commute (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (j : Fin 3) :
    fourierScalarPartial (NSEMaxwell.Classical.scalarL f) j =
      NSEMaxwell.Classical.scalarL (fourierScalarPartial f j) := by
  let F : Field := NSEMaxwell.HodgeProof.scalarLift f
  have hF : ContDiff ℝ ∞ F := GRTemp.ME16.E02.endpoint f hf
  have hpF : SpatialPeriodic F := GRTemp.ME16.E03.endpoint f hp
  have hLF : ContDiff ℝ ∞ (NSEMaxwell.Classical.vectorL F) :=
    GRTemp.ME03.endpoint F hF hpF
  have hcomp : (fun x => NSEMaxwell.Classical.vectorL F x (0 : Fin 3)) =
      NSEMaxwell.Classical.scalarL f := GRTemp.ME04.endpoint F hF hpF 0
  have hpartial : (fun x => spatialPartial F j x (0 : Fin 3)) =
      fourierScalarPartial f j := by
    funext x
    exact (StressCalc.component_fderiv (hF.differentiable (by simp) x)
      (unitVector j) 0).symm
  have hcompD := GRTemp.ME04.endpoint (spatialPartial F j)
    (spatialPartial_smooth hF j) (spatialPartial_periodic hpF j) (0 : Fin 3)
  change (fun x => NSEMaxwell.Classical.vectorL (spatialPartial F j) x 0) =
    NSEMaxwell.Classical.scalarL (fun x => spatialPartial F j x 0) at hcompD
  rw [hpartial] at hcompD
  funext x
  rw [← hcomp]
  change fderiv ℝ (fun y => NSEMaxwell.Classical.vectorL F y 0) x
    (unitVector j) = _
  rw [StressCalc.component_fderiv (hLF.differentiable (by simp) x)]
  change spatialPartial (NSEMaxwell.Classical.vectorL F) j x 0 = _
  have hcomm : spatialPartial (NSEMaxwell.Classical.vectorL F) j =
      NSEMaxwell.Classical.vectorL (spatialPartial F j) :=
    GRTemp.ME05.endpoint F hF hpF j
  rw [hcomm]
  exact congrFun hcompD x

/-- GC04: ordinary spatial partials commute with the native inverse. -/
theorem scalarPartial_poissonInverse_commute (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (j : Fin 3) :
    fourierScalarPartial (poissonInverse f) j =
      poissonInverse (fourierScalarPartial f j) := by
  rw [poissonInverse_eq_neg_scalarL, poissonInverse_eq_neg_scalarL]
  have hn (g : ScalarField) : fourierScalarPartial (-g) j =
      -fourierScalarPartial g j := by
    funext x
    simp [fourierScalarPartial, fderiv_neg]
  rw [hn, scalarPartial_scalarL_commute f hf hp j]

/-- Finite summation passes through the native inverse on smooth periodic inputs. -/
theorem poissonInverse_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ScalarField)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hp : ∀ i, SpatialPeriodic (f i)) :
    poissonInverse (fun x => ∑ i ∈ s, f i x) =
      fun x => ∑ i ∈ s, poissonInverse (f i) x := by
  rw [poissonInverse_eq_neg_scalarL,
    NSEMaxwell.HodgeProof.scalarL_finset_sum s f hf hp]
  funext x
  simp only [poissonInverse_eq_neg_scalarL, Pi.neg_apply, Finset.sum_neg_distrib]

/-- GC04: the second-order spatial operator commutes with the inverse. -/
theorem scalarLaplacian_poissonInverse_commute (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    scalarLaplacian (poissonInverse f) = poissonInverse (scalarLaplacian f) := by
  change (fun x => ∑ i : Fin 3,
    fourierScalarPartial (fourierScalarPartial (poissonInverse f) i) i x) =
    poissonInverse (fun x => ∑ i : Fin 3,
      fourierScalarPartial (fourierScalarPartial f i) i x)
  rw [poissonInverse_finset_sum Finset.univ
    (fun i => fourierScalarPartial (fourierScalarPartial f i) i)
    (fun i => fourierScalarPartial_smooth _ (fourierScalarPartial_smooth f hf i) i)
    (fun i => fourierScalarPartial_periodic _ (fourierScalarPartial_periodic f hp i) i)]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarPartial_poissonInverse_commute f hf hp i,
    scalarPartial_poissonInverse_commute _ (fourierScalarPartial_smooth f hf i)
      (fourierScalarPartial_periodic f hp i) i]

/-- GC02: left inversion modulo the actual cube mean, without LI03. -/
theorem poissonInverse_scalarLaplacian (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    poissonInverse (scalarLaplacian f) = f - (fun _ => scalarMean f) := by
  rw [← scalarLaplacian_poissonInverse_commute f hf hp]
  exact scalarLaplacian_poissonInverse f hf hp

/-- GC04: every smooth periodic gradient lies in the kernel of the projector. -/
theorem leray_gradient_zero (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    leray (gradient f) = 0 := by
  have hG : gradient (f - (fun _ => scalarMean f)) = gradient f := by
    funext x
    apply PiLp.ext
    intro i
    change fderiv ℝ (fun y => f y - scalarMean f) x (unitVector i) =
      fderiv ℝ f x (unitVector i)
    rw [fderiv_fun_sub (hf.differentiable (by simp) x)
      (differentiableAt_const (scalarMean f))]
    simp
  unfold leray
  rw [divergence_gradient hf, poissonInverse_scalarLaplacian f hf hp, hG]
  funext x
  exact sub_self _

theorem divergence_smooth (a : Field) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (divergence a) :=
  ContDiff.sum (fun i _ => StressCalc.partial_component_smooth ha i i)

theorem divergence_sub (a b : Field) (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) : divergence (a - b) = divergence a - divergence b := by
  funext x
  change (∑ i : Fin 3, (fderiv ℝ (fun y => a y - b y) x (unitVector i)) i) = _
  rw [fderiv_fun_sub (ha.differentiable (by simp) x)
    (hb.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]
  rfl

/-- GC04: the actual Helmholtz formula preserves smoothness. -/
theorem leray_smooth (a : Field) (ha : ContDiff ℝ ∞ a)
    (hp : SpatialPeriodic a) : ContDiff ℝ ∞ (leray a) :=
  ha.sub (gradient_smooth
    (poissonInverse_smooth (divergence a) (divergence_smooth a ha)
      (divergence_periodic hp)))

/-- GC04: the scalar inverse removes the entire divergence. -/
theorem divergence_leray_zero (a : Field) (ha : ContDiff ℝ ∞ a)
    (hp : SpatialPeriodic a) : divergence (leray a) = 0 := by
  have hG := poissonInverse_smooth (divergence a) (divergence_smooth a ha)
    (divergence_periodic hp)
  change divergence (a - gradient (poissonInverse (divergence a))) = 0
  rw [divergence_sub a _ ha (gradient_smooth hG), divergence_gradient hG,
    scalarLaplacian_poissonInverse (divergence a) (divergence_smooth a ha)
      (divergence_periodic hp), scalarMean_divergence_zero ha hp]
  ext x
  simp

/-- The native projector fixes every field with vanishing total divergence. -/
theorem leray_eq_self_of_divergence_zero (a : Field) (hdiv : divergence a = 0) :
    leray a = a := by
  funext x
  simp [leray, hdiv]

/-- GC04: idempotence follows from the proved divergence cancellation. -/
theorem leray_idempotent (a : Field) (ha : ContDiff ℝ ∞ a)
    (hp : SpatialPeriodic a) : leray (leray a) = leray a :=
  leray_eq_self_of_divergence_zero _ (divergence_leray_zero a ha hp)

/-- GC04: the zero frequency of the vector field is retained exactly. -/
theorem spatialMean_leray (a : Field) (ha : ContDiff ℝ ∞ a)
    (hp : SpatialPeriodic a) : spatialMean (leray a) = spatialMean a := by
  have hG := poissonInverse_smooth (divergence a) (divergence_smooth a ha)
    (divergence_periodic hp)
  change (∫ x in unitCube, a x - gradient (poissonInverse (divergence a)) x) = _
  rw [integral_sub (integrableOn_unitCube_of_continuous ha.continuous)
    (integrableOn_unitCube_of_continuous (gradient_smooth hG).continuous)]
  change spatialMean a - spatialMean (gradient (poissonInverse (divergence a))) = _
  rw [spatialMean_gradient_zero hG (poissonInverse_periodic _), sub_zero]

end
end NSEGR.Assembly
