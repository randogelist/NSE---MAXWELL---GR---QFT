import SingularClosure.PeriodicFourierRealization
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Separation.Hausdorff

/-!
# Pointwise uniqueness of actual physical periodic Fourier coefficients

The continuous periodic lift descends continuously to the compact unit torus.
The proof uses the quotient map from the compact physical cube, so it requires
neither a continuous choice of representatives nor an assumed inversion formula.
Hilbert-basis injectivity and Haar full support then imply pointwise uniqueness.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal

namespace SingularClosure

noncomputable section

local instance periodicInjectivityMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance periodicInjectivityHaarMeasure : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance periodicInjectivityProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The literal coordinate quotient on the compact physical cube. -/
def unitCubeTorusProjection (x : unitCube) : UnitAddTorus (Fin 3) :=
  fun i => (x.val i : UnitAddCircle)

theorem unitCubeTorusProjection_continuous : Continuous unitCubeTorusProjection := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (p := (1 : ℝ))).comp
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp continuous_subtype_val)

theorem unitCubeTorusProjection_surjective : Function.Surjective unitCubeTorusProjection := by
  intro θ
  refine ⟨⟨torusDatumRepresentative θ, torusDatumRepresentative_mem θ⟩, ?_⟩
  funext i
  exact torusDatumRepresentative_coe θ i

theorem unitCubeTorusProjection_isQuotientMap :
    Topology.IsQuotientMap unitCubeTorusProjection := by
  letI : CompactSpace unitCube := isCompact_iff_compactSpace.mp isCompact_unitCube
  exact unitCubeTorusProjection_continuous.isClosedMap.isQuotientMap
    unitCubeTorusProjection_continuous unitCubeTorusProjection_surjective

/-- Continuity of the actual periodic datum on the quotient torus. -/
theorem torusDatumComponent_continuous (a : Field) (ha : Continuous a)
    (hp : SpatialPeriodic a) (i : Fin 3) : Continuous (torusDatumComponent a i) := by
  apply unitCubeTorusProjection_isQuotientMap.continuous_iff.mpr
  have heq : torusDatumComponent a i ∘ unitCubeTorusProjection =
      fun x : unitCube => (a x.val i : ℂ) := by
    funext x
    exact torusDatumComponent_mk a hp i x.val
  rw [heq]
  exact Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
      (ha.comp continuous_subtype_val))

/-- Equality of physical Fourier integrals implies equality of the torus L² data. -/
theorem torusDatumL2_eq_of_fourierCoeff_eq (a b : Field)
    (ha : Continuous a) (hb : Continuous b)
    (hcoeff : datumFourierCoeff a = datumFourierCoeff b) (i : Fin 3) :
    torusDatumL2 a ha i = torusDatumL2 b hb i := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  apply lp.ext
  funext k
  rw [torusDatumL2_fourierBasis_repr, torusDatumL2_fourierBasis_repr, hcoeff]

/-- Actual continuous unit-periodic physical fields are determined pointwise by
their cube Fourier integrals. -/
theorem datumFourierCoeff_injective_continuous_periodic (a b : Field)
    (ha : Continuous a) (hb : Continuous b)
    (hpa : SpatialPeriodic a) (hpb : SpatialPeriodic b)
    (hcoeff : datumFourierCoeff a = datumFourierCoeff b) : a = b := by
  have htorus (i : Fin 3) : torusDatumComponent a i = torusDatumComponent b i := by
    apply (Continuous.ae_eq_iff_eq (volume : Measure (UnitAddTorus (Fin 3)))
      (torusDatumComponent_continuous a ha hpa i)
      (torusDatumComponent_continuous b hb hpb i)).mp
    have hl2 := torusDatumL2_eq_of_fourierCoeff_eq a b ha hb hcoeff i
    filter_upwards [torusDatumL2_coe a ha i, torusDatumL2_coe b hb i] with θ haθ hbθ
    rw [← haθ, ← hbθ, hl2]
  funext x
  ext i
  apply Complex.ofReal_injective
  calc
    (a x i : ℂ) = torusDatumComponent a i (fun j => (x j : UnitAddCircle)) :=
      (torusDatumComponent_mk a hpa i x).symm
    _ = torusDatumComponent b i (fun j => (x j : UnitAddCircle)) :=
      congrFun (htorus i) _
    _ = (b x i : ℂ) := torusDatumComponent_mk b hpb i x

end

end SingularClosure
