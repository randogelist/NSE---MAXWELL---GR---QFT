import SingularClosure.HilbertChannels
import SingularClosure.CoordinateAverageOrthogonal
import SingularClosure.FourierIntegral
import SingularClosure.PeriodicCover

/-!
# Actual physical cube data in the unit-torus Fourier Hilbert space

The representative is chosen by Mathlib's measurable equivalence with (0,1]^3.
For every continuous physical field, its component functions give literal L²
functions on the unit torus, and their Hilbert-basis coefficients equal the
actual physical cube Fourier integrals. No Fourier-agreement premise is used.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

local instance periodicRealizationMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance periodicRealizationHaarMeasure : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance periodicRealizationProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusDatumRepresentative (θ : UnitAddTorus (Fin 3)) : Vec :=
  WithLp.toLp 2 ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) θ).val)

theorem torusDatumRepresentative_measurable : Measurable torusDatumRepresentative :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
    (measurable_subtype_coe.comp
      (UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ)).measurable)

theorem torusDatumRepresentative_mem (θ : UnitAddTorus (Fin 3)) :
    torusDatumRepresentative θ ∈ unitCube := by
  intro i
  have h : 0 < (UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) θ).val i ∧
      (UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) θ).val i ≤ 1 := by
    simpa only [mem_Ioc, Pi.zero_apply, zero_add] using
      (UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ) θ).property i
  exact ⟨h.1.le, h.2⟩

theorem torusDatumRepresentative_mk_of_mem (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ Ioc (0 : ℝ) 1) :
    torusDatumRepresentative (fun i => (x i : UnitAddCircle)) = WithLp.toLp 2 x := by
  have hx' : ∀ i, x i ∈ Ioc ((0 : Fin 3 → ℝ) i) ((0 : Fin 3 → ℝ) i + 1) := by
    simpa only [Pi.zero_apply, zero_add] using hx
  change WithLp.toLp 2
      ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ)
        (fun i => (x i : UnitAddCircle))).val) = WithLp.toLp 2 x
  congr 1
  exact congrArg Subtype.val
    ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 3 → ℝ)).apply_symm_apply ⟨x, hx'⟩)

theorem torusDatumRepresentative_coe (θ : UnitAddTorus (Fin 3)) (i : Fin 3) :
    (torusDatumRepresentative θ i : UnitAddCircle) = θ i := by
  change ((AddCircle.equivIoc 1 0 (θ i)).val : UnitAddCircle) = θ i
  exact AddCircle.coe_equivIoc

/-- The selected representative gives the original field at every lift point. -/
theorem torusDatumRepresentative_periodic (a : Field) (hp : SpatialPeriodic a) (x : Vec) :
    a (torusDatumRepresentative (fun i => (x i : UnitAddCircle))) = a x := by
  let r : Vec := torusDatumRepresentative (fun i => (x i : UnitAddCircle))
  have hcoord (i : Fin 3) : ∃ n : ℤ, (n : ℝ) = r i - x i := by
    have hz : ((r i - x i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      change (torusDatumRepresentative (fun i => (x i : UnitAddCircle)) i : UnitAddCircle) -
        (x i : UnitAddCircle) = 0
      rw [torusDatumRepresentative_coe, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn⟩
  choose z hz using hcoord
  have hr : r = x + integerShift z := by
    ext i
    rw [PiLp.add_apply, integerShift_apply]
    linarith [hz i]
  change a r = a x
  rw [hr]
  exact spatialPeriodic_integerShift hp z x

def torusDatumComponent (a : Field) (i : Fin 3) : UnitAddTorus (Fin 3) → ℂ :=
  fun θ => (a (torusDatumRepresentative θ) i : ℂ)

theorem torusDatumComponent_mk (a : Field) (hp : SpatialPeriodic a)
    (i : Fin 3) (x : Vec) :
    torusDatumComponent a i (fun j => (x j : UnitAddCircle)) = (a x i : ℂ) := by
  unfold torusDatumComponent
  rw [torusDatumRepresentative_periodic a hp x]

theorem torusDatumComponent_measurable (a : Field) (ha : Continuous a) (i : Fin 3) :
    Measurable (torusDatumComponent a i) :=
  Complex.continuous_ofReal.measurable.comp
    (((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp ha).measurable.comp
      torusDatumRepresentative_measurable)

theorem torusDatumComponent_memLp (a : Field) (ha : Continuous a) (i : Fin 3) :
    MemLp (torusDatumComponent a i) 2 (volume : Measure (UnitAddTorus (Fin 3))) := by
  have hc : Continuous (fun x : Vec => (a x i : ℂ)) :=
    Complex.continuous_ofReal.comp ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp ha)
  obtain ⟨C, hC⟩ := isCompact_unitCube.bddAbove_image hc.norm.continuousOn
  apply MemLp.of_bound (torusDatumComponent_measurable a ha i).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun θ =>
    hC (mem_image_of_mem _ (torusDatumRepresentative_mem θ)))

/-- Concrete L² representative of one actual physical datum component. -/
def torusDatumL2 (a : Field) (ha : Continuous a) (i : Fin 3) : TorusScalarL2 :=
  (torusDatumComponent_memLp a ha i).toLp (torusDatumComponent a i)

theorem torusDatumL2_coe (a : Field) (ha : Continuous a) (i : Fin 3) :
    torusDatumL2 a ha i =ᵐ[volume] torusDatumComponent a i :=
  (torusDatumComponent_memLp a ha i).coeFn_toLp

theorem integral_unitCube_eq_piIoc (f : Vec → ℂ) :
    (∫ x in unitCube, f x) =
      ∫ x : Fin 3 → ℝ in {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}, f (WithLp.toLp 2 x) := by
  have hinterval : (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1) =
      (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  have hset : {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} =
      Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1) := by
    ext x
    simp
  rw [integral_unitCube_productMeasure, hset]
  change (∫ x, f (WithLp.toLp 2 x) ∂unitProductMeasure 3) =
    ∫ x, f (WithLp.toLp 2 x) ∂((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin 3 => Ioc (0 : ℝ) 1)))
  rw [Measure.restrict_pi_pi]
  simp_rw [hinterval]
  all_goals rfl

/-- Actual Fourier agreement, proved through the fundamental-cube measure equivalence. -/
theorem torusDatumComponent_fourierCoeff (a : Field) (i : Fin 3) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (torusDatumComponent a i) k = datumFourierCoeff a k i := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ k (0 : Fin 3 → ℝ)]
  unfold datumFourierCoeff
  rw [integral_unitCube_eq_piIoc]
  simp only [Pi.zero_apply, zero_add]
  apply setIntegral_congr_fun (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc))
  intro x hx
  have hrep := torusDatumRepresentative_mk_of_mem x hx
  have hchar : UnitAddTorus.mFourier (-k) (fun j => (x j : UnitAddCircle)) =
      star (fourierCharacter k (WithLp.toLp 2 x)) := by
    rw [← fourierCharacter_neg, fourierCharacter_eq_product]
    all_goals rfl
  simp only [smul_eq_mul, hchar, torusDatumComponent, hrep, datumFourierIntegrand]

/-- The actual unit-torus Hilbert coordinates equal the physical datum coefficients. -/
theorem torusDatumL2_fourierBasis_repr (a : Field) (ha : Continuous a)
    (i : Fin 3) (k : Frequency) :
    UnitAddTorus.mFourierBasis.repr (torusDatumL2 a ha i) k = datumFourierCoeff a k i := by
  rw [UnitAddTorus.mFourierBasis_repr]
  calc
    _ = UnitAddTorus.mFourierCoeff (torusDatumComponent a i) k := by
      apply integral_congr_ae
      filter_upwards [torusDatumL2_coe a ha i] with θ hθ
      simp only [hθ]
    _ = _ := torusDatumComponent_fourierCoeff a i k

end

end SingularClosure
