import GRAdapter.LiteratureInputs
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
Dimension-general physical unit-cube/torus bridges. No literature input is
assumed. The construction generalizes the audited three-dimensional Methlib
representative and compact-quotient argument without restricting dimension.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.NativeLiterature

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def literaturePiToSpace (n : ℕ) : (Fin n → ℝ) ≃L[ℝ] LiteratureSpace n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

theorem literaturePiToSpace_preimage_cube (n : ℕ) :
    literaturePiToSpace n ⁻¹' LiteratureUnitCube n = Icc (0 : Fin n → ℝ) 1 := by
  ext x
  change (∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1) ↔
    ((∀ i : Fin n, 0 ≤ x i) ∧ ∀ i : Fin n, x i ≤ 1)
  exact forall_and

theorem isCompact_literatureUnitCube (n : ℕ) : IsCompact (LiteratureUnitCube n) := by
  have hs : LiteratureUnitCube n = literaturePiToSpace n '' Icc (0 : Fin n → ℝ) 1 := by
    rw [← literaturePiToSpace_preimage_cube,
      Set.image_preimage_eq _ (literaturePiToSpace n).surjective]
  rw [hs]
  exact isCompact_Icc.image (literaturePiToSpace n).continuous

theorem integrableOn_literatureUnitCube_of_continuous
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] {f : LiteratureSpace n → E}
    (hf : Continuous f) : IntegrableOn f (LiteratureUnitCube n) := by
  have hm : MeasurePreserving (literaturePiToSpace n) := PiLp.volume_preserving_toLp (Fin n)
  apply (hm.integrableOn_comp_preimage
    (literaturePiToSpace n).toHomeomorph.measurableEmbedding).mp
  rw [literaturePiToSpace_preimage_cube]
  exact (hf.comp (literaturePiToSpace n).continuous).integrableOn_Icc

theorem volume_literatureUnitCube (n : ℕ) : volume (LiteratureUnitCube n) = 1 := by
  have hm : MeasurePreserving (literaturePiToSpace n) := PiLp.volume_preserving_toLp (Fin n)
  have hv := hm.measure_preimage_emb
    (literaturePiToSpace n).toHomeomorph.measurableEmbedding (LiteratureUnitCube n)
  rw [literaturePiToSpace_preimage_cube] at hv
  rw [← hv, ← Set.pi_univ_Icc, volume_pi_pi]
  simp [Real.volume_Icc]

def literatureUnitIntervalMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

def literatureUnitProductMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => literatureUnitIntervalMeasure)

instance literatureUnitIntervalMeasure_probability :
    IsProbabilityMeasure literatureUnitIntervalMeasure := by
  constructor
  simp [literatureUnitIntervalMeasure]

instance literatureUnitProductMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (literatureUnitProductMeasure n) := by
  unfold literatureUnitProductMeasure
  infer_instance

theorem literaturePiCube_eq (n : ℕ) :
    Icc (0 : Fin n → ℝ) (fun _ => 1) =
      Set.univ.pi (fun _ : Fin n => Icc (0 : ℝ) 1) := by
  ext x
  constructor
  · intro hx i _
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    exact ⟨fun i => (hx i (Set.mem_univ i)).1,
      fun i => (hx i (Set.mem_univ i)).2⟩

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_literatureUnitCube_productMeasure {n : ℕ} (f : LiteratureSpace n → E) :
    (∫ x in LiteratureUnitCube n, f x) =
      ∫ x : Fin n → ℝ, f (WithLp.toLp 2 x) ∂literatureUnitProductMeasure n := by
  have hc := (PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding f (LiteratureUnitCube n)
  have hp : (@WithLp.toLp 2 (Fin n → ℝ)) ⁻¹' LiteratureUnitCube n =
      Set.univ.pi (fun _ : Fin n => Icc (0 : ℝ) 1) := by
    ext x
    change (∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1) ↔
      (∀ i : Fin n, i ∈ Set.univ → 0 ≤ x i ∧ x i ≤ 1)
    exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩
  rw [hp] at hc
  rw [← hc]
  change (∫ x : Fin n → ℝ, f (WithLp.toLp 2 x)
    ∂((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin n => Icc (0 : ℝ) 1)))) = _
  rw [Measure.restrict_pi_pi]
  rfl

theorem continuous_integrable_literatureUnitProduct (n : ℕ)
    (f : (Fin n → ℝ) → E) (hf : Continuous f) :
    Integrable f (literatureUnitProductMeasure n) := by
  have hi : IntegrableOn f (Icc (0 : Fin n → ℝ) (fun _ => 1)) volume :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  rw [literaturePiCube_eq] at hi
  change Integrable f
    ((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin n => Icc (0 : ℝ) 1))) at hi
  rw [Measure.restrict_pi_pi] at hi
  exact hi

theorem integral_literatureUnitCube_disintegrate {n : ℕ}
    (j : Fin (n + 1)) (f : LiteratureSpace (n + 1) → E) (hf : Continuous f) :
    (∫ x in LiteratureUnitCube (n + 1), f x) =
      ∫ y : Fin n → ℝ, (∫ s in Icc (0 : ℝ) 1,
        f (WithLp.toLp 2 (j.insertNth s y))) ∂literatureUnitProductMeasure n := by
  let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j).symm
  have he : MeasurePreserving e
      (literatureUnitIntervalMeasure.prod (literatureUnitProductMeasure n))
      (literatureUnitProductMeasure (n + 1)) :=
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => literatureUnitIntervalMeasure) j).symm
  have hc : Continuous (fun x : Fin (n + 1) → ℝ => f (WithLp.toLp 2 x)) :=
    hf.comp (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ))
  have hi := continuous_integrable_literatureUnitProduct (n + 1) _ hc
  have hp : Integrable (fun z => f (WithLp.toLp 2 (e z)))
      (literatureUnitIntervalMeasure.prod (literatureUnitProductMeasure n)) :=
    (he.integrable_comp_emb e.measurableEmbedding).2 hi
  rw [integral_literatureUnitCube_productMeasure, ← he.integral_comp']
  rw [integral_prod_symm _ hp]
  rfl

theorem integral_literatureUnitCube_eq_piIoc {n : ℕ} (f : LiteratureSpace n → E) :
    (∫ x in LiteratureUnitCube n, f x) =
      ∫ x : Fin n → ℝ in {x | ∀ i, x i ∈ Ioc (0 : ℝ) 1}, f (WithLp.toLp 2 x) := by
  have hi : (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1) =
      (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  have hs : {x : Fin n → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} =
      Set.univ.pi (fun _ : Fin n => Ioc (0 : ℝ) 1) := by
    ext x
    simp
  rw [integral_literatureUnitCube_productMeasure, hs]
  change (∫ x, f (WithLp.toLp 2 x) ∂literatureUnitProductMeasure n) =
    ∫ x, f (WithLp.toLp 2 x)
      ∂((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
        (Set.univ.pi (fun _ : Fin n => Ioc (0 : ℝ) 1)))
  rw [Measure.restrict_pi_pi]
  simp_rw [hi]
  rfl

end Integral

def literatureIntegerShift {n : ℕ} (z : Fin n → ℤ) : LiteratureSpace n :=
  ∑ i : Fin n, z i • LiteratureUnitVector i

theorem literatureIntegerShift_apply {n : ℕ} (z : Fin n → ℤ) (i : Fin n) :
    literatureIntegerShift z i = (z i : ℝ) := by
  simp [literatureIntegerShift, LiteratureUnitVector, EuclideanSpace.single,
    Finset.sum_apply, zsmul_eq_mul, Pi.single_apply, mul_ite]

theorem literaturePeriodic_integerShift {n : ℕ} {f : LiteratureSpace n → ℂ}
    (hp : LiteraturePeriodic f) (z : Fin n → ℤ) :
    Function.Periodic f (literatureIntegerShift z) := by
  have hc (i : Fin n) : Function.Periodic f (z i • LiteratureUnitVector i) :=
    (show Function.Periodic f (LiteratureUnitVector i) from fun x => hp x i).zsmul (z i)
  have hs (s : Finset (Fin n)) :
      Function.Periodic f (∑ i ∈ s, z i • LiteratureUnitVector i) := by
    induction s using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hc i).add_period ih
  exact hs Finset.univ

def literatureTorusRepresentative {n : ℕ} (θ : UnitAddTorus (Fin n)) : LiteratureSpace n :=
  WithLp.toLp 2 ((UnitAddTorus.measurableEquivPiIoc (0 : Fin n → ℝ) θ).val)

theorem literatureTorusRepresentative_mem {n : ℕ} (θ : UnitAddTorus (Fin n)) :
    literatureTorusRepresentative θ ∈ LiteratureUnitCube n := by
  intro i
  have h : 0 < (UnitAddTorus.measurableEquivPiIoc (0 : Fin n → ℝ) θ).val i ∧
      (UnitAddTorus.measurableEquivPiIoc (0 : Fin n → ℝ) θ).val i ≤ 1 := by
    simpa only [mem_Ioc, Pi.zero_apply, zero_add] using
      (UnitAddTorus.measurableEquivPiIoc (0 : Fin n → ℝ) θ).property i
  exact ⟨h.1.le, h.2⟩

theorem literatureTorusRepresentative_mk_of_mem {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Ioc (0 : ℝ) 1) :
    literatureTorusRepresentative (fun i => (x i : UnitAddCircle)) = WithLp.toLp 2 x := by
  have hx' : ∀ i, x i ∈ Ioc ((0 : Fin n → ℝ) i) ((0 : Fin n → ℝ) i + 1) := by
    simpa only [Pi.zero_apply, zero_add] using hx
  change WithLp.toLp 2
      ((UnitAddTorus.measurableEquivPiIoc (0 : Fin n → ℝ)
        (fun i => (x i : UnitAddCircle))).val) = WithLp.toLp 2 x
  congr 1
  exact congrArg Subtype.val
    ((UnitAddTorus.measurableEquivPiIoc (0 : Fin n → ℝ)).apply_symm_apply ⟨x, hx'⟩)

theorem literatureTorusRepresentative_coe {n : ℕ} (θ : UnitAddTorus (Fin n)) (i : Fin n) :
    (literatureTorusRepresentative θ i : UnitAddCircle) = θ i := by
  change ((AddCircle.equivIoc 1 0 (θ i)).val : UnitAddCircle) = θ i
  exact AddCircle.coe_equivIoc

theorem literatureTorusRepresentative_periodic {n : ℕ}
    (f : LiteratureSpace n → ℂ) (hp : LiteraturePeriodic f) (x : LiteratureSpace n) :
    f (literatureTorusRepresentative (fun i => (x i : UnitAddCircle))) = f x := by
  let r : LiteratureSpace n := literatureTorusRepresentative (fun i => (x i : UnitAddCircle))
  have hc (i : Fin n) : ∃ z : ℤ, (z : ℝ) = r i - x i := by
    have hz : ((r i - x i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      change (literatureTorusRepresentative (fun i => (x i : UnitAddCircle)) i : UnitAddCircle) -
        (x i : UnitAddCircle) = 0
      rw [literatureTorusRepresentative_coe, sub_self]
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hz
    exact ⟨z, by simpa only [zsmul_eq_mul, mul_one] using hz⟩
  choose z hz using hc
  have hr : r = x + literatureIntegerShift z := by
    ext i
    rw [PiLp.add_apply, literatureIntegerShift_apply]
    linarith [hz i]
  change f r = f x
  rw [hr]
  exact literaturePeriodic_integerShift hp z x

def literatureTorusFunction {n : ℕ} (f : LiteratureSpace n → ℂ) :
    UnitAddTorus (Fin n) → ℂ := fun θ => f (literatureTorusRepresentative θ)

theorem literatureTorusFunction_mk {n : ℕ} (f : LiteratureSpace n → ℂ)
    (hp : LiteraturePeriodic f) (x : LiteratureSpace n) :
    literatureTorusFunction f (fun j => (x j : UnitAddCircle)) = f x :=
  literatureTorusRepresentative_periodic f hp x

def literatureCubeProjection (n : ℕ) (x : LiteratureUnitCube n) :
    UnitAddTorus (Fin n) := fun i => (x.val i : UnitAddCircle)

theorem literatureCubeProjection_continuous (n : ℕ) :
    Continuous (literatureCubeProjection n) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (p := (1 : ℝ))).comp
    ((EuclideanSpace.proj i : LiteratureSpace n →L[ℝ] ℝ).continuous.comp
      continuous_subtype_val)

theorem literatureCubeProjection_surjective (n : ℕ) :
    Function.Surjective (literatureCubeProjection n) := by
  intro θ
  refine ⟨⟨literatureTorusRepresentative θ, literatureTorusRepresentative_mem θ⟩, ?_⟩
  funext i
  exact literatureTorusRepresentative_coe θ i

theorem literatureCubeProjection_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (literatureCubeProjection n) := by
  letI : CompactSpace (LiteratureUnitCube n) :=
    isCompact_iff_compactSpace.mp (isCompact_literatureUnitCube n)
  exact (literatureCubeProjection_continuous n).isClosedMap.isQuotientMap
    (literatureCubeProjection_continuous n) (literatureCubeProjection_surjective n)

theorem literatureTorusFunction_continuous {n : ℕ} (f : LiteratureSpace n → ℂ)
    (hf : Continuous f) (hp : LiteraturePeriodic f) :
    Continuous (literatureTorusFunction f) := by
  apply (literatureCubeProjection_isQuotientMap n).continuous_iff.mpr
  have he : literatureTorusFunction f ∘ literatureCubeProjection n =
      fun x : LiteratureUnitCube n => f x.val := by
    funext x
    exact literatureTorusFunction_mk f hp x.val
  rw [he]
  exact hf.comp continuous_subtype_val

def literatureTorusContinuous {n : ℕ} (f : LiteratureSpace n → ℂ)
    (hf : Continuous f) (hp : LiteraturePeriodic f) : C(UnitAddTorus (Fin n), ℂ) :=
  ⟨literatureTorusFunction f, literatureTorusFunction_continuous f hf hp⟩

theorem literatureCharacter_eq_mFourier {n : ℕ} (k : LiteratureFrequency n)
    (x : LiteratureSpace n) :
    LiteratureCharacter k x = UnitAddTorus.mFourier k (fun i => (x i : UnitAddCircle)) := by
  change LiteratureCharacter k x = ∏ i : Fin n, fourier (k i) (x i : UnitAddCircle)
  simp only [fourier_coe_apply, div_one, ← Complex.exp_sum]
  unfold LiteratureCharacter
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem literatureCharacter_norm_eq_one {n : ℕ} (k : LiteratureFrequency n)
    (x : LiteratureSpace n) : ‖LiteratureCharacter k x‖ = 1 := by
  rw [literatureCharacter_eq_mFourier]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem literatureTorusFunction_fourierCoeff {n : ℕ}
    (f : LiteratureSpace n → ℂ) (k : LiteratureFrequency n) :
    UnitAddTorus.mFourierCoeff (literatureTorusFunction f) k =
      LiteratureFourierCoefficient f k := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ k (0 : Fin n → ℝ)]
  unfold LiteratureFourierCoefficient
  rw [integral_literatureUnitCube_eq_piIoc]
  simp only [Pi.zero_apply, zero_add]
  apply setIntegral_congr_fun (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc))
  intro x hx
  have hr := literatureTorusRepresentative_mk_of_mem x hx
  have hc : UnitAddTorus.mFourier (-k) (fun j => (x j : UnitAddCircle)) =
      LiteratureCharacter (-k) (WithLp.toLp 2 x) :=
    (literatureCharacter_eq_mFourier (-k) (WithLp.toLp 2 x)).symm
  simp only [smul_eq_mul, hc, literatureTorusFunction, hr]
  exact mul_comm _ _

theorem literatureFourier_hasSum_of_summable_norm {n : ℕ}
    (f : LiteratureSpace n → ℂ) (hf : Continuous f) (hp : LiteraturePeriodic f)
    (hs : Summable (fun k : LiteratureFrequency n => ‖LiteratureFourierCoefficient f k‖))
    (x : LiteratureSpace n) :
    HasSum (fun k : LiteratureFrequency n =>
      LiteratureFourierCoefficient f k * LiteratureCharacter k x) (f x) := by
  let fT := literatureTorusContinuous f hf hp
  have hc (k : LiteratureFrequency n) :
      UnitAddTorus.mFourierCoeff fT k = LiteratureFourierCoefficient f k :=
    literatureTorusFunction_fourierCoeff f k
  have hsc : Summable (UnitAddTorus.mFourierCoeff fT) := by
    exact hs.of_norm.congr (fun k => (hc k).symm)
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsc
    (fun i => (x i : UnitAddCircle))
  simpa only [hc, smul_eq_mul, ← literatureCharacter_eq_mFourier,
    fT, literatureTorusContinuous, ContinuousMap.coe_mk,
    literatureTorusFunction_mk f hp x, literatureTorusFunction_fourierCoeff] using h

theorem literatureFourier_hasSumUniformly_of_summable_norm {n : ℕ}
    (f : LiteratureSpace n → ℂ) (hf : Continuous f) (hp : LiteraturePeriodic f)
    (hs : Summable (fun k : LiteratureFrequency n => ‖LiteratureFourierCoefficient f k‖)) :
    HasSumUniformly (fun (k : LiteratureFrequency n) (x : LiteratureSpace n) =>
      LiteratureFourierCoefficient f k * LiteratureCharacter k x) f := by
  have hu : HasSumUniformlyOn
      (fun (k : LiteratureFrequency n) (x : LiteratureSpace n) =>
        LiteratureFourierCoefficient f k * LiteratureCharacter k x)
      (fun x => ∑' k : LiteratureFrequency n,
        LiteratureFourierCoefficient f k * LiteratureCharacter k x) Set.univ :=
    HasSumUniformlyOn.of_norm_le_summable hs (fun k x _ => by
      simp only [norm_mul, literatureCharacter_norm_eq_one, mul_one, le_refl])
  have he : (fun x : LiteratureSpace n => ∑' k : LiteratureFrequency n,
      LiteratureFourierCoefficient f k * LiteratureCharacter k x) = f := by
    funext x
    exact (literatureFourier_hasSum_of_summable_norm f hf hp hs x).tsum_eq
  rw [he] at hu
  exact hasSumUniformlyOn_univ_iff.mp hu

end

end NSEGR.NativeLiterature
