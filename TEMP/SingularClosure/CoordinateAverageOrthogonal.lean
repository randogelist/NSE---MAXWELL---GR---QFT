import SingularClosure.CoordinateAverage
import SingularClosure.PhysicalEnstrophy

/-!
# Fubini identities for concrete physical coordinate averaging

All averages and pairings are actual Lebesgue integrals. This module supplies
commutation of the coordinate averages on continuous fields.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem coordinateAverage_double_integrable (i j : Fin 3) (a : Field)
    (ha : Continuous a) (x : Vec) :
    Integrable (fun st : ℝ × ℝ =>
      a (resetCoordinate i st.1 (resetCoordinate j st.2 x)))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) := by
  have hreset : Continuous (fun st : ℝ × ℝ =>
      resetCoordinate i st.1 (resetCoordinate j st.2 x)) := by
    simpa only [Function.comp_def] using
      (resetCoordinate_smooth i).continuous.comp
        (((resetCoordinate_continuous_slice j x).comp continuous_snd).prodMk
          continuous_fst)
  have hint : IntegrableOn (fun st : ℝ × ℝ =>
      a (resetCoordinate i st.1 (resetCoordinate j st.2 x)))
      ((Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1)) volume :=
    (ha.comp hreset).continuousOn.integrableOn_compact
      ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod isCompact_Icc)
  simpa only [IntegrableOn, Measure.volume_eq_prod, Measure.prod_restrict] using hint

/-- The actual coordinate averages commute, without a Fourier representation premise. -/
theorem coordinateAverage_commute (i j : Fin 3) (a : Field)
    (ha : Continuous a) :
    coordinateAverage i (coordinateAverage j a) =
      coordinateAverage j (coordinateAverage i a) := by
  by_cases hij : i = j
  · subst j
    rfl
  funext x
  change (∫ s in Icc (0 : ℝ) 1, ∫ t in Icc (0 : ℝ) 1,
    a (resetCoordinate j t (resetCoordinate i s x))) =
      ∫ t in Icc (0 : ℝ) 1, ∫ s in Icc (0 : ℝ) 1,
        a (resetCoordinate i s (resetCoordinate j t x))
  simp_rw [← resetCoordinate_commute i j hij]
  exact integral_integral_swap (coordinateAverage_double_integrable i j a ha x)

def unitIntervalMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

def unitProductMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => unitIntervalMeasure)

instance unitIntervalMeasure_probability : IsProbabilityMeasure unitIntervalMeasure := by
  constructor
  simp [unitIntervalMeasure]

instance unitProductMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (unitProductMeasure n) := by
  unfold unitProductMeasure
  infer_instance

theorem unitPiCube_eq (n : ℕ) :
    Icc (0 : Fin n → ℝ) (fun _ => 1) =
      Set.univ.pi (fun _ : Fin n => Icc (0 : ℝ) 1) := by
  ext x
  constructor
  · intro hx i _
    exact ⟨hx.1 i, hx.2 i⟩
  · intro hx
    exact ⟨fun i => (hx i (Set.mem_univ i)).1,
      fun i => (hx i (Set.mem_univ i)).2⟩

section Codomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_unitCube_productMeasure (f : Vec → E) :
    (∫ x in unitCube, f x) =
      ∫ x : Fin 3 → ℝ, f (WithLp.toLp 2 x) ∂unitProductMeasure 3 := by
  have hchange := (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding f unitCube
  have hpre : (@WithLp.toLp 2 (Fin 3 → ℝ)) ⁻¹' unitCube =
      Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1) := by
    ext x
    change (∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1) ↔
      (∀ i : Fin 3, i ∈ Set.univ → 0 ≤ x i ∧ x i ≤ 1)
    exact ⟨fun h i _ => h i, fun h i => h i (Set.mem_univ i)⟩
  rw [hpre] at hchange
  rw [← hchange]
  change (∫ x : Fin 3 → ℝ, f (WithLp.toLp 2 x)
    ∂((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin 3 => Icc (0 : ℝ) 1)))) = _
  rw [Measure.restrict_pi_pi]
  rfl

theorem continuous_integrable_unitProduct (n : ℕ) (f : (Fin n → ℝ) → E)
    (hf : Continuous f) : Integrable f (unitProductMeasure n) := by
  have hint : IntegrableOn f (Icc (0 : Fin n → ℝ) (fun _ => 1)) volume :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  rw [unitPiCube_eq] at hint
  change Integrable f
    ((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin n => Icc (0 : ℝ) 1))) at hint
  rw [Measure.restrict_pi_pi] at hint
  exact hint

/-- Fubini disintegration of the actual Euclidean cube along any coordinate. -/
theorem integral_unitCube_disintegrate (j : Fin 3) (f : Vec → E)
    (hf : Continuous f) :
    (∫ x in unitCube, f x) =
      ∫ y : Fin 2 → ℝ, (∫ s in Icc (0 : ℝ) 1,
        f (WithLp.toLp 2 (j.insertNth s y))) ∂unitProductMeasure 2 := by
  let e : (ℝ × (Fin 2 → ℝ)) ≃ᵐ (Fin 3 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm
  have he : MeasurePreserving e
      (unitIntervalMeasure.prod (unitProductMeasure 2)) (unitProductMeasure 3) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => unitIntervalMeasure) j).symm
  have hc : Continuous (fun x : Fin 3 → ℝ => f (WithLp.toLp 2 x)) :=
    hf.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))
  have hint := continuous_integrable_unitProduct 3 _ hc
  have hp : Integrable (fun z => f (WithLp.toLp 2 (e z)))
      (unitIntervalMeasure.prod (unitProductMeasure 2)) :=
    (he.integrable_comp_emb e.measurableEmbedding).2 hint
  rw [integral_unitCube_productMeasure, ← he.integral_comp']
  rw [integral_prod_symm _ hp]
  rfl

end Codomain

theorem resetCoordinate_insertNth (j : Fin 3) (s t : ℝ) (y : Fin 2 → ℝ) :
    resetCoordinate j s (WithLp.toLp 2 (j.insertNth t y)) =
      WithLp.toLp 2 (j.insertNth s y) := by
  ext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i, rfl⟩ <;>
    simp [resetCoordinate, Fin.succAbove_ne]

theorem coordinateAverage_insertNth (j : Fin 3) (a : Field) (s t : ℝ)
    (y : Fin 2 → ℝ) :
    coordinateAverage j a (WithLp.toLp 2 (j.insertNth s y)) =
      coordinateAverage j a (WithLp.toLp 2 (j.insertNth t y)) := by
  simp only [coordinateAverage, resetCoordinate_insertNth]

/-- Averaging preserves the actual spatial integral on the physical unit cube. -/
theorem coordinateAverage_spatialMean (j : Fin 3) (a : Field)
    (ha : Continuous a) : spatialMean (coordinateAverage j a) = spatialMean a := by
  unfold spatialMean
  rw [integral_unitCube_disintegrate j _ (coordinateAverage_continuous j a ha),
    integral_unitCube_disintegrate j _ ha]
  apply integral_congr_ae
  filter_upwards with y
  simp_rw [coordinateAverage_insertNth j a _ 0 y]
  simp only [coordinateAverage, resetCoordinate_insertNth]
  simp

theorem coordinateAverage_preserves_meanZero (j : Fin 3) (a : Field)
    (ha : Continuous a) (hm : MeanZero a) : MeanZero (coordinateAverage j a) := by
  refine ⟨(coordinateAverage_continuous j a ha).continuousOn.integrableOn_compact
    isCompact_unitCube, ?_⟩
  rw [coordinateAverage_spatialMean j a ha]
  exact hm.2

/-- Self-adjointness of literal coordinate averaging for the physical L² pairing. -/
theorem coordinateAverage_selfAdjoint (j : Fin 3) (a b : Field)
    (ha : Continuous a) (hb : Continuous b) :
    (∫ x in unitCube, inner ℝ (coordinateAverage j a x) (b x)) =
      ∫ x in unitCube, inner ℝ (a x) (coordinateAverage j b x) := by
  rw [integral_unitCube_disintegrate j _ ((coordinateAverage_continuous j a ha).inner hb),
    integral_unitCube_disintegrate j _ (ha.inner (coordinateAverage_continuous j b hb))]
  apply integral_congr_ae
  filter_upwards with y
  let x : Vec := WithLp.toLp 2 (j.insertNth 0 y)
  have haint := coordinateAverage_slice_integrable j a ha x
  have hbint := coordinateAverage_slice_integrable j b hb x
  have haavg : (∫ s in Icc (0 : ℝ) 1,
      a (WithLp.toLp 2 (j.insertNth s y))) = coordinateAverage j a x := by
    simp only [coordinateAverage, x, resetCoordinate_insertNth]
  have hbavg : (∫ s in Icc (0 : ℝ) 1,
      b (WithLp.toLp 2 (j.insertNth s y))) = coordinateAverage j b x := by
    simp only [coordinateAverage, x, resetCoordinate_insertNth]
  have haint' : IntegrableOn (fun s : ℝ => a (WithLp.toLp 2 (j.insertNth s y)))
      (Icc (0 : ℝ) 1) volume := by
    simpa only [x, resetCoordinate_insertNth] using haint
  have hbint' : IntegrableOn (fun s : ℝ => b (WithLp.toLp 2 (j.insertNth s y)))
      (Icc (0 : ℝ) 1) volume := by
    simpa only [x, resetCoordinate_insertNth] using hbint
  simp_rw [coordinateAverage_insertNth j a _ 0 y,
    coordinateAverage_insertNth j b _ 0 y]
  change (∫ s in Icc (0 : ℝ) 1,
    inner ℝ (coordinateAverage j a x) (b (WithLp.toLp 2 (j.insertNth s y)))) =
      ∫ s in Icc (0 : ℝ) 1,
        inner ℝ (a (WithLp.toLp 2 (j.insertNth s y))) (coordinateAverage j b x)
  calc
    _ = inner ℝ (coordinateAverage j a x) (coordinateAverage j b x) := by
      simpa only [innerSL_apply_apply, hbavg] using!
        (innerSL ℝ (coordinateAverage j a x)).integral_comp_comm hbint'
    _ = inner ℝ (coordinateAverage j b x) (coordinateAverage j a x) :=
      real_inner_comm _ _
    _ = ∫ s in Icc (0 : ℝ) 1,
        inner ℝ (coordinateAverage j b x) (a (WithLp.toLp 2 (j.insertNth s y))) := by
      symm
      simpa only [innerSL_apply_apply, haavg] using!
        (innerSL ℝ (coordinateAverage j b x)).integral_comp_comm haint'
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      exact real_inner_comm _ _

end

end SingularClosure
