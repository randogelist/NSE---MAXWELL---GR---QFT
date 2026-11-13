import GRAdapter.Fields

/-! Native unit-cell calculus and periodicity for the GR reconstruction.
Adapted from the already audited NSEMaxwell.PeriodicIntegration/FourierPeriodic
proofs; all statements below use NSEGR's own concrete field operators.
No inversion or analytic convergence conclusion is inferred from periodicity. -/

set_option autoImplicit false
namespace NSEGR
open Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

theorem fderiv_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec → E} (hp : SpatialPeriodic f) : SpatialPeriodic (fderiv ℝ f) := by
  intro x i
  have hfun : (fun y : Vec => f (y + unitVector i)) = f := funext (fun y => hp y i)
  rw [← fderiv_comp_add_right (unitVector i), hfun]

theorem spatialPartial_periodic {a : Field} (hp : SpatialPeriodic a)
    (i : Fin 3) : SpatialPeriodic (spatialPartial a i) := by
  intro x j
  exact congrArg (fun L : Vec →L[ℝ] Vec => L (unitVector i)) (fderiv_periodic hp x j)

theorem divergence_periodic {a : Field} (hp : SpatialPeriodic a) :
    SpatialPeriodic (divergence a) := by
  intro x j
  unfold divergence
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun v : Vec => v i) (spatialPartial_periodic hp i x j)

theorem gradient_periodic {f : ScalarField} (hp : SpatialPeriodic f) :
    SpatialPeriodic (gradient f) := by
  intro x j
  ext i
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) (fderiv_periodic hp x j)

theorem laplacian_periodic {a : Field} (hp : SpatialPeriodic a) :
    SpatialPeriodic (laplacian a) := by
  intro x j
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i hi
  exact spatialPartial_periodic (spatialPartial_periodic hp i) i x j

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

/-- The native Euclidean unit cell has exactly unit Lebesgue volume. -/
theorem volume_unitCube : volume unitCube = 1 := by
  have hm : MeasurePreserving piToVec := PiLp.volume_preserving_toLp (Fin 3)
  have hvol := hm.measure_preimage_emb piToVec.toHomeomorph.measurableEmbedding unitCube
  rw [piToVec_preimage_cube] at hvol
  rw [← hvol, ← Set.pi_univ_Icc, volume_pi_pi]
  simp [Real.volume_Icc]

theorem scalarMean_const (c : ℝ) : scalarMean (fun _ : Vec => c) = c := by
  simp [scalarMean, measureReal_def, volume_unitCube]

theorem spatialMean_const (c : Vec) : spatialMean (fun _ : Vec => c) = c := by
  simp [spatialMean, measureReal_def, volume_unitCube]

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
private theorem pi_integral_spatialPartial_zero
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
    calc
      (∑ j : Fin 3, F' j x (Pi.single j 1)) = F' i x (Pi.single i 1) := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          simp [F', hji]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      _ = fderiv ℝ f x (Pi.single i 1) := by simp [F']
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
  have hzero := pi_integral_spatialPartial_zero f hf hp' i
  simp only [hdf] at hzero
  have hm : MeasurePreserving piToVec := PiLp.volume_preserving_toLp (Fin 3)
  have hchange := hm.setIntegral_preimage_emb
    piToVec.toHomeomorph.measurableEmbedding
      (fun x => fderiv ℝ a x (unitVector i)) unitCube
  rw [piToVec_preimage_cube] at hchange
  exact hchange.symm.trans hzero

/-- Every smooth periodic coordinate derivative has exactly zero cube mean. -/
theorem spatialMean_spatialPartial_zero {a : Field}
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) (i : Fin 3) :
    spatialMean (spatialPartial a i) = 0 :=
  integral_fderiv_unitVector_zero ha hp i

theorem spatialMean_apply {a : Field} (ha : Continuous a) (i : Fin 3) :
    spatialMean a i = ∫ x in unitCube, a x i := by
  exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) (𝕜 := ℝ) i).integral_comp_comm
    (integrableOn_unitCube_of_continuous ha)).symm

theorem gradient_smooth {f : ScalarField} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradient f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  apply (contDiff_piLp 2).mpr
  intro i
  exact hd.clm_apply contDiff_const

theorem spatialMean_gradient_zero {f : ScalarField}
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) :
    spatialMean (gradient f) = 0 := by
  ext i
  rw [spatialMean_apply (gradient_smooth hf).continuous i]
  exact integral_fderiv_unitVector_zero hf hp i

theorem cosineKernel_add_unit_left (k : Frequency) (x y : Vec) (i : Fin 3) :
    cosineKernel k (x + unitVector i) y = cosineKernel k x y := by
  have hsum :
      (∑ j : Fin 3, (k j : ℝ) * ((x + unitVector i) j - y j)) =
        (∑ j : Fin 3, (k j : ℝ) * (x j - y j)) + (k i : ℝ) := by
    calc
      (∑ j : Fin 3, (k j : ℝ) * ((x + unitVector i) j - y j)) =
          ∑ j : Fin 3,
            ((k j : ℝ) * (x j - y j) + (k j : ℝ) * unitVector i j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [PiLp.add_apply]
        ring
      _ = (∑ j : Fin 3, (k j : ℝ) * (x j - y j)) + (k i : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [unitVector, PiLp.single_apply, mul_ite]
  unfold cosineKernel
  rw [hsum]
  have hphase :
      2 * Real.pi * ((∑ j : Fin 3, (k j : ℝ) * (x j - y j)) + (k i : ℝ)) =
        2 * Real.pi * (∑ j : Fin 3, (k j : ℝ) * (x j - y j)) +
          (k i : ℝ) * (2 * Real.pi) := by ring
  rw [hphase]
  exact Real.cos_add_int_mul_two_pi _ _

theorem cosineKernel_symm (k : Frequency) (x y : Vec) :
    cosineKernel k x y = cosineKernel k y x := by
  have hphase :
      2 * Real.pi * (∑ i : Fin 3, (k i : ℝ) * (x i - y i)) =
        -(2 * Real.pi * (∑ i : Fin 3, (k i : ℝ) * (y i - x i))) := by
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold cosineKernel
  rw [hphase, Real.cos_neg]

theorem cosineKernel_add_unit_right (k : Frequency) (x y : Vec) (i : Fin 3) :
    cosineKernel k x (y + unitVector i) = cosineKernel k x y := by
  rw [cosineKernel_symm k x (y + unitVector i),
    cosineKernel_add_unit_left, cosineKernel_symm]


theorem poissonInverse_periodic (f : ScalarField) : SpatialPeriodic (poissonInverse f) := by
  intro x i
  simp only [poissonInverse, cosineKernel_add_unit_left]

theorem leray_periodic {a : Field} (ha : SpatialPeriodic a) : SpatialPeriodic (leray a) := by
  intro x i
  simp only [leray, ha x i, gradient_periodic (poissonInverse_periodic (divergence a)) x i]

end
end NSEGR
