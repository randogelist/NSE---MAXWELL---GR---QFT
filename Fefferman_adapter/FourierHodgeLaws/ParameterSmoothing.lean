import FourierHodgeLaws.ClosedHalfspaceSmooth
import FourierHodgeLaws.CosineMultiplier
import FourierHodgeLaws.ParameterCoefficients
import FourierHodgeLaws.UniformCoefficientBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
Joint inverse-Laplacian parameter calculus for the actual scalar Fourier
integral. The finite-order induction ranges over all smooth periodic inputs.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime
open Set Filter
open scoped BigOperators ContDiff Topology

noncomputable section

def inverseScalarSeries (f : Pressure) (z : ℝ × Vec) : ℂ :=
  SingularClosure.scalarFourierSeries (inverseScalarCoeff (f z.1)) z.2

def scalarSpaceDerivative (f : Pressure) (j : Fin 3) : Pressure :=
  fun t x => fderiv ℝ (f t) x (unitVector j)

def timeProjection : (ℝ × Vec) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ Vec)

def spaceProjection (j : Fin 3) : (ℝ × Vec) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((EuclideanSpace.proj j).comp
    (ContinuousLinearMap.snd ℝ ℝ Vec))

def phaseProjection (k : Frequency) : (ℝ × Vec) →L[ℝ] ℂ :=
  (SingularClosure.fourierPhaseCLM k).comp (ContinuousLinearMap.snd ℝ ℝ Vec)

def inverseScalarSeriesTerm (f : Pressure) (k : Frequency) (z : ℝ × Vec) : ℂ :=
  SingularClosure.fourierCharacter k z.2 * inverseScalarCoeff (f z.1) k

def inverseScalarSeriesTermDerivative (f : Pressure) (k : Frequency)
    (z : ℝ × Vec) : (ℝ × Vec) →L[ℝ] ℂ :=
  SingularClosure.fourierCharacter k z.2 •
    (inverseScalarCoeff (scalarTimeDerivative f z.1) k • timeProjection +
      inverseScalarCoeff (f z.1) k • phaseProjection k)

def inverseScalarSeriesDerivative (f : Pressure) (z : ℝ × Vec) :
    (ℝ × Vec) →L[ℝ] ℂ :=
  inverseScalarSeries (fun t => scalarTimeDerivative f t) z • timeProjection +
    ∑ j : Fin 3, inverseScalarSeries (scalarSpaceDerivative f j) z • spaceProjection j

theorem inverseScalarCoeff_trajectory_smooth (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => inverseScalarCoeff (f z.1) k)
      forwardSpacetime := by
  exact contDiffOn_const.mul (scalarCoeff_trajectory_smooth f hf k)

theorem inverseScalarSeriesTerm_continuousOn (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) : ContinuousOn (inverseScalarSeriesTerm f k) forwardSpacetime := by
  exact (((SingularClosure.fourierCharacter_contDiff k).comp contDiff_snd).contDiffOn.mul
    (inverseScalarCoeff_trajectory_smooth f hf k)).continuousOn

theorem inverseScalarSeries_continuousOn (f : Pressure) (hf : SmoothPressure f)
    (hp : PeriodicPressure f) : ContinuousOn (inverseScalarSeries f) forwardSpacetime := by
  intro z hz
  let T : ℝ := z.1 + 1
  let s : Set (ℝ × Vec) := {y | 0 ≤ y.1 ∧ y.1 ≤ T}
  obtain ⟨M, hMsum, _, hM⟩ := uniform_inverseScalarCoeff_moment_bound f hf hp T 0
  have hsSub : s ⊆ forwardSpacetime := fun y hy => hy.1
  have hcont : ContinuousOn (inverseScalarSeries f) s := by
    apply continuousOn_tsum
      (fun k => (inverseScalarSeriesTerm_continuousOn f hf k).mono hsSub) hMsum
    intro k y hy
    simpa only [inverseScalarSeriesTerm, norm_mul,
      SingularClosure.fourierCharacter_norm, one_mul, pow_zero, mul_one] using
      hM y.1 hy k
  have hzS : z ∈ s := ⟨hz, le_add_of_nonneg_right zero_le_one⟩
  have hupper : {y : ℝ × Vec | y.1 < T} ∈ 𝓝 z :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds (by dsimp [T]; linarith)
  have hsN : s ∈ 𝓝[forwardSpacetime] z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hupper] with y hy hyT
    exact ⟨hy, hyT.le⟩
  exact (hcont z hzS).mono_of_mem_nhdsWithin hsN

theorem inverseScalarSeriesTerm_hasFDerivAt (f : Pressure) (hf : SmoothPressure f)
    (k : Frequency) {z : ℝ × Vec} (hz : 0 < z.1) :
    HasFDerivAt (inverseScalarSeriesTerm f k)
      (inverseScalarSeriesTermDerivative f k z) z := by
  have hc := (SingularClosure.fourierCharacter_hasFDerivAt k z.2).comp z
    (hasFDerivAt_snd (𝕜 := ℝ) (p := z))
  have hb := ((scalarCoeff_hasDerivAt_pos f hf k hz).const_mul
    (inverseLaplacianSymbol k : ℂ)).hasFDerivAt.comp z
      (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  convert hc.mul hb using 1 <;> ext v <;>
    simp [inverseScalarSeriesTerm, inverseScalarSeriesTermDerivative, timeProjection, phaseProjection,
      inverseScalarCoeff, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      smul_eq_mul, Complex.real_smul] <;> ring

theorem inverseScalarSeriesTermDerivative_bound (f : Pressure) (k : Frequency)
    (z : ℝ × Vec) :
    ‖inverseScalarSeriesTermDerivative f k z‖ ≤
      ‖inverseScalarCoeff (scalarTimeDerivative f z.1) k‖ * ‖timeProjection‖ +
      (‖inverseScalarCoeff (f z.1) k‖ * ‖SingularClosure.fourierPhaseCLM k‖) *
        ‖ContinuousLinearMap.snd ℝ ℝ Vec‖ := by
  rw [inverseScalarSeriesTermDerivative, norm_smul,
    SingularClosure.fourierCharacter_norm, one_mul]
  calc
    _ ≤ ‖inverseScalarCoeff (scalarTimeDerivative f z.1) k • timeProjection‖ +
        ‖inverseScalarCoeff (f z.1) k • phaseProjection k‖ := norm_add_le _ _
    _ = ‖inverseScalarCoeff (scalarTimeDerivative f z.1) k‖ * ‖timeProjection‖ +
        ‖inverseScalarCoeff (f z.1) k‖ * ‖phaseProjection k‖ := by simp only [norm_smul]
    _ ≤ ‖inverseScalarCoeff (scalarTimeDerivative f z.1) k‖ * ‖timeProjection‖ +
        ‖inverseScalarCoeff (f z.1) k‖ *
          (‖SingularClosure.fourierPhaseCLM k‖ * ‖ContinuousLinearMap.snd ℝ ℝ Vec‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by ring

theorem phaseProjection_eq_sum (k : Frequency) :
    phaseProjection k = ∑ j : Fin 3, SingularClosure.derivativeSymbol j k • spaceProjection j := by
  ext v <;>
    simp [phaseProjection, SingularClosure.fourierPhaseCLM, spaceProjection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply]

theorem inverseScalarSeriesTermDerivative_eq_partials (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f) (k : Frequency)
    {z : ℝ × Vec} (hz : 0 ≤ z.1) :
    inverseScalarSeriesTermDerivative f k z =
      inverseScalarSeriesTerm (fun t => scalarTimeDerivative f t) k z • timeProjection +
      ∑ j : Fin 3, inverseScalarSeriesTerm (scalarSpaceDerivative f j) k z • spaceProjection j := by
  simp only [inverseScalarSeriesTermDerivative, phaseProjection_eq_sum,
    smul_add, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold inverseScalarSeriesTerm scalarSpaceDerivative inverseScalarCoeff
  rw [scalarCoeff_coordinateDerivative (f z.1) (cubeSlice_contDiff f hf hz)
    (hp z.1 hz) j k]
  ring

theorem inverseScalarSeriesTerm_summable (f : Pressure) (hf : SmoothPressure f)
    (hp : PeriodicPressure f) {z : ℝ × Vec} (hz : 0 ≤ z.1) :
    Summable (fun k => inverseScalarSeriesTerm f k z) :=
  SingularClosure.scalarFourierSeries_summable
    (rapid_inverseScalarCoeff (f z.1) (cubeSlice_contDiff f hf hz)
      (hp z.1 hz)).summable_norm z.2

theorem inverseScalarSeriesTermDerivative_summable (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f)
    {z : ℝ × Vec} (hz : 0 ≤ z.1) :
    Summable (fun k => inverseScalarSeriesTermDerivative f k z) := by
  have htime := (inverseScalarSeriesTerm_summable _
    (scalarTimeDerivative_smooth hf) (scalarTimeDerivative_periodic hp) hz).smul_const
      timeProjection
  have hspace (j : Fin 3) := (inverseScalarSeriesTerm_summable (scalarSpaceDerivative f j)
    (scalarSpatialDerivative_smooth hf j) (scalarSpatialDerivative_periodic hp j) hz).smul_const
      (spaceProjection j)
  exact (htime.add (summable_sum (fun j _ => hspace j))).congr
    (fun k => (inverseScalarSeriesTermDerivative_eq_partials f hf hp k hz).symm)

theorem tsum_inverseScalarSeriesTermDerivative (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f)
    {z : ℝ × Vec} (hz : 0 ≤ z.1) :
    (∑' k, inverseScalarSeriesTermDerivative f k z) = inverseScalarSeriesDerivative f z := by
  have htime := inverseScalarSeriesTerm_summable _
    (scalarTimeDerivative_smooth hf) (scalarTimeDerivative_periodic hp) hz
  have hspace (j : Fin 3) := inverseScalarSeriesTerm_summable (scalarSpaceDerivative f j)
    (scalarSpatialDerivative_smooth hf j) (scalarSpatialDerivative_periodic hp j) hz
  simp_rw [inverseScalarSeriesTermDerivative_eq_partials f hf hp _ hz]
  rw [(htime.smul_const timeProjection).tsum_add
    (summable_sum (fun j _ => (hspace j).smul_const (spaceProjection j)))]
  rw [Summable.tsum_finsetSum (fun j _ => (hspace j).smul_const (spaceProjection j))]
  rw [htime.tsum_smul_const]
  unfold inverseScalarSeriesDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (hspace j).tsum_smul_const (spaceProjection j)

theorem inverseScalarSeriesDerivative_continuousOn (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f) :
    ContinuousOn (inverseScalarSeriesDerivative f) forwardSpacetime := by
  apply ContinuousOn.add
  · exact (inverseScalarSeries_continuousOn _ (scalarTimeDerivative_smooth hf)
      (scalarTimeDerivative_periodic hp)).smul continuousOn_const
  · exact continuousOn_finsetSum _ (fun j _ =>
      (inverseScalarSeries_continuousOn (scalarSpaceDerivative f j)
        (scalarSpatialDerivative_smooth hf j) (scalarSpatialDerivative_periodic hp j)).smul
          continuousOn_const)

theorem inverseScalarSeries_hasFDerivAt_pos (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f)
    {z : ℝ × Vec} (hz : 0 < z.1) :
    HasFDerivAt (inverseScalarSeries f) (inverseScalarSeriesDerivative f z) z := by
  let T : ℝ := z.1 + 1
  let s : Set (ℝ × Vec) := Ioo (0 : ℝ) T ×ˢ (univ : Set Vec)
  obtain ⟨Mt, hMtSum, _, hMt⟩ := uniform_inverseScalarCoeff_moment_bound
    (fun t => scalarTimeDerivative f t) (scalarTimeDerivative_smooth hf)
    (scalarTimeDerivative_periodic hp) T 0
  obtain ⟨Mx, hMxSum, _, hMx⟩ := uniform_inverseScalarCoeff_moment_bound f hf hp T 1
  let M : Frequency → ℝ := fun k => Mt k * ‖timeProjection‖ +
    Mx k * ‖ContinuousLinearMap.snd ℝ ℝ Vec‖
  have hMsum : Summable M :=
    (hMtSum.mul_right ‖timeProjection‖).add
      (hMxSum.mul_right ‖ContinuousLinearMap.snd ℝ ℝ Vec‖)
  have hsOpen : IsOpen s := isOpen_Ioo.prod isOpen_univ
  have hsConvex : Convex ℝ s := (convex_Ioo (0 : ℝ) T).prod convex_univ
  have hzS : z ∈ s := ⟨⟨hz, by dsimp [T]; linarith⟩, mem_univ _⟩
  have hbound (k : Frequency) (y : ℝ × Vec) (hy : y ∈ s) :
      ‖inverseScalarSeriesTermDerivative f k y‖ ≤ M k := by
    have ht : y.1 ∈ Icc (0 : ℝ) T := ⟨hy.1.1.le, hy.1.2.le⟩
    have hbt : ‖inverseScalarCoeff (scalarTimeDerivative f y.1) k‖ ≤ Mt k := by
      simpa only [pow_zero, mul_one] using hMt y.1 ht k
    have hbx : ‖inverseScalarCoeff (f y.1) k‖ *
        ‖SingularClosure.fourierPhaseCLM k‖ ≤ Mx k := by
      simpa only [pow_one] using hMx y.1 ht k
    exact (inverseScalarSeriesTermDerivative_bound f k y).trans
      (add_le_add (mul_le_mul_of_nonneg_right hbt (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hbx (norm_nonneg _)))
  have hd := hasFDerivAt_tsum_of_isPreconnected hMsum hsOpen hsConvex.isPreconnected
    (fun k y hy => inverseScalarSeriesTerm_hasFDerivAt f hf k hy.1.1)
    hbound hzS (inverseScalarSeriesTerm_summable f hf hp hz.le) hzS
  rw [tsum_inverseScalarSeriesTermDerivative f hf hp hz.le] at hd
  exact hd

theorem inverseScalarSeries_hasFDerivWithinAt (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f)
    {z : ℝ × Vec} (hz : z ∈ forwardSpacetime) :
    HasFDerivWithinAt (inverseScalarSeries f) (inverseScalarSeriesDerivative f z)
      forwardSpacetime z := by
  have hcont : ContinuousOn (inverseScalarSeries f) (closure positiveSpacetime) := by
    rw [closure_positiveSpacetime]
    exact inverseScalarSeries_continuousOn f hf hp
  have hcontD : ContinuousOn (inverseScalarSeriesDerivative f) (closure positiveSpacetime) := by
    rw [closure_positiveSpacetime]
    exact inverseScalarSeriesDerivative_continuousOn f hf hp
  have h := hasFDerivWithinAt_closure_of_continuous_jets
    isOpen_positiveSpacetime convex_positiveSpacetime hcont hcontD
    (fun y hy => inverseScalarSeries_hasFDerivAt_pos f hf hp hy.1)
    (show z ∈ closure positiveSpacetime by rwa [closure_positiveSpacetime])
  simpa only [closure_positiveSpacetime] using h

theorem inverseScalarSeries_contDiffOn_nat (n : ℕ) (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f) :
    ContDiffOn ℝ n (inverseScalarSeries f) forwardSpacetime := by
  induction n generalizing f with
  | zero => exact contDiffOn_zero.mpr (inverseScalarSeries_continuousOn f hf hp)
  | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        uniqueDiffOn_forwardSpacetime).2
      refine ⟨by simp, inverseScalarSeriesDerivative f, ?_, ?_⟩
      · apply ContDiffOn.add
        · exact (ih _ (scalarTimeDerivative_smooth hf)
            (scalarTimeDerivative_periodic hp)).smul contDiffOn_const
        · exact ContDiffOn.sum (fun j _ =>
            (ih (scalarSpaceDerivative f j) (scalarSpatialDerivative_smooth hf j)
              (scalarSpatialDerivative_periodic hp j)).smul contDiffOn_const)
      · intro z hz
        exact inverseScalarSeries_hasFDerivWithinAt f hf hp hz

theorem inverseScalarSeries_contDiffOn (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f) :
    ContDiffOn ℝ ∞ (inverseScalarSeries f) forwardSpacetime := by
  apply contDiffOn_infty.mpr
  intro n
  exact inverseScalarSeries_contDiffOn_nat n f hf hp

theorem scalarL_trajectory_smooth {f : Pressure}
    (hf : SmoothPressure f) (hp : PeriodicPressure f) :
    SmoothPressure (fun t => scalarL (f t)) := by
  have h := Complex.reCLM.contDiff.comp_contDiffOn (inverseScalarSeries_contDiffOn f hf hp)
  apply h.congr
  intro z hz
  exact congrFun (scalarL_eq_realFourierSeries (f z.1)
    (cubeSlice_contDiff f hf hz) (hp z.1 hz)) z.2

theorem vectorL_trajectory_smooth {B : Velocity}
    (hB : SmoothVelocity B) (hp : PeriodicVelocity B) :
    SmoothVelocity (fun t => vectorL (B t)) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  have hBi : SmoothPressure (fun t x => B t x i) := (contDiffOn_piLp 2).mp hB i
  have hpi : PeriodicPressure (fun t x => B t x i) :=
    fun t ht x j => congrArg (fun v : Vec => v i) (hp t ht x j)
  apply (scalarL_trajectory_smooth hBi hpi).congr
  intro z hz
  exact congrFun (vectorL_component (B z.1)
    (NSEMaxwell.Classical.velocity_slice_smooth hB hz) (hp z.1 hz) i) z.2

end

end NSEMaxwell.HodgeProof
