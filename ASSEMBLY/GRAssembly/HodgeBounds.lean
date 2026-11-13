import GRAssembly.HodgeLocal
import SingularClosure.SmoothDatumSobolev

/-!
Joint smoothness on the original open slab and a universal fixed-order
spatial estimate for the actual negative-sign Poisson inverse.
-/
set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
noncomputable section

/-- Global joint smoothness follows by translating each time to the interior
of the retained halfspace theorem. -/
theorem poissonInverse_joint_smooth_global (f : Pressure)
    (hf : ContDiff ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2))
    (hp : ∀ s : ℝ, SpatialPeriodic (f s)) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => poissonInverse (f z.1) z.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  let g : Pressure := fun s y => f (s - 1 + z.1) y
  have hg : NSEMaxwell.Classical.SmoothPressure g :=
    (hf.comp (((contDiff_fst.sub contDiff_const).add contDiff_const).prodMk
      contDiff_snd)).contDiffOn
  have hgp : NSEMaxwell.Classical.PeriodicPressure g := fun s _ => hp (s - 1 + z.1)
  have hG := poissonInverse_halfspace_smooth hg hgp
  have hn : NSEMaxwell.Classical.forwardSpacetime ∈ 𝓝 (1, z.2) := by
    exact continuousAt_fst.preimage_mem_nhds (Ici_mem_nhds zero_lt_one)
  have hGa := (hG (1, z.2) (by change (0 : ℝ) ≤ 1; norm_num)).contDiffAt hn
  have hmap : ContDiff ℝ ∞ (fun w : ℝ × Vec => (w.1 - z.1 + 1, w.2)) :=
    ((contDiff_fst.sub contDiff_const).add contDiff_const).prodMk contDiff_snd
  have hGa' : ContDiffAt ℝ ∞ (fun w : ℝ × Vec => poissonInverse (g w.1) w.2)
      (z.1 - z.1 + 1, z.2) := by simpa using hGa
  simpa [Function.comp_def, g] using hGa'.comp z hmap.contDiffAt

/-- The output is jointly smooth on exactly the input's open time slab. -/
theorem poissonInverse_joint_smooth_on_open_slab (f : Pressure) {I : Set ℝ}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ s ∈ I, SpatialPeriodic (f s)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => poissonInverse (f z.1) z.2)
      {z | z.1 ∈ I} := by
  intro z hz
  obtain ⟨g, hg, hgp, heq⟩ := exists_smooth_periodic_extension f hI hf hp hz
  have he : (fun w : ℝ × Vec => poissonInverse (f w.1) w.2) =ᶠ[𝓝 z]
      (fun w : ℝ × Vec => poissonInverse (g w.1) w.2) := by
    filter_upwards [continuousAt_fst.tendsto.eventually heq] with w hw
    exact congrArg (fun a : ScalarField => poissonInverse a w.2) hw.symm
  exact ((poissonInverse_joint_smooth_global g hg hgp).contDiffAt.congr_of_eventuallyEq
    he).contDiffWithinAt

/-- Repeated actual spatial Fréchet differentiation in one coordinate. -/
def scalarSpatialIterate (j : Fin 3) : ℕ → ScalarField → ScalarField
  | 0, f => f
  | n + 1, f => fourierScalarPartial (scalarSpatialIterate j n f) j

theorem scalarSpatialIterate_smooth (j : Fin 3) (n : ℕ) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarSpatialIterate j n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact fourierScalarPartial_smooth _ ih j

theorem scalarSpatialIterate_periodic (j : Fin 3) (n : ℕ) (f : ScalarField)
    (hp : SpatialPeriodic f) : SpatialPeriodic (scalarSpatialIterate j n f) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact fourierScalarPartial_periodic _ ih j

theorem scalarLift_scalarSpatialIterate (j : Fin 3) (n : ℕ) (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) :
    SingularClosure.iteratedCoordinateDerivative j n (NSEMaxwell.HodgeProof.scalarLift f) =
      NSEMaxwell.HodgeProof.scalarLift (scalarSpatialIterate j n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [SingularClosure.iteratedCoordinateDerivative, ih]
      exact NSEMaxwell.HodgeProof.scalarLift_coordinateDerivative _
        (scalarSpatialIterate_smooth j n f hf) j

/-- A cube integral estimate with the measure factor retained explicitly. -/
theorem scalar_integral_norm_le (f : ScalarField) (hf : Continuous f) (B : ℝ)
    (hB : ∀ x ∈ unitCube, ‖f x‖ ≤ B) :
    (∫ x in unitCube, ‖f x‖) ≤ volume.real unitCube * B := by
  have hint : IntegrableOn (fun x : Vec => ‖f x‖) unitCube volume :=
    hf.norm.continuousOn.integrableOn_compact NSEMaxwell.PeriodicIntegration.isCompact_unitCube
  have hconst : IntegrableOn (fun _ : Vec => B) unitCube volume :=
    NSEMaxwell.PeriodicIntegration.integrableOn_unitCube_of_continuous continuous_const
  calc
    _ ≤ ∫ _x in unitCube, B := by
      apply integral_mono_ae hint hconst
      exact (ae_restrict_mem
        NSEMaxwell.PeriodicIntegration.isCompact_unitCube.isClosed.measurableSet).mono
          (fun x hx => hB x hx)
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

/-- The retained Fourier decay constant requires only order zero and three
pure eighth derivatives; it is independent of any later derivative order. -/
theorem scalar_fourierDecayConstant_eight_le (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (B : ℝ)
    (hzero : ∀ x ∈ unitCube, ‖f x‖ ≤ B)
    (height : ∀ j : Fin 3, ∀ x ∈ unitCube, ‖scalarSpatialIterate j 8 f x‖ ≤ B) :
    SingularClosure.fourierDecayConstant 8 (NSEMaxwell.HodgeProof.scalarLift f) ≤
      12 * (volume.real unitCube * B) := by
  have h0 := scalar_integral_norm_le f hf.continuous B hzero
  have h8 (j : Fin 3) := scalar_integral_norm_le (scalarSpatialIterate j 8 f)
    (scalarSpatialIterate_smooth j 8 f hf).continuous B (height j)
  unfold SingularClosure.fourierDecayConstant SingularClosure.coordinateDerivativeL1
  simp only [scalarLift_scalarSpatialIterate _ _ _ hf,
    NSEMaxwell.HodgeProof.scalarLift_component]
  calc
    _ ≤ ∑ _i : Fin 3, (volume.real unitCube * B +
        ∑ _j : Fin 3, volume.real unitCube * B) := by
      apply Finset.sum_le_sum
      intro i _
      exact add_le_add h0 (Finset.sum_le_sum (fun j _ => h8 j))
    _ = _ := by simp; ring

/-- A numerical majorant of the actual scalar Fourier coefficient. -/
theorem scalarCoeff_norm_le_eight (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (B : ℝ)
    (hzero : ∀ x ∈ unitCube, ‖f x‖ ≤ B)
    (height : ∀ j : Fin 3, ∀ x ∈ unitCube, ‖scalarSpatialIterate j 8 f x‖ ≤ B)
    (k : Frequency) :
    ‖NSEMaxwell.HodgeProof.scalarCoeff f k‖ ≤
      ((4 : ℝ) ^ 4 * (12 * (volume.real unitCube * B))) *
        (SingularClosure.torusSobolevWeight k)⁻¹ ^ 4 := by
  have h := SingularClosure.smooth_datum_sobolev_decay 2
    (NSEMaxwell.HodgeProof.scalarLift f)
    (NSEMaxwell.HodgeProof.scalarLift_contDiff f hf)
    (NSEMaxwell.HodgeProof.scalarLift_periodic f hp) k (0 : Fin 3)
  change SingularClosure.torusSobolevWeight k ^ 4 *
    ‖NSEMaxwell.HodgeProof.scalarCoeff f k‖ ≤
      (4 : ℝ) ^ 4 * SingularClosure.fourierDecayConstant 8
        (NSEMaxwell.HodgeProof.scalarLift f) at h
  have hd := h.trans (mul_le_mul_of_nonneg_left
    (scalar_fourierDecayConstant_eight_le f hf B hzero height) (by positivity))
  have hdiv : ‖NSEMaxwell.HodgeProof.scalarCoeff f k‖ ≤
      ((4 : ℝ) ^ 4 * (12 * (volume.real unitCube * B))) /
        SingularClosure.torusSobolevWeight k ^ 4 := by
    apply (le_div_iff₀ (pow_pos (SingularClosure.torusSobolevWeight_pos k) 4)).mpr
    simpa only [mul_comm] using hd
  simpa only [div_eq_mul_inv, inv_pow] using hdiv

/-- Fixed, strictly positive inverse bound; no dependence on the input or
on the order of derivatives subsequently substituted for the input. -/
def poissonInverseFixedLossConstant : ℝ :=
  (4 : ℝ) ^ 4 * 12 * (1 + volume.real unitCube) * SingularClosure.latticeSobolevConstant

theorem poissonInverseFixedLossConstant_pos : 0 < poissonInverseFixedLossConstant := by
  unfold poissonInverseFixedLossConstant
  have hv : 0 ≤ volume.real unitCube := ENNReal.toReal_nonneg
  exact mul_pos (mul_pos (by norm_num) (by linarith))
    SingularClosure.latticeSobolevConstant_pos

/-- Universal order-eight estimate for the actual Poisson inverse. -/
theorem poissonInverse_norm_le_eight (f : ScalarField)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (B : ℝ) (hB : 0 ≤ B)
    (hzero : ∀ x ∈ unitCube, ‖f x‖ ≤ B)
    (height : ∀ j : Fin 3, ∀ x ∈ unitCube, ‖scalarSpatialIterate j 8 f x‖ ≤ B)
    (x : Vec) : ‖poissonInverse f x‖ ≤ poissonInverseFixedLossConstant * B := by
  let A : ℝ := (4 : ℝ) ^ 4 * (12 * (volume.real unitCube * B))
  let w : Frequency → ℝ := fun k => (SingularClosure.torusSobolevWeight k)⁻¹ ^ 4
  have hw : Summable w := SingularClosure.summable_torusSobolevWeight_inv_four
  have hc := NSEMaxwell.HodgeProof.rapid_inverseScalarCoeff f hf hp
  have hcoeff (k : Frequency) : ‖NSEMaxwell.HodgeProof.inverseScalarCoeff f k‖ ≤ A * w k := by
    calc
      _ ≤ 1 * ‖NSEMaxwell.HodgeProof.scalarCoeff f k‖ := by
        rw [NSEMaxwell.HodgeProof.inverseScalarCoeff, norm_mul]
        exact mul_le_mul_of_nonneg_right
          (NSEMaxwell.HodgeProof.inverseLaplacianSymbol_complex_norm_le_one k) (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using scalarCoeff_norm_le_eight f hf hp B hzero height k
  have hsum : (∑' k, ‖NSEMaxwell.HodgeProof.inverseScalarCoeff f k‖) ≤ A * ∑' k, w k := by
    calc
      _ ≤ ∑' k, A * w k := tsum_le_tsum hcoeff hc.summable_norm (hw.mul_left A)
      _ = _ := tsum_mul_left
  have hnorm : ‖poissonInverse f x‖ ≤ ∑' k, ‖NSEMaxwell.HodgeProof.inverseScalarCoeff f k‖ := by
    rw [poissonInverse_eq_neg_scalarL, Pi.neg_apply, norm_neg,
      NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries f hf hp]
    unfold SingularClosure.realFourierSeries SingularClosure.scalarFourierSeries
    calc
      _ ≤ ‖∑' k, SingularClosure.fourierCharacter k x *
          NSEMaxwell.HodgeProof.inverseScalarCoeff f k‖ := RCLike.norm_re_le_norm _
      _ ≤ ∑' k, ‖SingularClosure.fourierCharacter k x *
          NSEMaxwell.HodgeProof.inverseScalarCoeff f k‖ := norm_tsum_le_tsum_norm (by
            simpa only [norm_mul, SingularClosure.fourierCharacter_norm, one_mul] using hc.summable_norm)
      _ = _ := by simp only [norm_mul, SingularClosure.fourierCharacter_norm, one_mul]
  have hv : 0 ≤ volume.real unitCube := ENNReal.toReal_nonneg
  have hw0 : 0 ≤ ∑' k, w k := tsum_nonneg (fun k => by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : (∑' k, w k) ≤ SingularClosure.latticeSobolevConstant := by
    change (∑' k, w k) ≤ 1 + ∑' k, w k
    linarith
  calc
    _ ≤ A * ∑' k, w k := hnorm.trans hsum
    _ ≤ A * SingularClosure.latticeSobolevConstant := mul_le_mul_of_nonneg_left hS hA
    _ ≤ poissonInverseFixedLossConstant * B := by
      dsimp [A, poissonInverseFixedLossConstant]
      nlinarith [mul_nonneg SingularClosure.latticeSobolevConstant_pos.le hB]

end
end NSEGR.Assembly
