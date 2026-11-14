import FourierHodgeLaws.UniformCoefficientBounds
import FourierHodgeLaws.ParameterCoefficients
import SingularClosure.FourierSobolevOperators
import SingularClosure.TorusSobolevReal
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Actual physical Fourier curves in the Sobolev norm

The curve is the norm-convergent sum of the actual weighted cube-integral
coefficients in `lp`, transported through the native Sobolev isometry.
Compact physical derivative bounds supply a locally uniform summable majorant.
The derivative theorem is therefore a Sobolev norm derivative, rather than
only a family of coefficient derivatives.

Positive-time smoothness suffices for the positive-time derivative theorem.
The forward trace theorem separately assumes the supplied physical field is
jointly smooth on the closed half-space. Neither theorem assumes mean zero.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology ContDiff BigOperators
open SingularClosure
open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.HodgeProof

namespace NSEGR.Strengthening
noncomputable section

/-- A single actual weighted physical coefficient in the native Hilbert sequence space. -/
def physicalFourierTerm (m : ℕ) (a : SingularClosure.Field) (ki : FourierIndex) :
    FourierVectorSequence :=
  lp.single 2 ki (sobolevWeightedCoeff m (datumFourierCoeff a) ki)

/-- The actual physical Fourier value; on every smooth periodic slice the sum converges in norm. -/
def physicalFourierValue (m : ℕ) (a : SingularClosure.Field) : TorusSobolev m :=
  (torusSobolevRepr m).symm (∑' ki : FourierIndex, physicalFourierTerm m a ki)

def physicalFourierCurve (m : ℕ) (u : SingularClosure.Velocity) (t : ℝ) :
    TorusSobolev m :=
  physicalFourierValue m (u t)

theorem physicalFourierTerm_hasSum (m : ℕ) (a : SingularClosure.Field)
    (ha : ContDiff ℝ ∞ a) (hp : SingularClosure.SpatialPeriodic a) :
    HasSum (physicalFourierTerm m a)
      (torusSobolevRepr m (smoothDatumSobolev m a ha hp)) := by
  exact lp.hasSum_single (by norm_num) (torusSobolevRepr m (smoothDatumSobolev m a ha hp))

theorem physicalFourierValue_eq_smoothDatumSobolev
    (m : ℕ) (a : SingularClosure.Field)
    (ha : ContDiff ℝ ∞ a) (hp : SingularClosure.SpatialPeriodic a) :
    physicalFourierValue m a = smoothDatumSobolev m a ha hp := by
  unfold physicalFourierValue
  rw [(physicalFourierTerm_hasSum m a ha hp).tsum_eq]
  exact (torusSobolevRepr m).symm_apply_apply _

theorem physicalFourierValue_coeff (m : ℕ) (a : SingularClosure.Field)
    (ha : ContDiff ℝ ∞ a) (hp : SingularClosure.SpatialPeriodic a) :
    (physicalFourierValue m a).val = datumFourierCoeff a := by
  rw [physicalFourierValue_eq_smoothDatumSobolev m a ha hp]
  rfl

/-- The physical compactness bound supplies an absolutely summable norm majorant. -/
theorem physicalFourier_uniform_weighted_bound
    (u : NSEMaxwell.Classical.Velocity) (hu : SmoothVelocity u)
    (hp : PeriodicVelocity u) (T : ℝ) (m : ℕ) :
    ∃ M : FourierIndex → ℝ, Summable M ∧ (∀ ki, 0 ≤ M ki) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ ki : FourierIndex,
        ‖sobolevWeightedCoeff m (datumFourierCoeff (u t)) ki‖ ≤ M ki := by
  obtain ⟨C, hCnon, hC⟩ := uniform_fourierDecayConstant u hu T (2 * (m + 4))
  let A : ℝ := (4 : ℝ) ^ (m + 4) * C
  let M : FourierIndex → ℝ := fun ki => A * (torusSobolevWeight ki.1)⁻¹ ^ 4
  have hAnon : 0 ≤ A := mul_nonneg (by positivity) hCnon
  have hMnon : ∀ ki, 0 ≤ M ki := fun ki => mul_nonneg hAnon (by positivity)
  have hMsum : Summable M := by
    apply (summable_prod_of_nonneg hMnon).2
    refine ⟨fun _ => summable_fintype _, ?_⟩
    simpa only [M, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using
      (summable_torusSobolevWeight_inv_four.mul_left A).mul_left (3 : ℝ)
  refine ⟨M, hMsum, hMnon, ?_⟩
  intro t ht ki
  have hdec : torusSobolevWeight ki.1 ^ (m + 4) *
      ‖datumFourierCoeff (u t) ki.1 ki.2‖ ≤ A := by
    have h := smooth_datum_sobolev_decay (m + 2) (u t)
      (velocity_slice_smooth hu ht.1) (hp t ht.1) ki.1 ki.2
    have hfirst : torusSobolevWeight ki.1 ^ (m + 4) *
        ‖datumFourierCoeff (u t) ki.1 ki.2‖ ≤
        (4 : ℝ) ^ (m + 4) * fourierDecayConstant (2 * (m + 4)) (u t) := by
      simpa [smoothDatumDecayConstant, Nat.add_assoc] using h
    exact hfirst.trans (mul_le_mul_of_nonneg_left (hC t ht) (by positivity))
  rw [torusSobolev_weightedCoeff_norm]
  calc
    _ = (torusSobolevWeight ki.1 ^ (m + 4) *
        ‖datumFourierCoeff (u t) ki.1 ki.2‖) * (torusSobolevWeight ki.1)⁻¹ ^ 4 := by
      rw [pow_add]
      field_simp [(torusSobolevWeight_pos ki.1).ne'] <;> ring
    _ ≤ M ki := mul_le_mul_of_nonneg_right hdec (by positivity)

theorem physicalFourierTerm_continuousOn
    (u : NSEMaxwell.Classical.Velocity) (hu : SmoothVelocity u)
    (m : ℕ) (ki : FourierIndex) :
    ContinuousOn (fun t => physicalFourierTerm m (u t) ki) (Ici (0 : ℝ)) := by
  have hcoeff := (datumFourierCoeff_contDiffOn u hu ki.1 ki.2).continuousOn
  exact (lp.singleContinuousLinearMap ℝ (fun _ : FourierIndex => ℂ) 2 ki).continuous
    |>.comp_continuousOn
      ((continuousOn_const : ContinuousOn
        (fun _ : ℝ => (torusSobolevWeight ki.1 : ℂ) ^ m) (Ici (0 : ℝ))).mul hcoeff)

/-- The physical Fourier transform is continuous in every Sobolev norm through zero. -/
theorem physicalFourierCurve_continuousOn
    (u : NSEMaxwell.Classical.Velocity) (hu : SmoothVelocity u)
    (hp : PeriodicVelocity u) (m : ℕ) :
    ContinuousOn (physicalFourierCurve m u) (Ici (0 : ℝ)) := by
  intro t ht
  obtain ⟨M, hMsum, _, hM⟩ := physicalFourier_uniform_weighted_bound u hu hp (t + 1) m
  have hseries : ContinuousOn
      (fun s => ∑' ki : FourierIndex, physicalFourierTerm m (u s) ki)
      (Icc (0 : ℝ) (t + 1)) := by
    apply continuousOn_tsum
      (fun ki => (physicalFourierTerm_continuousOn u hu m ki).mono (fun _ h => h.1)) hMsum
    intro ki s hs
    simpa only [physicalFourierTerm, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
      using hM s hs ki
  have hstate : ContinuousOn (physicalFourierCurve m u) (Icc (0 : ℝ) (t + 1)) :=
    (torusSobolevRepr m).symm.continuous.comp_continuousOn hseries
  apply (hstate t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
  have hupper : Iio (t + 1) ∈ 𝓝[Ici (0 : ℝ)] t :=
    (Iio_mem_nhds (lt_add_one t)).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hupper] with s hs hsu
  exact ⟨hs, hsu.le⟩

/-- The initial all-Sobolev trace is derived from joint physical smoothness. -/
theorem physicalFourierCurve_initial_trace
    (u : NSEMaxwell.Classical.Velocity) (hu : SmoothVelocity u)
    (hp : PeriodicVelocity u) (m : ℕ) :
    Tendsto (physicalFourierCurve m u) (𝓝[>] (0 : ℝ))
      (𝓝 (physicalFourierCurve m u 0)) :=
  (physicalFourierCurve_continuousOn u hu hp m 0 (by simp)).mono
    (fun _ ht => ht.le)

theorem physicalFourierTerm_hasDerivAt
    (u : NSEMaxwell.Classical.Velocity) (hu : SmoothVelocity u)
    (m : ℕ) (ki : FourierIndex) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => physicalFourierTerm m (u s) ki)
      (physicalFourierTerm m (NSEMaxwell.Classical.timeDerivative u t) ki) t := by
  have hcoeff := (datumFourierCoeff_hasDerivWithinAt u hu ki.1 ki.2 ht.le).hasDerivAt
    (Ici_mem_nhds ht)
  have hweighted := hcoeff.const_mul ((torusSobolevWeight ki.1 : ℂ) ^ m)
  exact (lp.singleContinuousLinearMap ℝ (fun _ : FourierIndex => ℂ) 2 ki).hasFDerivAt
    |>.comp_hasDerivAt t hweighted

/-- Genuine differentiation in the actual Sobolev norm; the majorant is derived physically. -/
theorem physicalFourierCurve_hasDerivAt
    (u : NSEMaxwell.Classical.Velocity) (hu : SmoothVelocity u)
    (hp : PeriodicVelocity u) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (physicalFourierCurve m u)
      (physicalFourierValue m (NSEMaxwell.Classical.timeDerivative u t)) t := by
  obtain ⟨M, hMsum, _, hM⟩ := physicalFourier_uniform_weighted_bound
    (fun s => NSEMaxwell.Classical.timeDerivative u s)
    (timeDerivative_smooth hu) (timeDerivative_periodic hp) (t + 1) m
  have hbase : Summable (fun ki : FourierIndex => physicalFourierTerm m (u t) ki) :=
    (physicalFourierTerm_hasSum m (u t) (velocity_slice_smooth hu ht.le) (hp t ht.le)).summable
  have hseries : HasDerivAt
      (fun s => ∑' ki : FourierIndex, physicalFourierTerm m (u s) ki)
      (∑' ki : FourierIndex,
        physicalFourierTerm m (NSEMaxwell.Classical.timeDerivative u t) ki) t := by
    apply hasDerivAt_tsum_of_isPreconnected hMsum isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (fun ki s hs => physicalFourierTerm_hasDerivAt u hu m ki hs.1)
      (fun ki s hs => ?_) (show t ∈ Ioo (0 : ℝ) (t + 1) from ⟨ht, lt_add_one t⟩)
      hbase (show t ∈ Ioo (0 : ℝ) (t + 1) from ⟨ht, lt_add_one t⟩)
    simpa only [physicalFourierTerm, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
      using hM s ⟨hs.1.le, hs.2.le⟩ ki
  exact ((torusSobolevRepr m).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
    .hasFDerivAt.comp_hasDerivAt t hseries

/-- Positive-time physical smoothness alone gives the norm derivative; no initial smoothness is assumed. -/
theorem physicalFourierCurve_hasDerivAt_of_positive_smooth
    (u : NSEMaxwell.Classical.Velocity)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × NSEMaxwell.Classical.Vec => u z.1 z.2)
      {z | 0 < z.1})
    (hp : ∀ s : ℝ, 0 < s → SingularClosure.SpatialPeriodic (u s))
    (m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (physicalFourierCurve m u)
      (physicalFourierValue m (NSEMaxwell.Classical.timeDerivative u t)) t := by
  let c : ℝ := t / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have htc : 0 < t - c := by dsimp [c]; linarith
  let v : NSEMaxwell.Classical.Velocity := fun s x => u (s + c) x
  have hv : SmoothVelocity v := by
    have hg : ContDiffOn ℝ ∞
        (fun z : ℝ × NSEMaxwell.Classical.Vec => (z.1 + c, z.2))
        NSEMaxwell.Classical.forwardSpacetime :=
      ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
    exact hu.comp hg (fun z hz => add_pos_of_nonneg_of_pos hz hc)
  have hpv : PeriodicVelocity v := by
    intro s hs
    exact hp (s + c) (add_pos_of_nonneg_of_pos hs hc)
  have hshift : HasDerivAt (fun s : ℝ => s - c) 1 t :=
    (hasDerivAt_id t).sub_const c
  have hdt : NSEMaxwell.Classical.timeDerivative v (t - c) =
      NSEMaxwell.Classical.timeDerivative u t := by
    funext x
    have h := ((time_slice_hasDerivWithinAt hv htc.le x).hasDerivAt (Ici_mem_nhds htc))
      .comp t hshift
    have he : HasDerivAt (fun s : ℝ => u s x)
        (NSEMaxwell.Classical.timeDerivative v (t - c) x) t := by
      simpa only [v, sub_add_cancel, one_smul] using h
    exact (he.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht.le)).symm
  have h := (physicalFourierCurve_hasDerivAt v hv hpv m htc).comp t hshift
  simpa only [physicalFourierCurve, v, sub_add_cancel, one_smul, hdt] using h

end
end NSEGR.Strengthening
