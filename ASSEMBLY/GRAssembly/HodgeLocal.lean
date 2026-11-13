import GRAssembly.HodgeTime
import ML019.Endpoint
import ML020.Endpoint
import ML021.Endpoint
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
GC02 finite-slab localization. A time-only cutoff preserves complete spatial
slices near the evaluation time; the source halfspace is reached only after
an explicit smooth global extension and a unit time translation.
-/
set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
noncomputable section

/-- Global smooth inputs may be translated so the source evaluation time is 1. -/
theorem poissonInverse_hasDerivAt_global (f : Pressure)
    (hf : ContDiff ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2))
    (hp : ∀ s : ℝ, SpatialPeriodic (f s)) (t : ℝ) (x : Vec) :
    HasDerivAt (fun s => poissonInverse (f s) x)
      (poissonInverse (scalarLocalTimeDerivative f t) x) t := by
  let g : Pressure := fun s y => f (s - 1 + t) y
  have hg : NSEMaxwell.Classical.SmoothPressure g :=
    (hf.comp (((contDiff_fst.sub contDiff_const).add contDiff_const).prodMk
      contDiff_snd)).contDiffOn
  have hgp : NSEMaxwell.Classical.PeriodicPressure g := fun s _ => hp (s - 1 + t)
  have hD : scalarLocalTimeDerivative g 1 = scalarLocalTimeDerivative f t := by
    funext y
    have hd : Differentiable ℝ (fun s => f s y) :=
      (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
    have he := (hd t).hasDerivAt.comp_of_eq 1
      (((hasDerivAt_id (1 : ℝ)).sub_const 1).add_const t) (by simp)
    have he' : HasDerivAt (fun s => g s y) (scalarLocalTimeDerivative f t y) 1 := by
      simpa only [g, Function.comp_def, mul_one, scalarLocalTimeDerivative] using he
    exact he'.deriv
  have h := poissonInverse_hasDerivAt_pos g hg hgp (t := 1) zero_lt_one x
  rw [hD] at h
  have he := h.comp_of_eq t
    (((hasDerivAt_id t).sub_const t).add_const 1) (by simp)
  simpa [Function.comp_def, g] using he

/-- The analogous translation for the actual cube mean. -/
theorem scalarMean_hasDerivAt_global (f : Pressure)
    (hf : ContDiff ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2)) (t : ℝ) :
    HasDerivAt (fun s => scalarMean (f s))
      (scalarMean (scalarLocalTimeDerivative f t)) t := by
  let g : Pressure := fun s y => f (s - 1 + t) y
  have hg : NSEMaxwell.Classical.SmoothPressure g :=
    (hf.comp (((contDiff_fst.sub contDiff_const).add contDiff_const).prodMk
      contDiff_snd)).contDiffOn
  have hD : scalarLocalTimeDerivative g 1 = scalarLocalTimeDerivative f t := by
    funext y
    have hd : Differentiable ℝ (fun s => f s y) :=
      (hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
    have he := (hd t).hasDerivAt.comp_of_eq 1
      (((hasDerivAt_id (1 : ℝ)).sub_const 1).add_const t) (by simp)
    have he' : HasDerivAt (fun s => g s y) (scalarLocalTimeDerivative f t y) 1 := by
      simpa only [g, Function.comp_def, mul_one, scalarLocalTimeDerivative] using he
    exact he'.deriv
  have h := scalarMean_hasDerivAt_pos g hg (t := 1) zero_lt_one
  rw [hD] at h
  have he := h.comp_of_eq t
    (((hasDerivAt_id t).sub_const t).add_const 1) (by simp)
  simpa [Function.comp_def, g] using he

/-- Smooth zero extension by a time-only cutoff supported inside the open slab. -/
theorem cutoff_mul_contDiff (f : Pressure) {I : Set ℝ} (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ I) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => χ z.1 * f z.1 z.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z.1 ∈ tsupport χ
  · exact (hχ.comp contDiff_fst).contDiffAt.mul
      ((hf z (hsupp hz)).contDiffAt
        ((hI.preimage continuous_fst).mem_nhds (hsupp hz)))
  · have hzero : χ =ᶠ[𝓝 z.1] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
    have hz' : ∀ᶠ y : ℝ × Vec in 𝓝 z, χ y.1 = 0 :=
      continuousAt_fst.tendsto.eventually hzero
    exact contDiffAt_const.congr_of_eventuallyEq
      (hz'.mono (fun y hy => by simp only [hy, zero_mul, Pi.zero_apply]))

/-- A smooth periodic slab has a global smooth periodic extension near any
chosen time, with equality of full spatial slices on one common neighborhood. -/
theorem exists_smooth_periodic_extension (f : Pressure) {I : Set ℝ}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ s ∈ I, SpatialPeriodic (f s)) {t : ℝ} (ht : t ∈ I) :
    ∃ g : Pressure, ContDiff ℝ ∞ (fun z : ℝ × Vec => g z.1 z.2) ∧
      (∀ s : ℝ, SpatialPeriodic (g s)) ∧ g =ᶠ[𝓝 t] f := by
  obtain ⟨r, hr, hrI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds ht)
  let χ : ContDiffBump t :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hsupp : tsupport (χ : ℝ → ℝ) ⊆ I := by
    rw [GRTemp.ML021.endpoint χ]
    exact (closedBall_subset_ball (show χ.rOut < r by dsimp [χ]; linarith)).trans hrI
  let g : Pressure := fun s y => χ s * f s y
  refine ⟨g, cutoff_mul_contDiff f hI hf χ (GRTemp.ML019.endpoint χ) hsupp, ?_, ?_⟩
  · intro s y i
    by_cases hs : χ s = 0
    · simp only [g, hs, zero_mul]
    · have hsmem : s ∈ tsupport (χ : ℝ → ℝ) :=
        subset_closure (show s ∈ Function.support (χ : ℝ → ℝ) from hs)
      change χ s * f s (y + unitVector i) = χ s * f s y
      rw [hp s (hsupp hsmem) y i]
  · filter_upwards [ball_mem_nhds t χ.rIn_pos] with s hs
    funext y
    change χ s * f s y = f s y
    rw [GRTemp.ML020.endpoint χ (ball_subset_closedBall hs), one_mul]

/-- GC02: native ordinary-time differentiation on an arbitrary open smooth slab. -/
theorem poissonInverse_hasDerivAt_local (f : Pressure) {I : Set ℝ}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ s ∈ I, SpatialPeriodic (f s)) {t : ℝ} (ht : t ∈ I) (x : Vec) :
    HasDerivAt (fun s => poissonInverse (f s) x)
      (poissonInverse (scalarLocalTimeDerivative f t) x) t := by
  obtain ⟨g, hg, hgp, heq⟩ := exists_smooth_periodic_extension f hI hf hp ht
  have hD : scalarLocalTimeDerivative g t = scalarLocalTimeDerivative f t := by
    funext y
    exact (heq.mono (fun s hs => congrFun hs y)).deriv_eq
  have h := poissonInverse_hasDerivAt_global g hg hgp t x
  rw [hD] at h
  exact h.congr_of_eventuallyEq
    (heq.symm.mono (fun s hs => congrArg (fun a : ScalarField => poissonInverse a x) hs))

theorem poissonInverse_localTimeDerivative (f : Pressure) {I : Set ℝ}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ s ∈ I, SpatialPeriodic (f s)) {t : ℝ} (ht : t ∈ I) :
    scalarLocalTimeDerivative (fun s => poissonInverse (f s)) t =
      poissonInverse (scalarLocalTimeDerivative f t) := by
  funext x
  exact (poissonInverse_hasDerivAt_local f hI hf hp ht x).deriv

/-- GC02: actual mean/ordinary-derivative commutation on the same open slab. -/
theorem scalarMean_hasDerivAt_local (f : Pressure) {I : Set ℝ}
    (hI : IsOpen I)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) {z | z.1 ∈ I})
    (hp : ∀ s ∈ I, SpatialPeriodic (f s)) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => scalarMean (f s))
      (scalarMean (scalarLocalTimeDerivative f t)) t := by
  obtain ⟨g, hg, hgp, heq⟩ := exists_smooth_periodic_extension f hI hf hp ht
  have hD : scalarLocalTimeDerivative g t = scalarLocalTimeDerivative f t := by
    funext y
    exact (heq.mono (fun s hs => congrFun hs y)).deriv_eq
  have h := scalarMean_hasDerivAt_global g hg t
  rw [hD] at h
  exact h.congr_of_eventuallyEq
    (heq.symm.mono (fun s hs => congrArg scalarMean hs))

end
end NSEGR.Assembly
