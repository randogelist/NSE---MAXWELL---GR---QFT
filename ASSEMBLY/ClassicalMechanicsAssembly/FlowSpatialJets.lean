import ClassicalMechanicsAssembly.FlowBounds
import ClassicalMechanicsAssembly.FlowBanach
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
The spatial Taylor tower of the actual smooth periodic velocity, including
uniform bounds on every finite spatial jet. This instantiates the path-space
superposition theorem with no assumed path-space differentiability.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical
open scoped ContDiff NNReal

noncomputable section

section GeneralSpatialFamilies

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {T : ℝ} {f : ℝ → Vec → F}

theorem flow_family_slice_contDiff
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) (finiteSpacetime T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ContDiff ℝ ∞ (f t) := by
  exact hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun _ => ht)

theorem flow_family_fderiv_contDiffOn (hT : 0 < T)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) (finiteSpacetime T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => fderiv ℝ (f z.1) z.2) (finiteSpacetime T) := by
  have hd : ContDiffOn ℝ ∞
      (fderivWithin ℝ (fun z : ℝ × Vec => f z.1 z.2) (finiteSpacetime T))
      (finiteSpacetime T) := hf.fderivWithin (uniqueDiffOn_finiteSpacetime hT) (by simp)
  have hc := hd.clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ Vec))
  apply hc.congr
  intro z hz
  have hd' := (hf.differentiableOn (by simp) z hz).hasFDerivWithinAt
  have he := (hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hcomp := hd'.comp_hasFDerivAt z.2 he
    (Filter.Eventually.of_forall (fun _ => hz))
  exact hcomp.fderiv

theorem flow_family_uniform_lipschitz (hT : 0 < T)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) (finiteSpacetime T))
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (f t)) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith K (f t) := by
  obtain ⟨K, hK⟩ := flow_periodic_uniform_bound
    (flow_family_fderiv_contDiffOn hT hf).continuousOn
    (fun t ht => NSEMaxwell.PeriodicIntegration.fderiv_periodic (hp t ht))
  refine ⟨K, ?_⟩
  intro t ht
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((flow_family_slice_contDiff hf ht).differentiable (by simp))
  intro x
  exact_mod_cast hK t ht x

end GeneralSpatialFamilies

/-- Actual ordinary spatial derivatives of all orders. -/
def flowSpatialJet (u : Velocity) (r : ℕ) : ℝ → Vec → (Vec [×r]→L[ℝ] Vec) :=
  fun t => iteratedFDeriv ℝ r (u t)

theorem flowSpatialJet_contDiffOn {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u) (r : ℕ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => flowSpatialJet u r z.1 z.2)
      (finiteSpacetime T) := by
  induction r with
  | zero =>
      exact (continuousMultilinearCurryFin0 ℝ Vec Vec).symm.contDiff.comp_contDiffOn hu
  | succ r ih =>
      have hd := flow_family_fderiv_contDiffOn hT ih
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (r + 1) => Vec) Vec).symm.contDiff.comp_contDiffOn hd

theorem flowSpatialJet_periodic {u : Velocity} {t : ℝ}
    (hp : SpatialPeriodic (u t)) (r : ℕ) : SpatialPeriodic (flowSpatialJet u r t) := by
  intro x i
  have heq : (fun y : Vec => u t (y + unitVector i)) = u t := funext (fun y => hp y i)
  change iteratedFDeriv ℝ r (u t) (x + unitVector i) = iteratedFDeriv ℝ r (u t) x
  rw [← iteratedFDeriv_comp_add_right r (unitVector i) x, heq]

theorem flowSpatialJet_uniform_bound {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) (r : ℕ) :
    ∃ M : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, ‖flowSpatialJet u r t x‖ ≤ M :=
  flow_periodic_uniform_bound (flowSpatialJet_contDiffOn hT hu r).continuousOn
    (fun t ht => flowSpatialJet_periodic (hp t ht) r)

theorem flowSpatialJet_uniform_lipschitz {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) (r : ℕ) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith K (flowSpatialJet u r t) :=
  flow_family_uniform_lipschitz hT (flowSpatialJet_contDiffOn hT hu r)
    (fun t ht => flowSpatialJet_periodic (hp t ht) r)

/-- Continuous coefficient field on the actual compact-time product. -/
def flowSpatialJetMap {T : ℝ} (hT : 0 < T) {u : Velocity}
    (hu : SmoothVelocityOn T u) (r : ℕ) :
    C(Icc (0 : ℝ) T × Vec, Vec [×r]→L[ℝ] Vec) where
  toFun z := flowSpatialJet u r z.1 z.2
  continuous_toFun := (flowSpatialJet_contDiffOn hT hu r).continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun z => z.1.property)

/-- The native curry operator identifying successive actual derivatives. -/
def flowSpatialCurry (r : ℕ) :
    (Vec [×(r + 1)]→L[ℝ] Vec) →L[ℝ] (Vec →L[ℝ] (Vec [×r]→L[ℝ] Vec)) :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Vec) Vec).toContinuousLinearEquiv

/-- Full C-infinity superposition for the actual spatial jets of the supplied velocity. -/
theorem flowSpatialJet_superposition_contDiff {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) :
    ∀ r, ContDiff ℝ ∞ (flowPathSuperpositionTo (flowSpatialJetMap hT hu r)) := by
  choose K hK using fun r => flowSpatialJet_uniform_lipschitz hT hu hp (r + 1)
  apply flowPathSuperposition_contDiff_of_spatial_tower
    (fun r => Vec [×r]→L[ℝ] Vec) (flowSpatialJetMap hT hu) flowSpatialCurry
    K
  · intro r t x
    have hd := ((flow_family_slice_contDiff (flowSpatialJet_contDiffOn hT hu r)
      t.property).differentiable (by simp) x).hasFDerivAt
    exact hd
  · intro r t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Vec) Vec)
        (flowSpatialJet u (r + 1) t x))
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Vec) Vec)
        (flowSpatialJet u (r + 1) t y)) ≤ (K r : ℝ) * dist x y
    rw [(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Vec) Vec).dist_map]
    exact (hK r t t.property).dist_le_mul x y

/-- The actual velocity field restricted to the compact time domain. -/
def flowVelocityMap {T : ℝ} {u : Velocity} (hu : SmoothVelocityOn T u) :
    C(Icc (0 : ℝ) T × Vec, Vec) where
  toFun z := u z.1 z.2
  continuous_toFun := hu.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun z => z.1.property)

/-- E07 with all coefficient hypotheses discharged from the literal L1 premises. -/
theorem periodic_velocity_superposition_contDiff {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) :
    ContDiff ℝ ∞ (flowPathSuperpositionTo (flowVelocityMap hu)) := by
  have hzero := flowSpatialJet_superposition_contDiff hT hu hp 0
  have hc := (flowPathPostcomposition (I := Icc (0 : ℝ) T)
    (continuousMultilinearCurryFin0 ℝ Vec Vec).toContinuousLinearEquiv.toContinuousLinearMap).contDiff.comp hzero
  exact hc

end

end ClassicalMechanicsAssembly
