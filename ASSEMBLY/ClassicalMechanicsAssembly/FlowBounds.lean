import ClassicalMechanics.TimeCalculus
import NSEMaxwell.PeriodicIntegration
import SingularClosure.PeriodicCover
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Uniform whole-slab bounds derived from the exact smooth periodic velocity
hypotheses. No flow-existence or smooth-dependence assumption is used.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open ClassicalMechanics NSEMaxwell.Classical Set
open scoped ContDiff

noncomputable section

/-- Methlib's integer-period endpoint, transported without changing coordinates. -/
theorem flow_integer_period {E : Type*} {f : Vec → E}
    (hp : SpatialPeriodic f) (z : Fin 3 → ℤ) :
    Function.Periodic f (SingularClosure.integerShift z) := by
  apply SingularClosure.spatialPeriodic_integerShift
  exact hp

/-- Reduction to the closed fundamental cell, for an arbitrary periodic codomain. -/
theorem flow_periodic_cell_representative {E : Type*} {f : Vec → E}
    (hp : SpatialPeriodic f) (x : Vec) :
    ∃ y ∈ unitCube, f y = f x := by
  let z : Fin 3 → ℤ := fun i => ⌊x i⌋
  let y : Vec := x - SingularClosure.integerShift z
  refine ⟨y, ?_, ?_⟩
  · intro i
    change 0 ≤ x i - SingularClosure.integerShift z i ∧
      x i - SingularClosure.integerShift z i ≤ 1
    rw [SingularClosure.integerShift_apply]
    constructor
    · exact sub_nonneg.mpr (Int.floor_le (x i))
    · have hi := Int.lt_floor_add_one (x i)
      change x i - (⌊x i⌋ : ℝ) ≤ 1
      linarith
  · have h := flow_integer_period hp z y
    simpa [y] using h.symm

/-- Compact-cell boundedness, uniform in time and all spatial labels. -/
theorem flow_periodic_uniform_bound {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {f : ℝ → Vec → E}
    (hc : ContinuousOn (fun z : ℝ × Vec => f z.1 z.2) (finiteSpacetime T))
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (f t)) :
    ∃ B : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, ‖f t x‖ ≤ B := by
  have hcell : IsCompact (Icc (0 : ℝ) T ×ˢ unitCube) :=
    isCompact_Icc.prod NSEMaxwell.PeriodicIntegration.isCompact_unitCube
  obtain ⟨C, hC⟩ := hcell.exists_bound_of_continuousOn
    (hc.mono (fun z hz => hz.1))
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro t ht x
  obtain ⟨y, hy, hxy⟩ := flow_periodic_cell_representative (hp t ht) x
  rw [← hxy]
  exact (hC (t, y) ⟨ht, hy⟩).trans (le_max_left _ _)

/-- The actual ordinary spatial derivative is jointly continuous on the slab. -/
theorem flow_spatial_fderiv_continuousOn {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u) :
    ContinuousOn (fun z : ℝ × Vec => fderiv ℝ (u z.1) z.2) (finiteSpacetime T) := by
  have hd := hu.continuousOn_fderivWithin (uniqueDiffOn_finiteSpacetime hT)
    (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hc := hd.clm_comp
    (continuousOn_const (c := ContinuousLinearMap.inr ℝ ℝ Vec))
  apply hc.congr
  intro z hz
  ext v
  exact finite_spatial_restriction_fderiv hu hz z.2 v

/-- The full uniform field and Lipschitz bounds required by Picard--Lindelof. -/
theorem periodic_velocity_uniform_bounds {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t)) :
    ∃ B K : ℝ≥0,
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec, ‖u t x‖ ≤ B) ∧
      (∀ t ∈ Icc (0 : ℝ) T, LipschitzWith K (u t)) := by
  obtain ⟨B, hB⟩ := flow_periodic_uniform_bound hu.continuousOn hp
  obtain ⟨K, hK⟩ := flow_periodic_uniform_bound
    (flow_spatial_fderiv_continuousOn hT hu)
    (fun t ht => NSEMaxwell.PeriodicIntegration.fderiv_periodic (hp t ht))
  refine ⟨B, K, hB, ?_⟩
  intro t ht
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((finite_velocity_slice_smooth hu ht).differentiable (by simp))
  intro x
  exact_mod_cast hK t ht x

/-- Closed-interval time continuity at every fixed spatial point. -/
theorem flow_velocity_time_continuousOn {T : ℝ} {u : Velocity}
    (hu : SmoothVelocityOn T u) (x : Vec) :
    ContinuousOn (fun t => u t x) (Icc (0 : ℝ) T) := by
  exact hu.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ ht => ht)

end

end ClassicalMechanicsAssembly
