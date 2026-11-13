import ClassicalMechanics.TimeCalculus
import NSEMaxwell.Spacetime

/-!
# Exact passage between global time and positive closed slabs

The global derivative is the within derivative on `Ici 0`; the finite derivative
is the within derivative on `Icc 0 T`.  Restriction of the actual derivative,
followed by uniqueness on the positive closed interval, identifies them even at
both temporal endpoints.  No pressure normalization or off-domain extension is
introduced.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical
open scoped ContDiff

noncomputable section

/-- Every finite forward slab is contained in the global forward spacetime. -/
theorem finiteSpacetime_subset_forwardSpacetime (T : ℝ) :
    finiteSpacetime T ⊆ forwardSpacetime := by
  intro z hz
  exact hz.1

/-- Global smooth velocity restricts to any finite closed slab. -/
theorem global_smoothVelocityOn {u : Velocity} (hu : SmoothVelocity u) (T : ℝ) :
    SmoothVelocityOn T u := by
  exact hu.mono (finiteSpacetime_subset_forwardSpacetime T)

/-- Global smooth pressure restricts without changing its spatial gauge. -/
theorem global_smoothPressureOn {p : Pressure} (hp : SmoothPressure p) (T : ℝ) :
    SmoothPressureOn T p := by
  exact hp.mono (finiteSpacetime_subset_forwardSpacetime T)

/-- The actual finite and global temporal derivatives agree, including `0` and `T`. -/
theorem finiteTimeDerivative_eq_timeDerivative {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocity u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Vec) :
    finiteTimeDerivative T u t x = timeDerivative u t x := by
  have hd := NSEMaxwell.Spacetime.time_slice_hasDerivWithinAt hu ht.1 x
  have hsub : Icc (0 : ℝ) T ⊆ Ici (0 : ℝ) := fun _ hs => hs.1
  exact (hd.mono hsub).derivWithin (uniqueDiffOn_Icc hT t ht)

/-- The complete convective acceleration is unchanged by restriction. -/
theorem finiteMaterialAcceleration_eq_materialAcceleration {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocity u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Vec) :
    finiteMaterialAcceleration T u t x = materialAcceleration u t x := by
  unfold finiteMaterialAcceleration materialAcceleration
  rw [finiteTimeDerivative_eq_timeDerivative hT hu ht x]

/-- An actual global Eulerian equation restricts to every positive finite slab. -/
theorem global_equation_to_finite_equation {ν T : ℝ} (hT : 0 < T)
    {u : Velocity} {p : Pressure} (hu : SmoothVelocity u)
    (heq : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
      timeDerivative u t x + convection (u t) x +
        NSEMaxwell.Classical.gradient (p t) x = ν • laplacian (u t) x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x +
        NSEMaxwell.Classical.gradient (p t) x = ν • laplacian (u t) x := by
  intro t ht x
  rw [finiteMaterialAcceleration_eq_materialAcceleration hT hu ht x]
  exact heq t ht.1 x

/-- Positive slabs exhaust every nonnegative time, retaining the common global fields. -/
theorem finite_equations_to_global_equation {ν : ℝ}
    {u : Velocity} {p : Pressure} (hu : SmoothVelocity u)
    (heq : ∀ T : ℝ, 0 < T → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x +
        NSEMaxwell.Classical.gradient (p t) x = ν • laplacian (u t) x) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
      timeDerivative u t x + convection (u t) x +
        NSEMaxwell.Classical.gradient (p t) x = ν • laplacian (u t) x := by
  intro t ht x
  have hT : 0 < t + 1 := by linarith
  have hmem : t ∈ Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have h := heq (t + 1) hT t hmem x
  rw [finiteMaterialAcceleration_eq_materialAcceleration hT hu hmem x] at h
  exact h

/-- Exact global/finite equation equivalence; no existential solution selection is exchanged. -/
theorem global_equation_iff_finite_equations {ν : ℝ}
    {u : Velocity} {p : Pressure} (hu : SmoothVelocity u) :
    (∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
      timeDerivative u t x + convection (u t) x +
        NSEMaxwell.Classical.gradient (p t) x = ν • laplacian (u t) x) ↔
    (∀ T : ℝ, 0 < T → ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Vec,
      finiteMaterialAcceleration T u t x +
        NSEMaxwell.Classical.gradient (p t) x = ν • laplacian (u t) x) := by
  constructor
  · intro h T hT
    exact global_equation_to_finite_equation hT hu h
  · exact finite_equations_to_global_equation hu

end

end ClassicalMechanicsAssembly
