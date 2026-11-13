import ClassicalMechanics.FiniteSlab

/-!
# Newtonian Cauchy balance implies NSE

The actual pressure, datum, temporal domain, and regularity predicates are
unchanged. The stress-divergence identity is proved in the native adapter,
not supplied as a hypothesis.
-/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical

noncomputable section

theorem newtonianSolution_to_nseSolution
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NewtonianSolution ν a u p) : NSSolution ν a u p := by
  refine
    { velocity_smooth := h.velocity_smooth
      pressure_smooth := h.pressure_smooth
      velocity_periodic := h.velocity_periodic
      pressure_periodic := h.pressure_periodic
      divergence_free := h.divergence_free
      equation := ?_
      initial := h.initial }
  intro t ht x
  have hDiv : NSEMaxwell.Classical.divergence (u t) = 0 := by
    funext y
    exact h.divergence_free t ht y
  have hStress := congrFun
    (tensorDivergence_newtonianStress_of_divergence_zero ν
      (velocity_slice_smooth h.velocity_smooth ht)
      (pressure_slice_smooth h.pressure_smooth ht) hDiv) x
  change tensorDivergence (newtonianStress ν (u t) (p t)) x =
    -NSEMaxwell.Classical.gradient (p t) x +
      ν • NSEMaxwell.Classical.laplacian (u t) x at hStress
  have hBalance := h.momentum_balance t ht x
  rw [hStress] at hBalance
  change timeDerivative u t x + convection (u t) x =
    -NSEMaxwell.Classical.gradient (p t) x +
      ν • NSEMaxwell.Classical.laplacian (u t) x at hBalance
  rw [hBalance]
  abel

theorem newtonianB_implies_feffermanB (ν : ℝ)
    (h : NewtonianB ν) : FeffermanB ν := by
  intro a ha
  obtain ⟨u, p, hNewton⟩ := h a ha
  exact ⟨u, p, newtonianSolution_to_nseSolution hNewton⟩

theorem newtonianSolutionOn_to_nseSolutionOn
    {ν T : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NewtonianSolutionOn ν a T u p) : NSSolutionOn ν a T u p := by
  refine
    { velocity_smooth := h.velocity_smooth
      pressure_smooth := h.pressure_smooth
      velocity_periodic := h.velocity_periodic
      pressure_periodic := h.pressure_periodic
      divergence_free := h.divergence_free
      equation := ?_
      initial := h.initial
      pressure_normalized := h.pressure_normalized }
  intro t ht x
  have hDiv : NSEMaxwell.Classical.divergence (u t) = 0 := by
    funext y
    exact h.divergence_free t ht y
  have hStress := congrFun
    (tensorDivergence_newtonianStress_of_divergence_zero ν
      (finite_velocity_slice_smooth h.velocity_smooth ht)
      (finite_pressure_slice_smooth h.pressure_smooth ht) hDiv) x
  change tensorDivergence (newtonianStress ν (u t) (p t)) x =
    -NSEMaxwell.Classical.gradient (p t) x +
      ν • NSEMaxwell.Classical.laplacian (u t) x at hStress
  have hBalance := h.momentum_balance t ht x
  rw [hStress] at hBalance
  change finiteTimeDerivative T u t x + convection (u t) x =
    -NSEMaxwell.Classical.gradient (p t) x +
      ν • NSEMaxwell.Classical.laplacian (u t) x at hBalance
  rw [hBalance]
  abel

end

end ClassicalMechanics
