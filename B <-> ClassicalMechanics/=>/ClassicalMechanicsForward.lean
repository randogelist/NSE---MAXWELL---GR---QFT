import ClassicalMechanics.FiniteSlab

/-!
# NSE implies Newtonian Cauchy balance

The same actual velocity and pressure are retained. The only equation rewrite
uses the proved divergence of the literal Newtonian stress. No Fourier/Hodge,
flow-existence, variational, or solution-existence premise is introduced.
-/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical

noncomputable section

theorem nseSolution_to_newtonianSolution
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSSolution ν a u p) : NewtonianSolution ν a u p := by
  refine
    { velocity_smooth := h.velocity_smooth
      pressure_smooth := h.pressure_smooth
      velocity_periodic := h.velocity_periodic
      pressure_periodic := h.pressure_periodic
      divergence_free := h.divergence_free
      momentum_balance := ?_
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
  rw [hStress]
  change timeDerivative u t x + convection (u t) x = _
  calc
    timeDerivative u t x + convection (u t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x -
          NSEMaxwell.Classical.gradient (p t) x :=
      (eq_sub_iff_add_eq).2 (h.equation t ht x)
    _ = -NSEMaxwell.Classical.gradient (p t) x +
        ν • NSEMaxwell.Classical.laplacian (u t) x := by abel

theorem feffermanB_implies_newtonianB (ν : ℝ)
    (h : FeffermanB ν) : NewtonianB ν := by
  intro a ha
  obtain ⟨u, p, hNS⟩ := h a ha
  exact ⟨u, p, nseSolution_to_newtonianSolution hNS⟩

theorem nseSolutionOn_to_newtonianSolutionOn
    {ν T : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSSolutionOn ν a T u p) : NewtonianSolutionOn ν a T u p := by
  refine
    { velocity_smooth := h.velocity_smooth
      pressure_smooth := h.pressure_smooth
      velocity_periodic := h.velocity_periodic
      pressure_periodic := h.pressure_periodic
      divergence_free := h.divergence_free
      momentum_balance := ?_
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
  rw [hStress]
  change finiteTimeDerivative T u t x + convection (u t) x = _
  calc
    finiteTimeDerivative T u t x + convection (u t) x =
        ν • NSEMaxwell.Classical.laplacian (u t) x -
          NSEMaxwell.Classical.gradient (p t) x :=
      (eq_sub_iff_add_eq).2 (h.equation t ht x)
    _ = -NSEMaxwell.Classical.gradient (p t) x +
        ν • NSEMaxwell.Classical.laplacian (u t) x := by abel

end

end ClassicalMechanics
