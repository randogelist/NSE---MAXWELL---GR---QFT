import ClassicalMechanicsForward
import ClassicalMechanicsReverse

/-!
# Deterministic concrete equivalence assembly

Both directions use the identical concrete fields and the native stress theorem.
These conclusions concern local Newtonian Cauchy balance. They do not claim the
later material-flow or Lagrange-d'Alembert equivalences.
-/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical

noncomputable section

theorem nseSolution_iff_newtonianSolution
    {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure} :
    NSSolution ν a u p ↔ NewtonianSolution ν a u p :=
  ⟨nseSolution_to_newtonianSolution, newtonianSolution_to_nseSolution⟩

theorem feffermanB_iff_newtonianB (ν : ℝ) :
    FeffermanB ν ↔ NewtonianB ν :=
  ⟨feffermanB_implies_newtonianB ν, newtonianB_implies_feffermanB ν⟩

theorem global_exact_equivalence : GlobalExactEquivalence := by
  intro ν _hν
  exact feffermanB_iff_newtonianB ν

theorem nseSolutionOn_iff_newtonianSolutionOn
    {ν T : ℝ} {a : Field} {u : Velocity} {p : Pressure} :
    NSSolutionOn ν a T u p ↔ NewtonianSolutionOn ν a T u p :=
  ⟨nseSolutionOn_to_newtonianSolutionOn, newtonianSolutionOn_to_nseSolutionOn⟩

theorem finite_solution_sets_eq (ν : ℝ) (a : Field) (T : ℝ) :
    {s : Velocity × Pressure | NSSolutionOn ν a T s.1 s.2} =
      {s : Velocity × Pressure | NewtonianSolutionOn ν a T s.1 s.2} := by
  apply Set.ext
  intro s
  exact nseSolutionOn_iff_newtonianSolutionOn

theorem finite_existence_iff (ν : ℝ) (a : Field) (T : ℝ) :
    (∃ (u : Velocity) (p : Pressure), NSSolutionOn ν a T u p) ↔
      (∃ (u : Velocity) (p : Pressure), NewtonianSolutionOn ν a T u p) := by
  constructor
  · rintro ⟨u, p, h⟩
    exact ⟨u, p, nseSolutionOn_to_newtonianSolutionOn h⟩
  · rintro ⟨u, p, h⟩
    exact ⟨u, p, newtonianSolutionOn_to_nseSolutionOn h⟩

theorem finite_exact_equivalence : FiniteExactEquivalence := by
  intro ν _hν T _hT a _ha u p
  exact nseSolutionOn_iff_newtonianSolutionOn

end

end ClassicalMechanics
