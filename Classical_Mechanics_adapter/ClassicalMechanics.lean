import ClassicalMechanics.MaxwellBridge

/-! The exact first classical-mechanics adapter: local Newtonian Cauchy balance. -/

set_option autoImplicit false

namespace ClassicalMechanics

theorem CLASSICAL_MECHANICS_ADAPTER :
    GlobalExactEquivalence ∧ FiniteExactEquivalence :=
  ⟨global_exact_equivalence, finite_exact_equivalence⟩

end ClassicalMechanics
