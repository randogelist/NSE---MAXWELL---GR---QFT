import SingularClosure.SobolevSmoothRealization

/-! Exact coefficient-tower interfaces shared by extraction and reconstruction. -/
set_option autoImplicit false
set_option Elab.async true
open Set
open scoped BigOperators

namespace QuantumAdapter.Obligations
open SingularClosure

def FourierTimeTowerDerivative (d : ℕ → ℝ → FourierCoeff) : Prop :=
  ∀ n t, 0 ≤ t → ∀ k i,
    HasDerivWithinAt (fun s => d n s k i) (d (n + 1) t k i) (Ici (0 : ℝ)) t

def FourierTimeTowerBounds (d : ℕ → ℝ → FourierCoeff) : Prop :=
  ∀ n m : ℕ, ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ I : Finset FourierIndex,
      (∑ ki ∈ I, ‖sobolevWeightedCoeff m (d n t) ki‖ ^ 2) ≤ C

end QuantumAdapter.Obligations
