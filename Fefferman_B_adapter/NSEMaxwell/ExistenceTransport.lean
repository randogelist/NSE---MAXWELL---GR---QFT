import Mathlib.Logic.Equiv.Basic

/-!
# Explicit transport of universally quantified existence

These are logical transfer lemmas. A concrete application must provide the
initial-data equivalence and the forward/backward solution constructions.
No PDE existence or analytic realization is asserted in this module.
-/

namespace NSEMaxwell.ExistenceTransport

variable {D₁ D₂ S₁ S₂ : Type*}

/-- Transfer a universally quantified proposition across a genuine data equivalence. -/
theorem forall_iff_of_data_equiv
    (e : D₁ ≃ D₂)
    (P : D₁ → Prop) (Q : D₂ → Prop)
    (pointwise : ∀ a, P a ↔ Q (e a)) :
    (∀ a, P a) ↔ ∀ b, Q b := by
  constructor
  · intro h b
    have hb := (pointwise (e.symm b)).mp (h (e.symm b))
    simpa only [Equiv.apply_symm_apply] using hb
  · intro h a
    exact (pointwise a).mpr (h (e a))

/-- Universal existence is transported by explicit solution constructions.

The hypotheses are the actual maps on solutions, including all predicates
P and Q; no correspondence is inferred from names or syntax.
-/
theorem forall_exists_iff_of_data_equiv
    (e : D₁ ≃ D₂)
    (P : D₁ → S₁ → Prop) (Q : D₂ → S₂ → Prop)
    (forward : ∀ a s, P a s → ∃ t, Q (e a) t)
    (backward : ∀ a t, Q (e a) t → ∃ s, P a s) :
    (∀ a, ∃ s, P a s) ↔ ∀ b, ∃ t, Q b t := by
  apply forall_iff_of_data_equiv e
  intro a
  constructor
  · intro h
    rcases h with ⟨s, hs⟩
    exact forward a s hs
  · intro h
    rcases h with ⟨t, ht⟩
    exact backward a t ht

/-- A family of solution equivalences gives the same universal-existence result. -/
theorem forall_nonempty_iff_of_solution_equiv
    (e : D₁ ≃ D₂)
    (Solution₁ : D₁ → Type*) (Solution₂ : D₂ → Type*)
    (solutionEquiv : ∀ a, Solution₁ a ≃ Solution₂ (e a)) :
    (∀ a, Nonempty (Solution₁ a)) ↔
      ∀ b, Nonempty (Solution₂ b) := by
  apply forall_iff_of_data_equiv e
  intro a
  constructor
  · intro h
    rcases h with ⟨s⟩
    exact ⟨solutionEquiv a s⟩
  · intro h
    rcases h with ⟨t⟩
    exact ⟨(solutionEquiv a).symm t⟩

end NSEMaxwell.ExistenceTransport

