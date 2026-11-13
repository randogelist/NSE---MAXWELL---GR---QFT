import QuantumAdapter.Assembly.Flow

/-!
Deterministic construction of the native flow record from complete actual
orbits and the actual real divergence identity. Both unresolved analytic
endpoints are fully exposed; no complete-orbit existence is asserted here.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QuantumAdapter.Assembly

noncomputable section

variable {ν : ℝ}

def chosenCompleteOrbit
    (complete : ∀ (N : ℕ) (q₀ : Phase N), ∃ q : ℝ → Phase N,
      q 0 = q₀ ∧ ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (N : ℕ) (q₀ : Phase N) : ℝ → Phase N :=
  Classical.choose (complete N q₀)

theorem chosenCompleteOrbit_zero
    (complete : ∀ (N : ℕ) (q₀ : Phase N), ∃ q : ℝ → Phase N,
      q 0 = q₀ ∧ ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (N : ℕ) (q₀ : Phase N) : chosenCompleteOrbit complete N q₀ 0 = q₀ :=
  (Classical.choose_spec (complete N q₀)).1

theorem chosenCompleteOrbit_derivative
    (complete : ∀ (N : ℕ) (q₀ : Phase N), ∃ q : ℝ → Phase N,
      q 0 = q₀ ∧ ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (N : ℕ) (q₀ : Phase N) (t : ℝ) :
    HasDerivAt (chosenCompleteOrbit complete N q₀)
      (drift ν N (chosenCompleteOrbit complete N q₀ t)) t :=
  (Classical.choose_spec (complete N q₀)).2 t

theorem chosenCompleteOrbit_add
    (complete : ∀ (N : ℕ) (q₀ : Phase N), ∃ q : ℝ → Phase N,
      q 0 = q₀ ∧ ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (N : ℕ) (q₀ : Phase N) (t s : ℝ) :
    chosenCompleteOrbit complete N q₀ (t + s) =
      chosenCompleteOrbit complete N (chosenCompleteOrbit complete N q₀ s) t := by
  have hleft (r : ℝ) :
      HasDerivAt (fun u => chosenCompleteOrbit complete N q₀ (u + s))
        (drift ν N (chosenCompleteOrbit complete N q₀ (r + s))) r := by
    simpa only [one_smul, Function.comp_def, id_eq] using
      (chosenCompleteOrbit_derivative complete N q₀ (r + s)).scomp r
        ((hasDerivAt_id r).add_const s)
  have hright := chosenCompleteOrbit_derivative complete N
    (chosenCompleteOrbit complete N q₀ s)
  have hzero : (fun r => chosenCompleteOrbit complete N q₀ (r + s)) 0 =
      chosenCompleteOrbit complete N (chosenCompleteOrbit complete N q₀ s) 0 := by
    simp only [zero_add, chosenCompleteOrbit_zero]
  exact congrFun (drift_solutions_unique ν N hleft hright hzero) t

def phaseFlowOfCompleteOrbits
    (complete : ∀ (N : ℕ) (q₀ : Phase N), ∃ q : ℝ → Phase N,
      q 0 = q₀ ∧ ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (divergence : ∀ N q, driftDivergence ν N q = -phaseDecayRate ν N) :
    PhaseFlow ν where
  map N t q₀ := chosenCompleteOrbit complete N q₀ t
  map_zero := chosenCompleteOrbit_zero complete
  map_add N t s q₀ := chosenCompleteOrbit_add complete N q₀ t s
  orbit_derivative := chosenCompleteOrbit_derivative complete
  divergence_eq := divergence

theorem nonempty_phaseFlow_of_completeOrbits
    (complete : ∀ (N : ℕ) (q₀ : Phase N), ∃ q : ℝ → Phase N,
      q 0 = q₀ ∧ ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (divergence : ∀ N q, driftDivergence ν N q = -phaseDecayRate ν N) :
    Nonempty (PhaseFlow ν) :=
  ⟨phaseFlowOfCompleteOrbits complete divergence⟩

theorem phaseFlow_eq_constructed
    (complete : ∀ (N : ℕ) (q₀ : Phase N), ∃ q : ℝ → Phase N,
      q 0 = q₀ ∧ ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (divergence : ∀ N q, driftDivergence ν N q = -phaseDecayRate ν N)
    (F : PhaseFlow ν) : F = phaseFlowOfCompleteOrbits complete divergence :=
  phaseFlow_unique F _

end
end QuantumAdapter.Assembly
