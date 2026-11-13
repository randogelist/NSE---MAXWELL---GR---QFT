import GRAdapter.ScalarNormalForm

/-!
# Analyticity of the concrete scalar normal form

The RHS is the actual rational scalarJetRHS. The only division condition is
rho + trace Q != 0 at the base jet. No CK existence or uniqueness theorem,
solution, or ScalarBoundaryCompletionLaws inhabitant is asserted here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace NSEGR
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed finite sum of actual scalar analytic maps. -/
theorem analyticAt_fin3_sum {f : Fin 3 → E → ℝ} {z : E}
    (hf : ∀ i, AnalyticAt ℝ (f i) z) :
    AnalyticAt ℝ (fun y => ∑ i : Fin 3, f i y) z := by
  have heq : (fun y : E => ∑ i : Fin 3, f i y) = ∑ i : Fin 3, f i := by
    funext y
    simp only [Finset.sum_apply]
  rw [heq]
  exact Finset.analyticAt_sum Finset.univ (fun i _ => hf i)

theorem analyticAt_trace3_components {A : E → Tensor3} {z : E}
    (hA : ∀ i j, AnalyticAt ℝ (fun y => A y i j) z) :
    AnalyticAt ℝ (fun y => trace3 (A y)) z := by
  simpa only [trace3, Pi.add_def] using ((hA 0 0).add (hA 1 1)).add (hA 2 2)

theorem analyticAt_vectorDot3_components {u b : E → Fin 3 → ℝ} {z : E}
    (hu : ∀ i, AnalyticAt ℝ (fun y => u y i) z)
    (hb : ∀ i, AnalyticAt ℝ (fun y => b y i) z) :
    AnalyticAt ℝ (fun y => vectorDot3 (u y) (b y)) z := by
  simpa only [vectorDot3, Pi.add_def, Pi.mul_def] using
    (((hu 0).mul (hb 0)).add ((hu 1).mul (hb 1))).add ((hu 2).mul (hb 2))

theorem analyticAt_vectorSq3_components {u : E → Fin 3 → ℝ} {z : E}
    (hu : ∀ i, AnalyticAt ℝ (fun y => u y i) z) :
    AnalyticAt ℝ (fun y => vectorSq3 (u y)) z := by
  simpa only [vectorSq3, Pi.add_def, Pi.pow_def] using
    (((hu 0).pow 2).add ((hu 1).pow 2)).add ((hu 2).pow 2)

theorem analyticAt_frobeniusInner3_components {A Q : E → Tensor3} {z : E}
    (hA : ∀ i j, AnalyticAt ℝ (fun y => A y i j) z)
    (hQ : ∀ i j, AnalyticAt ℝ (fun y => Q y i j) z) :
    AnalyticAt ℝ (fun y => frobeniusInner3 (A y) (Q y)) z := by
  unfold frobeniusInner3
  apply analyticAt_fin3_sum
  intro i
  apply analyticAt_fin3_sum
  intro j
  simpa only [Pi.mul_def] using (hA i j).mul (hQ i j)

theorem analyticAt_frobeniusSq3_components {A : E → Tensor3} {z : E}
    (hA : ∀ i j, AnalyticAt ℝ (fun y => A y i j) z) :
    AnalyticAt ℝ (fun y => frobeniusSq3 (A y)) z := by
  unfold frobeniusSq3
  apply analyticAt_fin3_sum
  intro i
  apply analyticAt_fin3_sum
  intro j
  simpa only [Pi.pow_def] using (hA i j).pow 2

/-- The native signed Hamiltonian of the source block is a polynomial in its entries. -/
theorem analyticAt_sourceHamiltonian4_boundaryBlock
    {ρ : E → ℝ} {u : E → Fin 3 → ℝ} {A : E → Tensor3} {z : E}
    (hρ : AnalyticAt ℝ ρ z)
    (hu : ∀ i, AnalyticAt ℝ (fun y => u y i) z)
    (hA : ∀ i j, AnalyticAt ℝ (fun y => A y i j) z) :
    AnalyticAt ℝ (fun y => sourceHamiltonian4 (boundaryBlock (ρ y) (u y) (A y))) z := by
  have hu2 := analyticAt_vectorSq3_components hu
  have hA2 := analyticAt_frobeniusSq3_components hA
  have htr := analyticAt_trace3_components hA
  have hc2 : AnalyticAt ℝ (fun _ : E => (2 : ℝ)) z := analyticAt_const
  have ht : AnalyticAt ℝ (fun y => -ρ y + trace3 (A y)) z := by
    simpa only [Pi.neg_def, Pi.add_def] using hρ.neg.add htr
  have ht2 : AnalyticAt ℝ (fun y => (-ρ y + trace3 (A y)) ^ 2 / 3) z := by
    simpa only [Pi.pow_def] using (ht.pow 2).div_const (c := (3 : ℝ))
  have heq :
      (fun y => sourceHamiltonian4 (boundaryBlock (ρ y) (u y) (A y))) =
      (fun y => (ρ y) ^ 2 - 2 * vectorSq3 (u y) + frobeniusSq3 (A y) -
        (-ρ y + trace3 (A y)) ^ 2 / 3) := by
    funext y
    exact sourceHamiltonian4_boundaryBlock (ρ y) (u y) (A y)
  rw [heq]
  simpa only [Pi.pow_def, Pi.sub_def, Pi.add_def, Pi.mul_def] using
    (((hρ.pow 2).sub (hc2.mul hu2)).add hA2).sub ht2

/-- Analyticity of the actual rational scalar RHS at every noncharacteristic jet.
The analytic input maps may live on any real normed vector space; finite jet
spaces are included. Component assumptions avoid an arbitrary matrix norm. -/
theorem analyticAt_scalarJetRHS_components
    {ρ : E → ℝ} {u b : E → Fin 3 → ℝ} {A Q : E → Tensor3} {z : E}
    (hρ : AnalyticAt ℝ ρ z)
    (hu : ∀ i, AnalyticAt ℝ (fun y => u y i) z)
    (hA : ∀ i j, AnalyticAt ℝ (fun y => A y i j) z)
    (hQ : ∀ i j, AnalyticAt ℝ (fun y => Q y i j) z)
    (hb : ∀ i, AnalyticAt ℝ (fun y => b y i) z)
    (hden : ρ z + trace3 (Q z) ≠ 0) :
    AnalyticAt ℝ (fun y => scalarJetRHS (ρ y) (u y) (A y) (Q y) (b y)) z := by
  have hS := analyticAt_sourceHamiltonian4_boundaryBlock hρ hu hA
  have hdot := analyticAt_vectorDot3_components hu hb
  have hinner := analyticAt_frobeniusInner3_components hA hQ
  have hb2 := analyticAt_vectorSq3_components hb
  have hQ2 := analyticAt_frobeniusSq3_components hQ
  have htr := analyticAt_trace3_components hQ
  have hc2 : AnalyticAt ℝ (fun _ : E => (2 : ℝ)) z := analyticAt_const
  have hc4 : AnalyticAt ℝ (fun _ : E => (4 : ℝ)) z := analyticAt_const
  have hnum : AnalyticAt ℝ (fun y =>
      -sourceHamiltonian4 (boundaryBlock (ρ y) (u y) (A y)) -
        4 * vectorDot3 (u y) (b y) - 2 * frobeniusInner3 (A y) (Q y) +
        2 * vectorSq3 (b y) - frobeniusSq3 (Q y) + (trace3 (Q y)) ^ 2) z := by
    simpa only [Pi.neg_def, Pi.sub_def, Pi.add_def, Pi.mul_def, Pi.pow_def] using
      (((((hS.neg.sub (hc4.mul hdot)).sub (hc2.mul hinner)).add
        (hc2.mul hb2)).sub hQ2).add (htr.pow 2))
  have hdenA : AnalyticAt ℝ (fun y => 2 * (ρ y + trace3 (Q y))) z := by
    simpa only [Pi.mul_def, Pi.add_def] using hc2.mul (hρ.add htr)
  have hden0 : 2 * (ρ z + trace3 (Q z)) ≠ 0 :=
    mul_ne_zero (by norm_num) hden
  simpa only [scalarJetRHS, Pi.div_def] using hnum.div hdenA hden0

/-- The same native RHS is analytic throughout any domain on which the
component maps are analytic and the scalar coefficient is nonzero. -/
theorem analyticOnNhd_scalarJetRHS_components
    {ρ : E → ℝ} {u b : E → Fin 3 → ℝ} {A Q : E → Tensor3} {D : Set E}
    (hρ : AnalyticOnNhd ℝ ρ D)
    (hu : ∀ i, AnalyticOnNhd ℝ (fun y => u y i) D)
    (hA : ∀ i j, AnalyticOnNhd ℝ (fun y => A y i j) D)
    (hQ : ∀ i j, AnalyticOnNhd ℝ (fun y => Q y i j) D)
    (hb : ∀ i, AnalyticOnNhd ℝ (fun y => b y i) D)
    (hden : ∀ z ∈ D, ρ z + trace3 (Q z) ≠ 0) :
    AnalyticOnNhd ℝ (fun y => scalarJetRHS (ρ y) (u y) (A y) (Q y) (b y)) D := by
  intro z hz
  exact analyticAt_scalarJetRHS_components (hρ z hz)
    (fun i => hu i z hz) (fun i j => hA i j z hz) (fun i j => hQ i j z hz)
    (fun i => hb i z hz) (hden z hz)

end
end NSEGR
