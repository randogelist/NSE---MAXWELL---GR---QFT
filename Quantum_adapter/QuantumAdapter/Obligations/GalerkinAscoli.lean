import QuantumAdapter.Obligations.GalerkinCompactness
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Simultaneous uniform subsequences on countably many compact domains

This module proves the topological extraction used for Fourier coefficient
trajectories and their derivative families. It constructs a single increasing
subsequence for the entire countable family. Nonlinear bounds and derivative
identification remain separate analytic steps.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace QuantumAdapter.Obligations

noncomputable section

/-- A uniformly bounded equicontinuous sequence has compact closure in sup norm. -/
theorem bounded_equicontinuous_range_isCompact {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (f : ℕ → X →ᵇ ℂ) (R : ℝ)
    (hbound : ∀ n : ℕ, ∀ x : X, ‖f n x‖ ≤ R)
    (hequi : Equicontinuous (fun n : ℕ => fun x : X => f n x)) :
    IsCompact (closure (Set.range f)) := by
  classical
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) R)
    (isCompact_closedBall (0 : ℂ) R) (Set.range f)
  · intro g x hg
    obtain ⟨n, rfl⟩ := hg
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n x
  · let chooseIndex : Set.range f → ℕ := fun g => Classical.choose g.property
    have heq : (fun g : Set.range f => fun x : X => g.val x) =
        (fun g : Set.range f => fun x : X => f (chooseIndex g) x) := by
      funext g x
      exact congrFun (congrArg (fun h : X →ᵇ ℂ => (h : X → ℂ))
        (Classical.choose_spec g.property).symm) x
    rw [heq]
    exact hequi.comp chooseIndex

/-- The uniform limit is a bounded continuous function on the same actual domain. -/
theorem bounded_equicontinuous_subsequence {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (f : ℕ → X →ᵇ ℂ) (R : ℝ)
    (hbound : ∀ n : ℕ, ∀ x : X, ‖f n x‖ ≤ R)
    (hequi : Equicontinuous (fun n : ℕ => fun x : X => f n x)) :
    ∃ (g : X →ᵇ ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (f ∘ φ) atTop (𝓝 g) := by
  obtain ⟨g, hg, φ, hφ, hlim⟩ :=
    (bounded_equicontinuous_range_isCompact f R hbound hequi).tendsto_subseq
      (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨g, φ, hφ, hlim⟩

/-- One subsequence serves every coordinate, derivative order, and finite horizon. -/
theorem countable_bounded_equicontinuous_subsequence {ι : Type*} [Countable ι]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    (f : ℕ → ∀ i, X i →ᵇ ℂ) (R : ι → ℝ)
    (hbound : ∀ i n, ∀ x : X i, ‖f n i x‖ ≤ R i)
    (hequi : ∀ i, Equicontinuous (fun n : ℕ => fun x : X i => f n i x)) :
    ∃ (g : ∀ i, X i →ᵇ ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ i, Tendsto (fun n : ℕ => f (φ n) i) atTop (𝓝 (g i)) := by
  let S : Set (∀ i, X i →ᵇ ℂ) :=
    Set.pi Set.univ (fun i => closure (Set.range (fun n : ℕ => f n i)))
  have hcompact : IsCompact S :=
    isCompact_univ_pi (fun i =>
      bounded_equicontinuous_range_isCompact (fun n => f n i) (R i)
        (hbound i) (hequi i))
  have hf : ∀ n : ℕ, f n ∈ S := by
    intro n i hi
    exact subset_closure (Set.mem_range_self n)
  obtain ⟨g, hg, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hf
  refine ⟨g, φ, hφ, ?_⟩
  intro i
  exact (tendsto_pi_nhds.mp hlim) i

end
end QuantumAdapter.Obligations
