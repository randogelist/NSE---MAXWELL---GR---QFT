import GRAdapter.Sector

/-!
# A native nonzero-normalization constrained boundary

This is an actual analytic periodic constant boundary tensor satisfying
both flat-boundary vacuum constraints and both normalization traces.
It is not a constructed five-dimensional vacuum metric. Its realization
still requires the separately stated radial analytic extension theorem.
-/

set_option autoImplicit false

open scoped Matrix.Norms.Frobenius

namespace NSEGR

noncomputable section

def normalizedBoundaryMatrix (ρ : ℝ) : Tensor4 :=
  boundaryBlock (-(ρ / 3)) (fun _ => 0)
    (fun i j => -(ρ / 3) * identity3 i j)

def constantNormalizedBoundary (ρ : ℝ) : BoundaryTensor :=
  fun _ _ => normalizedBoundaryMatrix ρ

theorem normalizedBoundaryMatrix_symmetric (ρ : ℝ) :
    (normalizedBoundaryMatrix ρ).IsSymm := by
  change (normalizedBoundaryMatrix ρ).transpose = normalizedBoundaryMatrix ρ
  ext a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · rfl
    · rfl
  · refine Fin.cases ?_ (fun j => ?_) b
    · rfl
    · change -(ρ / 3) * identity3 j i = -(ρ / 3) * identity3 i j
      by_cases h : i = j
      · subst j
        rfl
      · simp [identity3, h, Ne.symm h]

@[simp] theorem constantNormalizedBoundary_beta (ρ : ℝ) (t : ℝ) (x : Vec) :
    boundaryBeta (constantNormalizedBoundary ρ) t x = ρ := by
  simp [boundaryBeta, constantNormalizedBoundary, normalizedBoundaryMatrix,
    spatialIndex4] <;> ring

@[simp] theorem constantNormalizedBoundary_beta_time (ρ t0 : ℝ) (x : Vec) :
    deriv (fun t : ℝ => boundaryBeta (constantNormalizedBoundary ρ) t x) t0 = 0 := by
  simp

theorem boundaryCodazzi_constant (M : Tensor4) :
    boundaryCodazzi (fun _ _ => M) = 0 := by
  funext t x b
  simp [boundaryCodazzi]

@[simp] theorem constantNormalizedBoundary_codazzi (ρ t : ℝ) (x : Vec) (b : Fin 4) :
    boundaryCodazzi (constantNormalizedBoundary ρ) t x b = 0 := by
  exact congrFun (congrFun (congrFun (boundaryCodazzi_constant (normalizedBoundaryMatrix ρ)) t) x) b

@[simp] theorem constantNormalizedBoundary_hamiltonian (ρ t : ℝ) (x : Vec) :
    boundaryHamiltonian (constantNormalizedBoundary ρ) t x = 0 := by
  have hA : trace3 (fun i j : Fin 3 => -(ρ / 3) * identity3 i j) = -ρ := by
    simp [trace3] <;> ring
  unfold boundaryHamiltonian constantNormalizedBoundary normalizedBoundaryMatrix
  rw [boundaryBlock_hamiltonian ρ (-(ρ / 3)) (fun _ => 0)
    (fun i j => -(ρ / 3) * identity3 i j) hA]
  simp [frobeniusSq3, vectorSq3, identity3, Fin.sum_univ_succ] <;> ring

/-- Exact flat-boundary constraints for every rho and every positive time radius. -/
theorem boundaryAdmissible_constantNormalized (ρ t0 δ : ℝ) (hδ : 0 < δ) :
    BoundaryAdmissible ρ t0 δ (constantNormalizedBoundary ρ) where
  radius_pos := hδ
  analytic := analyticOnNhd_const
  periodic := by
    intro t ht
    exact spatialPeriodic_const (normalizedBoundaryMatrix ρ)
  symmetric := by
    intro t ht x
    exact normalizedBoundaryMatrix_symmetric ρ
  momentum_constraint := by
    intro t ht x b
    exact constantNormalizedBoundary_codazzi ρ t x b
  hamiltonian := by
    intro t ht x
    exact constantNormalizedBoundary_hamiltonian ρ t x
  beta_initial := by
    intro x
    exact constantNormalizedBoundary_beta ρ t0 x
  beta_time_initial := by
    intro x
    exact constantNormalizedBoundary_beta_time ρ t0 x

theorem constantNormalizedBoundary_ne_zero (ρ : ℝ) (hρ : ρ ≠ 0) :
    constantNormalizedBoundary ρ ≠ 0 := by
  intro h
  have hb : boundaryBeta (constantNormalizedBoundary ρ) 0 (0 : Vec) = 0 := by
    rw [h]
    simp
  exact hρ (by simpa using hb)

theorem exists_boundaryAdmissible (ρ t0 δ : ℝ) (hδ : 0 < δ) :
    ∃ K : BoundaryTensor, BoundaryAdmissible ρ t0 δ K :=
  ⟨constantNormalizedBoundary ρ, boundaryAdmissible_constantNormalized ρ t0 δ hδ⟩

end

end NSEGR
