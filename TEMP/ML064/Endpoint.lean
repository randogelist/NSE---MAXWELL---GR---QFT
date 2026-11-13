/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
ML064 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean#L97
Source SHA256: 3d324fcdf3d667b6aca6cf59d81f63d8a6f42b15c2e7e5819b6a09cbd4325308
Source declaration: Matrix.IsHermitian.instContinuousFunctionalCalculus
Source lines: 97–125
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
The exported structure is a named definition, not a registered global instance.
-/

set_option autoImplicit false
noncomputable section

open Topology Unitary
namespace Matrix
namespace IsHermitian
variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

def _root_.GRTemp.ML064.endpoint :
    ContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint where
  exists_cfc_of_predicate a ha := by
    replace ha : IsHermitian a := ha
    refine ⟨ha.cfcAux, ha.isClosedEmbedding_cfcAux.continuous,
      ha.isClosedEmbedding_cfcAux.injective, ha.cfcAux_id, fun f ↦ ?map_spec,
      fun f ↦ ?hermitian⟩
    case map_spec =>
      apply Set.eq_of_subset_of_subset
      · rw [← ContinuousMap.spectrum_eq_range f]
        apply AlgHom.spectrum_apply_subset
      · rw [cfcAux_apply, conjStarAlgAut_apply, Unitary.spectrum_star_right_conjugate]
        rintro - ⟨x, rfl⟩
        apply spectrum.of_algebraMap_mem 𝕜
        simp only [Function.comp_apply, Set.mem_range, spectrum_diagonal]
        obtain ⟨x, hx⟩ := x
        obtain ⟨i, rfl⟩ := ha.spectrum_real_eq_range_eigenvalues ▸ hx
        exact ⟨i, rfl⟩
    case hermitian =>
      simp only [isSelfAdjoint_iff, cfcAux_apply, ← map_star]
      rw [star_eq_conjTranspose, diagonal_conjTranspose]
      congr!
      simp [Pi.star_def, Function.comp_def]
  spectrum_nonempty a ha := by
    obtain (h | h) := isEmpty_or_nonempty n
    · obtain ⟨x, y, hxy⟩ := exists_pair_ne (Matrix n n 𝕜)
      exact False.elim <| Matrix.of.symm.injective.ne hxy <| Subsingleton.elim _ _
    · exact spectrum_real_eq_range_eigenvalues ha ▸ Set.range_nonempty _
  predicate_zero := .zero _

end IsHermitian
end Matrix
