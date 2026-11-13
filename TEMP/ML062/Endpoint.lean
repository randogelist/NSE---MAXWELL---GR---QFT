/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Anne Baanen
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
ML062 — isolated copied endpoint body.
Source: https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean#L675
Source SHA256: 8d744de386397a71349f271d027a974c7251f230220bfdb2e973af2ef8ef634b
Source declaration: Matrix.det_fromBlocks_zero₂₁
Source lines: 675–720
Status: A_TIER_CANDIDATE; no local Lean execution.
Dependencies: owning Mathlib module remains imported for definitions and helper lemmas.
No alias to the original target declaration occurs in the copied body.
-/

set_option autoImplicit false
noncomputable section

open Equiv Equiv.Perm Finset Function
namespace Matrix
variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
variable {R : Type*} [CommRing R]
local notation "ε " σ:arg => ((sign σ : ℤ) : R)
set_option backward.isDefEq.respectTransparency false in

theorem _root_.GRTemp.ML062.endpoint (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) :
    (Matrix.fromBlocks A B 0 D).det = A.det * D.det := by
  classical
    simp_rw [det_apply']
    convert!
      Eq.symm <|
        sum_subset (M := R) (subset_univ ((sumCongrHom m n).range : Set (Perm (m ⊕ n))).toFinset) ?_
    · simp_rw [sum_mul_sum, ← sum_product', univ_product_univ]
      refine sum_nbij (fun σ ↦ σ.fst.sumCongr σ.snd) ?_ ?_ ?_ ?_
      · intro σ₁₂ _
        simp
      · intro σ₁ _ σ₂ _
        dsimp only
        intro h
        have h2 : ∀ x, Perm.sumCongr σ₁.fst σ₁.snd x = Perm.sumCongr σ₂.fst σ₂.snd x :=
          DFunLike.congr_fun h
        simp only [Sum.map_inr, Sum.map_inl, Perm.sumCongr_apply, Sum.forall, Sum.inl.injEq,
          Sum.inr.injEq] at h2
        ext x
        · exact h2.left x
        · exact h2.right x
      · intro σ hσ
        rw [mem_coe, Set.mem_toFinset] at hσ
        obtain ⟨σ₁₂, hσ₁₂⟩ := hσ
        use σ₁₂
        rw [← hσ₁₂]
        simp
      · simp only [forall_prop_of_true, Prod.forall, mem_univ]
        intro σ₁ σ₂
        rw [Fintype.prod_sum_type]
        simp_rw [Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, fromBlocks_apply₁₁,
          fromBlocks_apply₂₂]
        rw [mul_mul_mul_comm]
        congr
        rw [sign_sumCongr, Units.val_mul, Int.cast_mul]
    · rintro σ - hσn
      have h1 : ¬∀ x, ∃ y, Sum.inl y = σ (Sum.inl x) := by
        rw [Set.mem_toFinset] at hσn
        simpa only [Set.MapsTo, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] using
          mt mem_sumCongrHom_range_of_perm_mapsTo_inl hσn
      obtain ⟨a, ha⟩ := not_forall.mp h1
      rcases hx : σ (Sum.inl a) with a2 | b
      · have hn := (not_exists.mp ha) a2
        exact absurd hx.symm hn
      · rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)), mul_zero]
        rw [hx, fromBlocks_apply₂₁, zero_apply]

end Matrix
