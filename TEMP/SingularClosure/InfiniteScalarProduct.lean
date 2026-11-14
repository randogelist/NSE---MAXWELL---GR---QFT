import SingularClosure.HighOrderProduct

/-!
# Infinite scalar Fourier convolution estimate

The finite tame product estimate is passed to the actual convergent convolution
along all finite subsets of the frequency lattice. No finite-support assumption
is imposed on either coefficient family.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology

namespace SingularClosure

noncomputable section

theorem scalarConvolution_weighted_square_partialSum_tendsto
    (m : ℕ) (a b : Frequency → ℂ)
    (hab : ∀ k : Frequency, Summable (fun p : Frequency => a p * b (k - p)))
    (r : Finset Frequency) :
    Tendsto (fun s : Finset Frequency =>
      ∑ k ∈ r, (torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a b k‖) ^ 2)
      atTop (𝓝 (∑ k ∈ r,
        (torusSobolevWeight k ^ m * ‖∑' p : Frequency, a p * b (k - p)‖) ^ 2)) := by
  apply tendsto_finsetSum r
  intro k _
  have hsum : Tendsto
      (fun s : Finset Frequency => finiteScalarConvolution s a b k)
      atTop (𝓝 (∑' p : Frequency, a p * b (k - p))) :=
    (hab k).hasSum
  exact (tendsto_const_nhds.mul hsum.norm).pow 2

/-- Actual infinite scalar Fourier convolution obeys a cutoff-independent
weighted square estimate. Both Sobolev moment bounds and convolution summability
are explicit hypotheses. -/
theorem INFINITE_SCALAR_FOURIER_PRODUCT_BOUND (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b : Frequency → ℂ) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∀ s : Finset Frequency,
          (∑ k ∈ s, (torusSobolevWeight k ^ 2 * ‖a k‖) ^ 2) ≤ A) →
        (∀ s : Finset Frequency,
          (∑ k ∈ s, (torusSobolevWeight k ^ m * ‖a k‖) ^ 2) ≤ A) →
        (∀ s : Finset Frequency,
          (∑ k ∈ s, (torusSobolevWeight k ^ 2 * ‖b k‖) ^ 2) ≤ B) →
        (∀ s : Finset Frequency,
          (∑ k ∈ s, (torusSobolevWeight k ^ m * ‖b k‖) ^ 2) ≤ B) →
        (∀ k : Frequency, Summable (fun p : Frequency => a p * b (k - p))) →
        ∀ r : Finset Frequency,
          (∑ k ∈ r,
            (torusSobolevWeight k ^ m * ‖∑' p : Frequency, a p * b (k - p)‖) ^ 2) ≤
              C * A * B := by
  classical
  obtain ⟨C, hC, htame⟩ := FINITE_FOURIER_TAME_PRODUCT_BOUND m
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro a b A B hA hB ha2 ham hb2 hbm hab r
  have hfinite (s : Finset Frequency) :
      (∑ k ∈ r, (torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a b k‖) ^ 2) ≤
        (2 * C) * A * B := by
    let t : Finset Frequency := r.biUnion (fun k => s.image (fun p => k - p))
    let bt : Frequency → ℂ := fun q => if q ∈ t then b q else 0
    have hsupport : ∀ q : Frequency, q ∉ t → bt q = 0 := by
      intro q hq
      simp only [bt, if_neg hq]
    have hcoeff (q : Frequency) (hq : q ∈ t) : bt q = b q := by
      simp only [bt, if_pos hq]
    have htrunc (n : ℕ) :
        (∑ q ∈ t, (torusSobolevWeight q ^ n * ‖bt q‖) ^ 2) =
          ∑ q ∈ t, (torusSobolevWeight q ^ n * ‖b q‖) ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hcoeff q hq]
    have hconv (k : Frequency) (hk : k ∈ r) :
        finiteScalarConvolution s a bt k = finiteScalarConvolution s a b k := by
      unfold finiteScalarConvolution
      apply Finset.sum_congr rfl
      intro p hp
      have hmem : k - p ∈ t :=
        Finset.mem_biUnion.mpr
          ⟨k, hk, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
      rw [hcoeff (k - p) hmem]
    have houtput :
        (∑ k ∈ r, (torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a bt k‖) ^ 2) =
          ∑ k ∈ r, (torusSobolevWeight k ^ m * ‖finiteScalarConvolution s a b k‖) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hconv k hk]
    have ht := htame r s t a bt hsupport
    rw [houtput, htrunc 2, htrunc m] at ht
    have hfirst :
        (∑ q ∈ t, (torusSobolevWeight q ^ 2 * ‖b q‖) ^ 2) *
          (∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) ^ 2) ≤ B * A :=
      mul_le_mul (hb2 t) (ham s) (Finset.sum_nonneg (fun p _ => sq_nonneg _)) hB
    have hsecond :
        (∑ p ∈ s, (torusSobolevWeight p ^ 2 * ‖a p‖) ^ 2) *
          (∑ q ∈ t, (torusSobolevWeight q ^ m * ‖b q‖) ^ 2) ≤ A * B :=
      mul_le_mul (ha2 s) (hbm t) (Finset.sum_nonneg (fun q _ => sq_nonneg _)) hA
    calc
      _ ≤ C *
          ((∑ q ∈ t, (torusSobolevWeight q ^ 2 * ‖b q‖) ^ 2) *
              (∑ p ∈ s, (torusSobolevWeight p ^ m * ‖a p‖) ^ 2) +
            (∑ p ∈ s, (torusSobolevWeight p ^ 2 * ‖a p‖) ^ 2) *
              (∑ q ∈ t, (torusSobolevWeight q ^ m * ‖b q‖) ^ 2)) := ht
      _ ≤ C * (B * A + A * B) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC.le
      _ = (2 * C) * A * B := by ring
  exact le_of_tendsto (scalarConvolution_weighted_square_partialSum_tendsto m a b hab r)
    (Filter.Eventually.of_forall hfinite)

end

end SingularClosure
