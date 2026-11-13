import GRAssembly.NativeCKMultilinear
import GRAssembly.NativeCKFixedPoint
import GRAssembly.NativeCKNormalization

/-! The concrete scaled jet and its coefficient-space contraction bounds. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology BigOperators NNReal ENNReal

namespace NSEGR.NativeLiterature

noncomputable section

namespace CKSeries

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def linear (L : E →L[ℝ] F) : CKSeries E F :=
  single 1 ((continuousMultilinearCurryFin1 ℝ E F).symm L)
    (by intro h; omega)
    (by
      intro v σ
      congr 1
      funext i
      congr 1
      exact Subsingleton.elim _ _)

@[simp] theorem norm_linear (L : E →L[ℝ] F) : ‖linear L‖ = ‖L‖ := by
  rw [linear, norm_single]
  exact (continuousMultilinearCurryFin1 ℝ E F).symm.norm_map L

theorem eval_linear [CompleteSpace F] (L : E →L[ℝ] F) {x : E} (hx : ‖x‖ < 1) :
    (linear L).eval x = L x := by
  rw [linear, eval_single _ _ _ _ hx]
  rfl

def pair (p : CKSeries E F) (q : CKSeries E G) : CKSeries E (F × G) :=
  postcompose (ContinuousLinearMap.inl ℝ F G) p + postcompose (ContinuousLinearMap.inr ℝ F G) q

theorem norm_pair_le (p : CKSeries E F) (q : CKSeries E G) : ‖pair p q‖ ≤ ‖p‖ + ‖q‖ := by
  calc
    ‖pair p q‖ ≤ ‖postcompose (ContinuousLinearMap.inl ℝ F G) p‖ +
        ‖postcompose (ContinuousLinearMap.inr ℝ F G) q‖ := norm_add_le _ _
    _ ≤ 1 * ‖p‖ + 1 * ‖q‖ := by
      gcongr
      · exact (norm_postcompose_le _ _).trans
          (mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_inl_le_one (norm_nonneg p))
      · exact (norm_postcompose_le _ _).trans
          (mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_inr_le_one (norm_nonneg q))
    _ = _ := by ring

theorem pair_sub (p₁ p₂ : CKSeries E F) (q₁ q₂ : CKSeries E G) :
    pair p₁ q₁ - pair p₂ q₂ = pair (p₁ - p₂) (q₁ - q₂) := by
  unfold pair
  change postcomposeCLM _ p₁ + postcomposeCLM _ q₁ -
      (postcomposeCLM _ p₂ + postcomposeCLM _ q₂) =
    postcomposeCLM _ (p₁ - p₂) + postcomposeCLM _ (q₁ - q₂)
  rw [map_sub, map_sub]
  abel

theorem eval_pair [CompleteSpace F] [CompleteSpace G]
    (p : CKSeries E F) (q : CKSeries E G) {x : E} (hx : ‖x‖ < 1) :
    (pair p q).eval x = (p.eval x, q.eval x) := by
  simp [pair, eval_add _ _ hx, eval_postcompose _ _ hx]

end CKSeries

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def ckCoefficientScale (ε : ℝ) : CKTimeSpace E →L[ℝ] ℝ × E :=
  ((ε ^ 2) • WithLp.fstL 1 ℝ ℝ E).prod (ε • WithLp.sndL 1 ℝ ℝ E)

theorem ckCoefficientScale_norm_le {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ‖ckCoefficientScale (E := E) ε‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro z
  change ‖(ε ^ 2 * z.fst, ε • z.snd)‖ ≤ ε * ‖z‖
  rw [Prod.norm_def]
  apply max_le
  · rw [norm_mul, Real.norm_of_nonneg (sq_nonneg ε)]
    have hε² : ε ^ 2 ≤ ε := by nlinarith
    exact (mul_le_mul_of_nonneg_right hε² (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le z) hε)
  · rw [norm_smul, Real.norm_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left (WithLp.norm_snd_le z) hε

def ckScaledJetUsing
    (A : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) V)
    (B : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) (E →L[ℝ] V))
    (ε : ℝ) (p : CKSeries (CKTimeSpace E) V) : CKSeries (CKTimeSpace E) (CKJet E V) :=
  CKSeries.pair (CKSeries.linear (ckCoefficientScale ε))
    (CKSeries.pair (ε ^ 2 • A p) (ε • B p))

theorem ckScaledJetUsing_norm_le
    (A : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) V)
    (B : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) (E →L[ℝ] V))
    (hA : ‖A‖ ≤ (1 / 2 : ℝ)) (hB : ‖B‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    {p : CKSeries (CKTimeSpace E) V} (hp : ‖p‖ ≤ 1) :
    ‖ckScaledJetUsing A B ε p‖ ≤ 4 * ε := by
  have hAp : ‖A p‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖A p‖ ≤ ‖A‖ * ‖p‖ := A.le_opNorm p
      _ ≤ (1 / 2 : ℝ) * 1 := mul_le_mul hA hp (norm_nonneg p) (by norm_num)
      _ = _ := by ring
  have hBp : ‖B p‖ ≤ 1 := by
    calc
      ‖B p‖ ≤ ‖B‖ * ‖p‖ := B.le_opNorm p
      _ ≤ 1 * 1 := mul_le_mul hB hp (norm_nonneg p) (by norm_num)
      _ = _ := by ring
  calc
    ‖ckScaledJetUsing A B ε p‖ ≤
        ‖CKSeries.linear (ckCoefficientScale ε)‖ + ‖ε ^ 2 • A p‖ + ‖ε • B p‖ := by
      exact (CKSeries.norm_pair_le _ _).trans
        (by linarith [CKSeries.norm_pair_le (ε ^ 2 • A p) (ε • B p)])
    _ ≤ ε + ε ^ 2 * (1 / 2) + ε * 1 := by
      rw [CKSeries.norm_linear, norm_smul, norm_smul,
        Real.norm_of_nonneg (sq_nonneg ε), Real.norm_of_nonneg hε]
      gcongr
      exact ckCoefficientScale_norm_le hε hε₁
    _ ≤ 4 * ε := by
      have hb := (ck_scaled_tuple_budget hε hε₁).1
      nlinarith [sq_nonneg ε]

theorem ckScaledJetUsing_difference_le
    (A : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) V)
    (B : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) (E →L[ℝ] V))
    (hA : ‖A‖ ≤ (1 / 2 : ℝ)) (hB : ‖B‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (p q : CKSeries (CKTimeSpace E) V) :
    ‖ckScaledJetUsing A B ε p - ckScaledJetUsing A B ε q‖ ≤ 2 * ε * ‖p - q‖ := by
  have hAp : ‖A (p - q)‖ ≤ (1 / 2 : ℝ) * ‖p - q‖ :=
    (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hBp : ‖B (p - q)‖ ≤ ‖p - q‖ := by
    simpa only [one_mul] using
      (B.le_opNorm (p - q)).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  rw [ckScaledJetUsing, ckScaledJetUsing, CKSeries.pair_sub, sub_self,
    CKSeries.pair_sub, ← smul_sub, ← smul_sub, ← map_sub, ← map_sub]
  calc
    ‖CKSeries.pair 0 (CKSeries.pair (ε ^ 2 • A (p - q)) (ε • B (p - q)))‖ ≤
        ‖ε ^ 2 • A (p - q)‖ + ‖ε • B (p - q)‖ := by
      exact (CKSeries.norm_pair_le _ _).trans
        (by simpa only [norm_zero, zero_add] using CKSeries.norm_pair_le
          (ε ^ 2 • A (p - q)) (ε • B (p - q)))
    _ ≤ ε ^ 2 * ((1 / 2) * ‖p - q‖) + ε * ‖p - q‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (sq_nonneg ε), Real.norm_of_nonneg hε]
      gcongr
    _ = (ε ^ 2 / 2 + ε) * ‖p - q‖ := by ring
    _ ≤ 2 * ε * ‖p - q‖ :=
      mul_le_mul_of_nonneg_right (ck_scaled_tuple_budget hε hε₁).2 (norm_nonneg _)

variable [CompleteSpace E] [CompleteSpace V]

def ckScaledCoefficientMapUsing (c : FormalMultilinearSeries ℝ (CKJet E V) V)
    (A : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) V)
    (B : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) (E →L[ℝ] V))
    (ε : ℝ) (p : CKSeries (CKTimeSpace E) V) : CKSeries (CKTimeSpace E) V :=
  CKSeries.superposition c (ckScaledJetUsing A B ε p)

theorem ckScaledCoefficientMapUsing_fixedPoint
    (c : FormalMultilinearSeries ℝ (CKJet E V) V)
    {s : ℝ} (hs : 0 < s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    (A : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) V)
    (B : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) (E →L[ℝ] V))
    (hA : ‖A‖ ≤ (1 / 2 : ℝ)) (hB : ‖B‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hεs : 4 * ε ≤ s)
    (hself : 4 * ckPositiveMajorant (fun n => c (n + 1)) s * ε ≤ 1)
    (hcontract : 2 * ckPositiveMajorant (fun n => c (n + 1)) s * ε ≤ (1 / 4 : ℝ)) :
    ∃ p : CKSeries (CKTimeSpace E) V, ‖p‖ ≤ 1 ∧
      ckScaledCoefficientMapUsing c A B ε p = p ∧
      ∀ q : CKSeries (CKTimeSpace E) V, ‖q‖ ≤ 1 →
        ckScaledCoefficientMapUsing c A B ε q = q → q = p := by
  exact ck_exists_unique_scaled_fixedPoint (CKSeries.superposition c) (ckScaledJetUsing A B ε)
    s (ckPositiveMajorant (fun n => c (n + 1)) s) ε
    (ckPositiveMajorant_nonneg _ hs.le) hε.le hεs hself hcontract
    (fun p hp => CKSeries.norm_superposition_le c hs.le hc hp)
    (fun p q hp hq => CKSeries.superposition_difference_le c hs.le hc hp hq)
    (fun p hp => ckScaledJetUsing_norm_le A B hA hB hε.le hε₁ hp)
    (fun p q _ _ => ckScaledJetUsing_difference_le A B hA hB hε.le hε₁ p q)

theorem ckScaledCoefficientMapUsing_exists_fixedPoint
    (c : FormalMultilinearSeries ℝ (CKJet E V) V)
    {s : ℝ} (hs : 0 < s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    (A : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) V)
    (B : CKSeries (CKTimeSpace E) V →L[ℝ] CKSeries (CKTimeSpace E) (E →L[ℝ] V))
    (hA : ‖A‖ ≤ (1 / 2 : ℝ)) (hB : ‖B‖ ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 4 * ε ≤ s ∧
      ∃ p : CKSeries (CKTimeSpace E) V, ‖p‖ ≤ 1 ∧
        ckScaledCoefficientMapUsing c A B ε p = p ∧
        ∀ q : CKSeries (CKTimeSpace E) V, ‖q‖ ≤ 1 →
          ckScaledCoefficientMapUsing c A B ε q = q → q = p := by
  obtain ⟨ε, hε, hε₁, hεs, hself, hcontract⟩ := ck_exists_scaling_budget s
    (ckPositiveMajorant (fun n => c (n + 1)) s) hs (ckPositiveMajorant_nonneg _ hs.le)
  exact ⟨ε, hε, hε₁, hεs,
    ckScaledCoefficientMapUsing_fixedPoint c hs hc A B hA hB hε hε₁ hεs hself hcontract⟩

theorem ckAnalytic_superposition_data {g : CKRHS E V}
    (hg : AnalyticAt ℝ g 0) (hg₀ : g 0 = 0) :
    ∃ c : FormalMultilinearSeries ℝ (CKJet E V) V, ∃ s : ℝ,
      0 < s ∧ c 0 = 0 ∧
      Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n) ∧
      ∀ y : CKJet E V, ‖y‖ ≤ s → c.sum y = g y := by
  obtain ⟨c, hc⟩ := hg
  have hc₀ : c 0 = 0 := by
    ext v
    simpa [hg₀] using hc.coeff_zero v
  obtain ⟨r, hr⟩ := hc
  obtain ⟨R, hR₀, hR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr.r_pos
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast hR₀
  have hsum : Summable (fun n => ‖c n‖ * (R : ℝ) ^ n) :=
    c.summable_norm_mul_pow (hR.trans_le hr.r_le)
  refine ⟨c, (R : ℝ) / 2, half_pos hRpos, hc₀,
    ck_summable_derivative_majorant_halfRadius (fun n => ‖c n‖)
      (fun n => norm_nonneg _) hRpos hsum, ?_⟩
  intro y hy
  have hyR : y ∈ Metric.eball (0 : CKJet E V) (R : ℝ≥0∞) := by
    rw [Metric.eball_coe]
    simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt hy (half_lt_self hRpos)
  have hsumy := (hr.mono hR₀ hR.le).hasSum hyR
  simpa only [FormalMultilinearSeries.sum, zero_add] using hsumy.tsum_eq

end

end NSEGR.NativeLiterature
