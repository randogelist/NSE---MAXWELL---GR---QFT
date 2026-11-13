import GRAssembly.NativeCKLift

/-! Native bounded bilinear lifting to symmetric absolutely summable coefficients. -/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology BigOperators

namespace NSEGR.NativeLiterature

noncomputable section

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def ckBilinearCoeff {n m : ℕ} (B : F →L[ℝ] G →L[ℝ] H)
    (a : CKCoeff E F n) (b : CKCoeff E G m) : CKCoeff E H (n + m) :=
  ((((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin m => E) G H).flip b).compContinuousMultilinearMap
        (B.compContinuousMultilinearMap a)).uncurrySum).domDomCongr finSumFinEquiv

@[simp] theorem ckBilinearCoeff_diagonal {n m : ℕ} (B : F →L[ℝ] G →L[ℝ] H)
    (a : CKCoeff E F n) (b : CKCoeff E G m) (x : E) :
    ckBilinearCoeff B a b (fun _ => x) = B (a (fun _ => x)) (b (fun _ => x)) := by
  rfl

theorem ckBilinearCoeff_norm_le {n m : ℕ} (B : F →L[ℝ] G →L[ℝ] H)
    (a : CKCoeff E F n) (b : CKCoeff E G m) :
    ‖ckBilinearCoeff B a b‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ := by
  let K := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin m => E) G H).flip b
  have hK : ‖K‖ ≤ ‖b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b)
    intro L
    change ‖L.compContinuousMultilinearMap b‖ ≤ ‖b‖ * ‖L‖
    simpa only [mul_comm] using L.norm_compContinuousMultilinearMap_le b
  calc
    ‖ckBilinearCoeff B a b‖ =
        ‖K.compContinuousMultilinearMap (B.compContinuousMultilinearMap a)‖ := by
      rw [ckBilinearCoeff, ContinuousMultilinearMap.norm_domDomCongr]
      exact (ContinuousMultilinearMap.currySumEquiv ℝ (Fin n) (Fin m) E H).symm.norm_map _
    _ ≤ ‖K‖ * ‖B.compContinuousMultilinearMap a‖ :=
      K.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖b‖ * (‖B‖ * ‖a‖) :=
      mul_le_mul hK (B.norm_compContinuousMultilinearMap_le a)
        (B.compContinuousMultilinearMap a).opNorm_nonneg b.opNorm_nonneg
    _ = ‖B‖ * ‖a‖ * ‖b‖ := by ring

namespace CKSeries

def bilinearTerm (B : F →L[ℝ] G →L[ℝ] H)
    (p : CKSeries E F) (q : CKSeries E G) (nm : ℕ × ℕ) : CKSeries E H :=
  single (nm.1 + nm.2)
    (ckSymmetrize E H (ckBilinearCoeff B (p.coeff nm.1) (q.coeff nm.2)))
    (by
      intro h
      rcases nm with ⟨n, m⟩
      have hn : n = 0 := by omega
      have hm : m = 0 := by omega
      subst n
      subst m
      apply ContinuousMultilinearMap.ext
      intro v
      simp [ckSymmetrize, ckBilinearCoeff])
    (ckSymmetrize_symmetric E H _)

theorem norm_bilinearTerm_le (B : F →L[ℝ] G →L[ℝ] H)
    (p : CKSeries E F) (q : CKSeries E G) (nm : ℕ × ℕ) :
    ‖bilinearTerm B p q nm‖ ≤ ‖B‖ * (‖p.coeff nm.1‖ * ‖q.coeff nm.2‖) := by
  calc
    ‖bilinearTerm B p q nm‖ =
        ‖ckSymmetrize E H (ckBilinearCoeff B (p.coeff nm.1) (q.coeff nm.2))‖ := by
      apply norm_single
    _ ≤ ‖ckBilinearCoeff B (p.coeff nm.1) (q.coeff nm.2)‖ :=
      ckSymmetrize_norm_le E H _
    _ ≤ ‖B‖ * ‖p.coeff nm.1‖ * ‖q.coeff nm.2‖ := ckBilinearCoeff_norm_le _ _ _
    _ = _ := mul_assoc _ _ _

variable [CompleteSpace H]

theorem bilinearTerm_summable (B : F →L[ℝ] G →L[ℝ] H)
    (p : CKSeries E F) (q : CKSeries E G) : Summable (bilinearTerm B p q) := by
  have hm := summable_mul_of_summable_norm p.summable_norm.norm q.summable_norm.norm
  exact (hm.mul_left ‖B‖).of_norm_bounded (norm_bilinearTerm_le B p q)

def bilinear (B : F →L[ℝ] G →L[ℝ] H) (p : CKSeries E F) (q : CKSeries E G) :
    CKSeries E H := ∑' nm : ℕ × ℕ, bilinearTerm B p q nm

theorem norm_bilinear_le (B : F →L[ℝ] G →L[ℝ] H)
    (p : CKSeries E F) (q : CKSeries E G) :
    ‖bilinear B p q‖ ≤ ‖B‖ * ‖p‖ * ‖q‖ := by
  have hm := summable_mul_of_summable_norm p.summable_norm.norm q.summable_norm.norm
  have hs := (p.hasSum_norm.mul q.hasSum_norm hm).mul_left ‖B‖
  simpa only [bilinear, mul_assoc] using tsum_of_norm_bounded hs (norm_bilinearTerm_le B p q)

theorem eval_bilinearTerm (B : F →L[ℝ] G →L[ℝ] H)
    (p : CKSeries E F) (q : CKSeries E G) (nm : ℕ × ℕ) {x : E} (hx : ‖x‖ < 1) :
    (bilinearTerm B p q nm).eval x =
      B (p.coeff nm.1 (fun _ => x)) (q.coeff nm.2 (fun _ => x)) := by
  rw [bilinearTerm, eval_single _ _ _ _ hx, ckSymmetrize_diagonal,
    ckBilinearCoeff_diagonal]

variable [CompleteSpace F] [CompleteSpace G]

theorem eval_bilinear (B : F →L[ℝ] G →L[ℝ] H)
    (p : CKSeries E F) (q : CKSeries E G) {x : E} (hx : ‖x‖ < 1) :
    (bilinear B p q).eval x = B (p.eval x) (q.eval x) := by
  have hs : Summable (fun nm : ℕ × ℕ =>
      B (p.coeff nm.1 (fun _ => x)) (q.coeff nm.2 (fun _ => x))) := by
    simpa only [evalCLM_apply, eval_bilinearTerm B p q _ hx] using
      (evalCLM x hx).summable (bilinearTerm_summable B p q)
  calc
    (bilinear B p q).eval x = ∑' nm : ℕ × ℕ,
        B (p.coeff nm.1 (fun _ => x)) (q.coeff nm.2 (fun _ => x)) := by
      rw [bilinear, eval_tsum _ (bilinearTerm_summable B p q) hx]
      exact tsum_congr fun nm => eval_bilinearTerm B p q nm hx
    _ = ∑' n, ∑' m, B (p.coeff n (fun _ => x)) (q.coeff m (fun _ => x)) :=
      hs.tsum_prod
    _ = ∑' n, B (p.coeff n (fun _ => x)) (q.eval x) := by
      apply tsum_congr
      intro n
      exact ((B (p.coeff n (fun _ => x))).hasSum (q.hasSum_eval hx)).tsum_eq
    _ = B (p.eval x) (q.eval x) :=
      ((B.flip (q.eval x)).hasSum (p.hasSum_eval hx)).tsum_eq

theorem bilinear_add_left (B : F →L[ℝ] G →L[ℝ] H)
    (p₁ p₂ : CKSeries E F) (q : CKSeries E G) :
    bilinear B (p₁ + p₂) q = bilinear B p₁ q + bilinear B p₂ q := by
  apply eq_of_eval_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : ‖x‖ < 1 := by simpa using hx
  simp only [eval_bilinear B _ _ hx', eval_add _ _ hx', map_add,
    ContinuousLinearMap.add_apply]

theorem bilinear_smul_left (B : F →L[ℝ] G →L[ℝ] H)
    (c : ℝ) (p : CKSeries E F) (q : CKSeries E G) :
    bilinear B (c • p) q = c • bilinear B p q := by
  apply eq_of_eval_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : ‖x‖ < 1 := by simpa using hx
  simp only [eval_bilinear B _ _ hx', eval_smul _ _ hx', map_smul,
    ContinuousLinearMap.smul_apply]

theorem bilinear_add_right (B : F →L[ℝ] G →L[ℝ] H)
    (p : CKSeries E F) (q₁ q₂ : CKSeries E G) :
    bilinear B p (q₁ + q₂) = bilinear B p q₁ + bilinear B p q₂ := by
  apply eq_of_eval_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : ‖x‖ < 1 := by simpa using hx
  simp only [eval_bilinear B _ _ hx', eval_add _ _ hx', map_add]

theorem bilinear_smul_right (B : F →L[ℝ] G →L[ℝ] H)
    (c : ℝ) (p : CKSeries E F) (q : CKSeries E G) :
    bilinear B p (c • q) = c • bilinear B p q := by
  apply eq_of_eval_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : ‖x‖ < 1 := by simpa using hx
  simp only [eval_bilinear B _ _ hx', eval_smul _ _ hx', map_smul]

end CKSeries

end

end NSEGR.NativeLiterature
