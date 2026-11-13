import GRAssembly.NativeCKBilinear
import GRAssembly.NativeCKComposition

/-! Native multilinear superposition on the symmetric `ℓ¹` series space. -/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology BigOperators

namespace NSEGR.NativeLiterature

noncomputable section

variable {E G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [CompleteSpace G] [CompleteSpace H]

private abbrev CKBoundedLinear (A B : Type*)
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] := A →L[ℝ] B

def ckCurryZeroCLM : CKBoundedLinear (CKCoeff G H 0) H :=
  LinearMap.mkContinuous
    { toFun := fun a : CKCoeff G H 0 => a.curry0
      map_add' := by intro a b; rfl
      map_smul' := by intro t a; rfl }
    1 (fun a : CKCoeff G H 0 => by
      change ‖a.curry0‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using le_of_eq a.curry0_norm)

def ckCurryLeftCLM (n : ℕ) :
    CKBoundedLinear (CKCoeff G H (n + 1)) (CKBoundedLinear G (CKCoeff G H n)) :=
  LinearMap.mkContinuous
    { toFun := fun a : CKCoeff G H (n + 1) => a.curryLeft
      map_add' := by intro a b; ext x v; rfl
      map_smul' := by intro t a; ext x v; rfl }
    1 (fun a : CKCoeff G H (n + 1) => by
      change ‖a.curryLeft‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using le_of_eq a.curryLeft_norm)

theorem ckCurryZeroCLM_norm_le : ‖ckCurryZeroCLM (G := G) (H := H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  change ‖a.curry0‖ ≤ 1 * ‖a‖
  simpa only [one_mul] using le_of_eq a.curry0_norm

theorem ckCurryLeftCLM_norm_le (n : ℕ) : ‖ckCurryLeftCLM (G := G) (H := H) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro a
  change ‖a.curryLeft‖ ≤ 1 * ‖a‖
  simpa only [one_mul] using le_of_eq a.curryLeft_norm

namespace CKSeries

def contractMultilinear : (n : ℕ) → CKSeries E (CKCoeff G H n) →
    (Fin n → CKSeries E G) → CKSeries E H
  | 0, r, _ => postcompose (ckCurryZeroCLM (G := G) (H := H)) r
  | n + 1, r, p =>
      contractMultilinear n
        (bilinear (ContinuousLinearMap.id ℝ (CKBoundedLinear G (CKCoeff G H n)))
          (postcompose (ckCurryLeftCLM (G := G) (H := H) n) r) (p 0)) (Fin.tail p)

theorem norm_contractMultilinear_le (n : ℕ) (r : CKSeries E (CKCoeff G H n))
    (p : Fin n → CKSeries E G) :
    ‖contractMultilinear n r p‖ ≤ ‖r‖ * ∏ i, ‖p i‖ := by
  induction n with
  | zero =>
      calc
        ‖contractMultilinear 0 r p‖ ≤ ‖ckCurryZeroCLM (G := G) (H := H)‖ * ‖r‖ :=
          norm_postcompose_le (ckCurryZeroCLM (G := G) (H := H)) r
        _ ≤ 1 * ‖r‖ := mul_le_mul_of_nonneg_right ckCurryZeroCLM_norm_le (norm_nonneg r)
        _ = _ := by simp
  | succ n ih =>
      let s := bilinear (ContinuousLinearMap.id ℝ (CKBoundedLinear G (CKCoeff G H n)))
        (postcompose (ckCurryLeftCLM (G := G) (H := H) n) r) (p 0)
      have hs : ‖s‖ ≤ ‖r‖ * ‖p 0‖ := by
        calc
          ‖s‖ ≤ ‖ContinuousLinearMap.id ℝ (CKBoundedLinear G (CKCoeff G H n))‖ *
              ‖postcompose (ckCurryLeftCLM (G := G) (H := H) n) r‖ * ‖p 0‖ :=
                norm_bilinear_le _ _ _
          _ ≤ 1 * (1 * ‖r‖) * ‖p 0‖ := by
            gcongr
            · exact ContinuousLinearMap.norm_id_le
            · exact (norm_postcompose_le _ _).trans
                (mul_le_mul_of_nonneg_right
                  (ckCurryLeftCLM_norm_le (G := G) (H := H) n) (norm_nonneg r))
          _ = _ := by ring
      calc
        ‖contractMultilinear (n + 1) r p‖ ≤ ‖s‖ * ∏ i, ‖Fin.tail p i‖ := ih s (Fin.tail p)
        _ ≤ (‖r‖ * ‖p 0‖) * ∏ i, ‖Fin.tail p i‖ := by gcongr
        _ = ‖r‖ * ∏ i, ‖p i‖ := by rw [Fin.prod_univ_succ, mul_assoc]; rfl

theorem eval_contractMultilinear (n : ℕ) (r : CKSeries E (CKCoeff G H n))
    (p : Fin n → CKSeries E G) {x : E} (hx : ‖x‖ < 1) :
    (contractMultilinear n r p).eval x = r.eval x (fun i => (p i).eval x) := by
  induction n with
  | zero =>
      rw [contractMultilinear, eval_postcompose (ckCurryZeroCLM (G := G) (H := H)) r hx]
      change r.eval x 0 = r.eval x (fun i => (p i).eval x)
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      rw [contractMultilinear, ih, eval_bilinear _ _ _ hx, eval_postcompose _ _ hx]
      change (r.eval x).curryLeft ((p 0).eval x)
        (fun i => (p i.succ).eval x) = r.eval x (fun i => (p i).eval x)
      rw [ContinuousMultilinearMap.curryLeft_apply]
      congr 1
      exact Fin.cons_self_tail (fun i => (p i).eval x)

def multilinearApply {n : ℕ} (c : CKCoeff G H (n + 1))
    (p : Fin (n + 1) → CKSeries E G) : CKSeries E H :=
  contractMultilinear n (postcompose c.curryLeft (p 0)) (Fin.tail p)

theorem norm_multilinearApply_le {n : ℕ} (c : CKCoeff G H (n + 1))
    (p : Fin (n + 1) → CKSeries E G) :
    ‖multilinearApply c p‖ ≤ ‖c‖ * ∏ i, ‖p i‖ := by
  calc
    ‖multilinearApply c p‖ ≤ ‖postcompose c.curryLeft (p 0)‖ *
        ∏ i, ‖Fin.tail p i‖ := norm_contractMultilinear_le _ _ _
    _ ≤ (‖c‖ * ‖p 0‖) * ∏ i, ‖Fin.tail p i‖ := by
      gcongr
      simpa only [ContinuousMultilinearMap.curryLeft_norm] using norm_postcompose_le c.curryLeft (p 0)
    _ = ‖c‖ * ∏ i, ‖p i‖ := by rw [Fin.prod_univ_succ, mul_assoc]; rfl

theorem eval_multilinearApply {n : ℕ} (c : CKCoeff G H (n + 1))
    (p : Fin (n + 1) → CKSeries E G) {x : E} (hx : ‖x‖ < 1) :
    (multilinearApply c p).eval x = c (fun i => (p i).eval x) := by
  rw [multilinearApply, eval_contractMultilinear _ _ _ hx, eval_postcompose _ _ hx,
    ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  exact Fin.cons_self_tail (fun i => (p i).eval x)

def multilinearLift {n : ℕ} (c : CKCoeff G H (n + 1)) :
    CKCoeff (CKSeries E G) (CKSeries E H) (n + 1) :=
  MultilinearMap.mkContinuous
    { toFun := multilinearApply c
      map_update_add' := by
        intro _ p i a b
        apply eq_of_eval_eventuallyEq
        filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
        have hx' : ‖x‖ < 1 := by simpa using hx
        have heval (q : Fin (n + 1) → CKSeries E G) (u : CKSeries E G) :
            (fun j => (Function.update q i u j).eval x) =
              Function.update (fun j => (q j).eval x) i (u.eval x) := by
          funext j
          by_cases hji : j = i <;> simp [hji]
        simp only [eval_multilinearApply _ _ hx', eval_add _ _ hx', heval]
        exact c.map_update_add _ i _ _
      map_update_smul' := by
        intro _ p i t a
        apply eq_of_eval_eventuallyEq
        filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
        have hx' : ‖x‖ < 1 := by simpa using hx
        have heval (q : Fin (n + 1) → CKSeries E G) (u : CKSeries E G) :
            (fun j => (Function.update q i u j).eval x) =
              Function.update (fun j => (q j).eval x) i (u.eval x) := by
          funext j
          by_cases hji : j = i <;> simp [hji]
        simp only [eval_multilinearApply _ _ hx', eval_smul _ _ hx', heval]
        exact c.map_update_smul _ i t _ }
    ‖c‖ (norm_multilinearApply_le c)

@[simp] theorem multilinearLift_apply {n : ℕ} (c : CKCoeff G H (n + 1))
    (p : Fin (n + 1) → CKSeries E G) :
    multilinearLift c p = multilinearApply c p := rfl

theorem norm_multilinearLift_le {n : ℕ} (c : CKCoeff G H (n + 1)) :
    ‖multilinearLift (E := E) c‖ ≤ ‖c‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg c) _

def superposition (c : FormalMultilinearSeries ℝ G H) (p : CKSeries E G) : CKSeries E H :=
  ckPositiveMultilinearSum (fun n => multilinearLift (c (n + 1))) p

theorem superposition_majorant_summable (c : FormalMultilinearSeries ℝ G H)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n)) :
    Summable (fun n => ‖multilinearLift (E := E) (c (n + 1))‖ * (n + 1) * s ^ n) := by
  apply hc.of_nonneg_of_le (fun n => by positivity)
  intro n
  gcongr
  exact norm_multilinearLift_le _

theorem superposition_majorant_le (c : FormalMultilinearSeries ℝ G H)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n)) :
    ckPositiveMajorant (fun n => multilinearLift (E := E) (c (n + 1))) s ≤
      ckPositiveMajorant (fun n => c (n + 1)) s := by
  apply hasSum_le _ (superposition_majorant_summable c hs hc).hasSum hc.hasSum
  intro n
  gcongr
  exact norm_multilinearLift_le _

theorem norm_superposition_le (c : FormalMultilinearSeries ℝ G H)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    {p : CKSeries E G} (hp : ‖p‖ ≤ s) :
    ‖superposition c p‖ ≤ ckPositiveMajorant (fun n => c (n + 1)) s * ‖p‖ :=
  (ckPositiveMultilinearSum_norm_le _ hs (superposition_majorant_summable c hs hc) hp).trans
    (mul_le_mul_of_nonneg_right (superposition_majorant_le c hs hc) (norm_nonneg p))

theorem superposition_difference_le (c : FormalMultilinearSeries ℝ G H)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    {p q : CKSeries E G} (hp : ‖p‖ ≤ s) (hq : ‖q‖ ≤ s) :
    ‖superposition c p - superposition c q‖ ≤
      ckPositiveMajorant (fun n => c (n + 1)) s * ‖p - q‖ :=
  (ckPositiveMultilinearSum_difference_le _ hs (superposition_majorant_summable c hs hc) hp hq).trans
    (mul_le_mul_of_nonneg_right (superposition_majorant_le c hs hc) (norm_nonneg (p - q)))

theorem eval_superposition (c : FormalMultilinearSeries ℝ G H) (hc₀ : c 0 = 0)
    {s : ℝ} (hs : 0 ≤ s)
    (hc : Summable (fun n => ‖c (n + 1)‖ * (n + 1) * s ^ n))
    {p : CKSeries E G} (hp : ‖p‖ ≤ s) {x : E} (hx : ‖x‖ < 1) :
    (superposition c p).eval x = c.sum (p.eval x) := by
  have hlift := ckPositiveMultilinearSum_summable
    (fun n => multilinearLift (E := E) (c (n + 1))) hs
    (superposition_majorant_summable c hs hc) hp
  have heval := ckPositiveMultilinearSum_summable (fun n => c (n + 1)) hs hc
    ((p.norm_eval_le hx).trans hp)
  calc
    (superposition c p).eval x = ∑' n, c (n + 1) (fun _ => p.eval x) := by
      rw [superposition, ckPositiveMultilinearSum, eval_tsum _ hlift hx]
      apply tsum_congr
      intro n
      exact eval_multilinearApply _ _ hx
    _ = c.sum (p.eval x) := by
      symm
      change (∑' n, c n (fun _ => p.eval x)) = _
      rw [tsum_eq_zero_add' (f := fun n => c n (fun _ => p.eval x)) heval,
        hc₀, ContinuousMultilinearMap.zero_apply, zero_add]

end CKSeries

end

end NSEGR.NativeLiterature
