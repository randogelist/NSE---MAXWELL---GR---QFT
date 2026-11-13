import GRAssembly.NativeCKSeries
import GRAssembly.NativeCKLift
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Actual coefficient time primitives.  The finite-degree integral below is
the symmetric subset formula in an equivalent integral representation.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace NSEGR.NativeLiterature

noncomputable section

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def ckTimeProj : CKTimeSpace E →L[ℝ] ℝ := WithLp.fstL 1 ℝ ℝ E

def ckSpaceProj : CKTimeSpace E →L[ℝ] E := WithLp.sndL 1 ℝ ℝ E

def ckTimeInclude : ℝ →L[ℝ] CKTimeSpace E :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ ℝ E)

def ckSpaceInclude : E →L[ℝ] CKTimeSpace E :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ ℝ E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ ℝ E)

def ckTimeScale (s : ℝ) : CKTimeSpace E →L[ℝ] CKTimeSpace E :=
  s • ((ckTimeInclude E).comp (ckTimeProj E)) +
    (ckSpaceInclude E).comp (ckSpaceProj E)

@[simp] theorem ckTimeProj_apply (z : CKTimeSpace E) : ckTimeProj E z = z.fst := rfl

@[simp] theorem ckSpaceProj_apply (z : CKTimeSpace E) : ckSpaceProj E z = z.snd := rfl

@[simp] theorem ckTimeScale_apply (s : ℝ) (z : CKTimeSpace E) :
    ckTimeScale E s z = WithLp.toLp 1 (s * z.fst, z.snd) := by
  change WithLp.toLp 1 (s * z.fst + 0, s • (0 : E) + z.snd) = _
  simp

theorem ckTimeScale_continuous : Continuous (ckTimeScale E) := by
  unfold ckTimeScale
  fun_prop

theorem ckTimeScale_norm (s : ℝ) (hs : 0 ≤ s) (z : CKTimeSpace E) :
    ‖ckTimeScale E s z‖ = s * |z.fst| + ‖z.snd‖ := by
  rw [ckTimeScale_apply, WithLp.prod_norm_eq_of_L1]
  simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs]

theorem ck_prod_erase_eq_succAbove {n : ℕ} (j : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    (∏ i ∈ Finset.univ.erase j, f i) = ∏ i : Fin n, f (j.succAbove i) := by
  symm
  apply Finset.prod_bij (fun i _ => j.succAbove i)
  · intro i _
    simp [j.succAbove_ne i]
  · intro i _ k _ hik
    exact Fin.succAbove_right_injective hik
  · intro i hi
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hi).1
    exact ⟨k, Finset.mem_univ _, hk⟩
  · intro i _
    rfl

theorem ck_hasDerivAt_product {n : ℕ} (a b : Fin (n + 1) → ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∏ j : Fin (n + 1), (t * a j + b j))
      (∑ j : Fin (n + 1), a j * ∏ i : Fin n, (s * a (j.succAbove i) + b (j.succAbove i))) s := by
  have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin (n + 1))))
    (fun j _ => ((hasDerivAt_id s).mul_const (a j)).add_const (b j))
  simpa only [id_eq, one_mul, mul_one, smul_eq_mul, ck_prod_erase_eq_succAbove, mul_comm] using h

theorem ck_integral_product_derivative {n : ℕ} (a b : Fin (n + 1) → ℝ) :
    (∫ s in (0 : ℝ)..1,
      ∑ j : Fin (n + 1), a j * ∏ i : Fin n,
        (s * a (j.succAbove i) + b (j.succAbove i))) =
      (∏ j : Fin (n + 1), (a j + b j)) - ∏ j : Fin (n + 1), b j := by
  have hc : Continuous (fun s : ℝ => ∑ j : Fin (n + 1), a j *
      ∏ i : Fin n, (s * a (j.succAbove i) + b (j.succAbove i))) := by fun_prop
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => ck_hasDerivAt_product a b s) (hc.intervalIntegrable 0 1)

def ckInsertTimeCLM {n : ℕ} (j : Fin (n + 1)) :
    CKCoeff (CKTimeSpace E) F n →L[ℝ] CKCoeff (CKTimeSpace E) F (n + 1) :=
  (ContinuousMultilinearMap.curryMidEquiv ℝ
      (fun _ : Fin (n + 1) => CKTimeSpace E) F j).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.smulRightL ℝ (CKTimeSpace E) (CKCoeff (CKTimeSpace E) F n)
      (ckTimeProj E))

@[simp] theorem ckInsertTimeCLM_apply {n : ℕ} (j : Fin (n + 1))
    (a : CKCoeff (CKTimeSpace E) F n) (v : Fin (n + 1) → CKTimeSpace E) :
    ckInsertTimeCLM E F j a v = (v j).fst • a (fun i => v (j.succAbove i)) := by
  rfl

def ckPrimitiveKernelCLM (n : ℕ) (s : ℝ) :
    CKCoeff (CKTimeSpace E) F n →L[ℝ] CKCoeff (CKTimeSpace E) F (n + 1) :=
  ((n + 1 : ℝ)⁻¹) • ∑ j : Fin (n + 1),
    (ckInsertTimeCLM E F j).comp
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (F := F) (fun _ : Fin n => ckTimeScale E s))

theorem ckPrimitiveKernelCLM_apply {n : ℕ} (s : ℝ)
    (a : CKCoeff (CKTimeSpace E) F n) (v : Fin (n + 1) → CKTimeSpace E) :
    ckPrimitiveKernelCLM E F n s a v = (n + 1 : ℝ)⁻¹ •
      ∑ j : Fin (n + 1), (v j).fst •
        a (fun i => ckTimeScale E s (v (j.succAbove i))) := by
  simp [ckPrimitiveKernelCLM, ckInsertTimeCLM_apply,
    ContinuousMultilinearMap.compContinuousLinearMapL_apply]

theorem ckPrimitiveKernelCLM_continuous (n : ℕ) :
    Continuous (ckPrimitiveKernelCLM E F n) := by
  have hc : Continuous (fun s : ℝ =>
      ContinuousMultilinearMap.compContinuousLinearMapL
        (F := F) (fun _ : Fin n => ckTimeScale E s)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
      (fun _ : Fin n => CKTimeSpace E) (fun _ : Fin n => CKTimeSpace E) F).cont.comp
        (continuous_pi fun _ => ckTimeScale_continuous E)
  have hsum : Continuous (fun s : ℝ => ∑ j : Fin (n + 1),
      (ckInsertTimeCLM E F j).comp
        (ContinuousMultilinearMap.compContinuousLinearMapL
          (F := F) (fun _ : Fin n => ckTimeScale E s))) :=
    continuous_finsetSum _ fun j _ =>
      (continuous_const : Continuous (fun _ : ℝ => ckInsertTimeCLM E F j)).clm_comp hc
  exact hsum.const_smul ((n + 1 : ℝ)⁻¹)

theorem ckPrimitiveKernelCLM_eval_norm_le {n : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (a : CKCoeff (CKTimeSpace E) F n) (v : Fin (n + 1) → CKTimeSpace E) :
    ‖ckPrimitiveKernelCLM E F n s a v‖ ≤
      ((n + 1 : ℝ)⁻¹ * ‖a‖) *
        ∑ j : Fin (n + 1), |(v j).fst| *
          ∏ i : Fin n, (s * |(v (j.succAbove i)).fst| + ‖(v (j.succAbove i)).snd‖) := by
  have hn : 0 ≤ (n + 1 : ℝ)⁻¹ := by positivity
  rw [ckPrimitiveKernelCLM_apply, norm_smul, Real.norm_of_nonneg hn]
  calc
    (n + 1 : ℝ)⁻¹ * ‖∑ j : Fin (n + 1), (v j).fst •
        a (fun i => ckTimeScale E s (v (j.succAbove i)))‖
      ≤ (n + 1 : ℝ)⁻¹ * ∑ j : Fin (n + 1),
          ‖(v j).fst • a (fun i => ckTimeScale E s (v (j.succAbove i)))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hn
    _ ≤ (n + 1 : ℝ)⁻¹ * ∑ j : Fin (n + 1),
        |(v j).fst| * (‖a‖ * ∏ i : Fin n,
          (s * |(v (j.succAbove i)).fst| + ‖(v (j.succAbove i)).snd‖)) := by
      apply mul_le_mul_of_nonneg_left _ hn
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [ckTimeScale_norm E s hs] using
        a.le_opNorm (fun i => ckTimeScale E s (v (j.succAbove i)))
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

def ckPrimitiveCoeffCLM [CompleteSpace F] (n : ℕ) :
    CKCoeff (CKTimeSpace E) F n →L[ℝ] CKCoeff (CKTimeSpace E) F (n + 1) :=
  (ckSymmetrizeCLM (CKTimeSpace E) F (n + 1)).comp
    (∫ s in (0 : ℝ)..1, ckPrimitiveKernelCLM E F n s)

theorem ckPrimitiveIntegral_apply [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) (v : Fin (n + 1) → CKTimeSpace E) :
    ((∫ s in (0 : ℝ)..1, ckPrimitiveKernelCLM E F n s) a) v =
      ∫ s in (0 : ℝ)..1, ckPrimitiveKernelCLM E F n s a v := by
  have hc := ckPrimitiveKernelCLM_continuous E F n
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1) a]
  exact ((ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin (n + 1) => CKTimeSpace E) F v).intervalIntegral_comp_comm
      (((continuous_eval_const a).comp hc).intervalIntegrable 0 1)).symm

theorem ckPrimitiveIntegral_norm_le [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) :
    ‖(∫ s in (0 : ℝ)..1, ckPrimitiveKernelCLM E F n s) a‖ ≤
      (n + 1 : ℝ)⁻¹ * ‖a‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [ckPrimitiveIntegral_apply]
  let A : Fin (n + 1) → ℝ := fun j => |(v j).fst|
  let B : Fin (n + 1) → ℝ := fun j => ‖(v j).snd‖
  let C : ℝ := (n + 1 : ℝ)⁻¹ * ‖a‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : Continuous (fun s : ℝ => C *
      ∑ j : Fin (n + 1), A j * ∏ i : Fin n,
        (s * A (j.succAbove i) + B (j.succAbove i))) := by fun_prop
  calc
    ‖∫ s in (0 : ℝ)..1, ckPrimitiveKernelCLM E F n s a v‖
      ≤ ∫ s in (0 : ℝ)..1, C *
          ∑ j : Fin (n + 1), A j * ∏ i : Fin n,
            (s * A (j.succAbove i) + B (j.succAbove i)) := by
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
          (Filter.Eventually.of_forall fun s hs => ?_) (hg.intervalIntegrable 0 1)
        have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hs
        exact ckPrimitiveKernelCLM_eval_norm_le E F s hs'.1.le a v
    _ = C * ((∏ j : Fin (n + 1), (A j + B j)) - ∏ j : Fin (n + 1), B j) := by
      rw [intervalIntegral.integral_const_mul, ck_integral_product_derivative]
    _ ≤ C * ∏ j : Fin (n + 1), (A j + B j) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact sub_le_self _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = ((n + 1 : ℝ)⁻¹ * ‖a‖) * ∏ j : Fin (n + 1), ‖v j‖ := by
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      simpa [A, B, Real.norm_eq_abs] using (WithLp.prod_norm_eq_of_L1 (v j)).symm

theorem ckPrimitiveCoeffCLM_norm_apply_le [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) :
    ‖ckPrimitiveCoeffCLM E F n a‖ ≤ (n + 1 : ℝ)⁻¹ * ‖a‖ := by
  simpa only [ckPrimitiveCoeffCLM, ContinuousLinearMap.comp_apply, ckSymmetrizeCLM_apply]
    using (ckSymmetrize_norm_le (CKTimeSpace E) F _).trans
      (ckPrimitiveIntegral_norm_le E F a)

theorem ckPrimitiveCoeffCLM_norm_le [CompleteSpace F] (n : ℕ) :
    ‖ckPrimitiveCoeffCLM E F n‖ ≤ (n + 1 : ℝ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound (ckPrimitiveCoeffCLM E F n) (by positivity)
  exact ckPrimitiveCoeffCLM_norm_apply_le E F

theorem ckPrimitiveCoeffCLM_symmetric [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) (v : Fin (n + 1) → CKTimeSpace E)
    (σ : Equiv.Perm (Fin (n + 1))) :
    ckPrimitiveCoeffCLM E F n a (v ∘ σ) = ckPrimitiveCoeffCLM E F n a v := by
  simp only [ckPrimitiveCoeffCLM, ContinuousLinearMap.comp_apply, ckSymmetrizeCLM_apply]
  exact ckSymmetrize_symmetric (CKTimeSpace E) F _ v σ

def ckTimePrimitiveFormal [CompleteSpace F] (p : CKSeries (CKTimeSpace E) F) :
    FormalMultilinearSeries ℝ (CKTimeSpace E) F
  | 0 => 0
  | n + 1 => ckPrimitiveCoeffCLM E F n (p.coeff n)

theorem ckTimePrimitiveFormal_norm_le [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) (n : ℕ) :
    ‖ckTimePrimitiveFormal E F p (n + 1)‖ ≤ (1 / 2 : ℝ) * ‖p.coeff n‖ := by
  cases n with
  | zero => simp [ckTimePrimitiveFormal]
  | succ n =>
    apply (ckPrimitiveCoeffCLM_norm_apply_le E F (p.coeff (n + 1))).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [one_div, Nat.cast_add, Nat.cast_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (by have hn : (0 : ℝ) ≤ n := by positivity
            linarith : (2 : ℝ) ≤ (n + 1 + 1 : ℝ))

theorem ckTimePrimitiveFormal_summable [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) :
    Summable (fun n => ‖ckTimePrimitiveFormal E F p n‖) := by
  apply Summable.comp_nat_add (k := 1)
  exact (p.summable_norm.mul_left (1 / 2 : ℝ)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (ckTimePrimitiveFormal_norm_le E F p)

def ckTimePrimitiveSeries [CompleteSpace F] (p : CKSeries (CKTimeSpace E) F) :
    CKSeries (CKTimeSpace E) F :=
  CKSeries.ofCoeffs (ckTimePrimitiveFormal E F p)
    (ckTimePrimitiveFormal_summable E F p) rfl
    (by
      intro n v σ
      cases n with
      | zero => rfl
      | succ n => exact ckPrimitiveCoeffCLM_symmetric E F (p.coeff n) v σ)

@[simp] theorem ckTimePrimitiveSeries_coeff_succ [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) (n : ℕ) :
    (ckTimePrimitiveSeries E F p).coeff (n + 1) =
      ckPrimitiveCoeffCLM E F n (p.coeff n) := rfl

theorem ckTimePrimitiveSeries_norm_le [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) :
    ‖ckTimePrimitiveSeries E F p‖ ≤ (1 / 2 : ℝ) * ‖p‖ := by
  let q := ckTimePrimitiveSeries E F p
  have hq : HasSum (fun n => ‖q.coeff (n + 1)‖) ‖q‖ := by
    simpa using (hasSum_nat_add_iff' 1).2 q.hasSum_norm
  exact hasSum_le (fun n => ckTimePrimitiveFormal_norm_le E F p n) hq
    (p.hasSum_norm.mul_left (1 / 2 : ℝ))

def timePrimitive [CompleteSpace F] :
    CKSeries (CKTimeSpace E) F →L[ℝ] CKSeries (CKTimeSpace E) F :=
  LinearMap.mkContinuous
    { toFun := ckTimePrimitiveSeries E F
      map_add' := by
        intro p q
        apply CKSeries.ext
        intro n
        cases n with
        | zero => simp
        | succ n => simp
      map_smul' := by
        intro c p
        apply CKSeries.ext
        intro n
        cases n with
        | zero => simp
        | succ n => simp }
    (1 / 2 : ℝ) (ckTimePrimitiveSeries_norm_le E F)

@[simp] theorem timePrimitive_apply [CompleteSpace F] (p : CKSeries (CKTimeSpace E) F) :
    timePrimitive E F p = ckTimePrimitiveSeries E F p := rfl

theorem timePrimitive_norm_le [CompleteSpace F] : ‖timePrimitive E F‖ ≤ (1 / 2 : ℝ) := by
  exact ContinuousLinearMap.opNorm_le_bound (timePrimitive E F) (by norm_num)
    (ckTimePrimitiveSeries_norm_le E F)

theorem ckPrimitiveKernelCLM_diagonal {n : ℕ} (s : ℝ)
    (a : CKCoeff (CKTimeSpace E) F n) (z : CKTimeSpace E) :
    ckPrimitiveKernelCLM E F n s a (fun _ => z) =
      z.fst • a (fun _ => ckTimeScale E s z) := by
  rw [ckPrimitiveKernelCLM_apply]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  rw [inv_mul_cancel₀ hn, one_smul]

theorem ckPrimitiveCoeffCLM_diagonal [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) (z : CKTimeSpace E) :
    ckPrimitiveCoeffCLM E F n a (fun _ => z) =
      ∫ s in (0 : ℝ)..1, z.fst • a (fun _ => ckTimeScale E s z) := by
  simp only [ckPrimitiveCoeffCLM, ContinuousLinearMap.comp_apply,
    ckSymmetrizeCLM_apply, ckSymmetrize_diagonal]
  rw [ckPrimitiveIntegral_apply]
  apply intervalIntegral.integral_congr
  intro s _
  exact ckPrimitiveKernelCLM_diagonal E F s a z

theorem ckTimeScale_norm_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (z : CKTimeSpace E) : ‖ckTimeScale E s z‖ ≤ ‖z‖ := by
  rw [ckTimeScale_norm E s hs.1, WithLp.prod_norm_eq_of_L1]
  simpa only [Real.norm_eq_abs, one_mul, add_comm] using
    add_le_add_right (mul_le_mul_of_nonneg_right hs.2 (abs_nonneg z.fst)) ‖z.snd‖

set_option maxHeartbeats 1000000 in
theorem timePrimitive_eval_eq_scaled_integral [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) {z : CKTimeSpace E} (hz : ‖z‖ < 1) :
    (timePrimitive E F p).eval z =
      ∫ s in (0 : ℝ)..1, z.fst • p.eval (ckTimeScale E s z) := by
  let q := timePrimitive E F p
  have hs (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) : ‖ckTimeScale E s z‖ < 1 := by
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        Set.uIoc_subset_uIcc hs
    exact (ckTimeScale_norm_le E hs' z).trans_lt hz
  have hc (n : ℕ) : Continuous (fun s : ℝ =>
      z.fst • p.coeff n (fun _ => ckTimeScale E s z)) := by
    apply Continuous.const_smul
    exact (p.coeff n).cont.comp
      (continuous_pi fun _ => (ckTimeScale_continuous E).clm_apply continuous_const)
  have hsum : HasSum (fun n => ∫ s in (0 : ℝ)..1,
      z.fst • p.coeff n (fun _ => ckTimeScale E s z))
      (∫ s in (0 : ℝ)..1, z.fst • p.eval (ckTimeScale E s z)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => |z.fst| * ‖p.coeff n‖)
      (fun n => (hc n).aestronglyMeasurable)
    · intro n
      exact Filter.Eventually.of_forall fun s hsm => by
        rw [norm_smul, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg z.fst)
        exact (p.coeff n).unit_le_opNorm
          ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun _ => (hs s hsm).le)
    · exact Filter.Eventually.of_forall fun _ _ => p.summable_norm.mul_left |z.fst|
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s hsm => (p.hasSum_eval (hs s hsm)).const_smul z.fst
  have hshift : HasSum (fun n => q.coeff (n + 1) (fun _ => z))
      (∫ s in (0 : ℝ)..1, z.fst • p.eval (ckTimeScale E s z)) := by
    simpa only [q, timePrimitive_apply, ckTimePrimitiveSeries_coeff_succ,
      ckPrimitiveCoeffCLM_diagonal] using hsum
  have hfull : HasSum (fun n => q.coeff n (fun _ => z))
      (∫ s in (0 : ℝ)..1, z.fst • p.eval (ckTimeScale E s z)) := by
    simpa only [CKSeries.coeff_zero, ContinuousMultilinearMap.zero_apply, zero_add] using
      (HasSum.zero_add (f := fun n => q.coeff n (fun _ => z)) hshift)
  exact (q.hasSum_eval hz).unique hfull

theorem timePrimitive_eval_eq_integral [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) {z : CKTimeSpace E} (hz : ‖z‖ < 1) :
    (timePrimitive E F p).eval z =
      ∫ t in (0 : ℝ)..z.fst, p.eval (WithLp.toLp 1 (t, z.snd)) := by
  rw [timePrimitive_eval_eq_scaled_integral E F p hz]
  simp only [ckTimeScale_apply, intervalIntegral.integral_smul]
  simpa using intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1)
    (fun t => p.eval (WithLp.toLp 1 (t, z.snd))) z.fst

theorem ckSymmetric_update_eq_snoc {n : ℕ} (a : CKCoeff E F (n + 1))
    (ha : ∀ (v : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))),
      a (v ∘ σ) = a v) (x y : E) (j : Fin (n + 1)) :
    a (Function.update (fun _ => x) j y) = a (Fin.snoc (fun _ : Fin n => x) y) := by
  have hlast : Function.update (fun _ : Fin (n + 1) => x) (Fin.last n) y =
      Fin.snoc (fun _ : Fin n => x) y := by
    funext k
    refine Fin.lastCases ?_ (fun i => ?_) k <;> simp
  have hp : (Fin.snoc (fun _ : Fin n => x) y) ∘ Equiv.swap j (Fin.last n) =
      Function.update (fun _ => x) j y := by
    rw [← hlast]
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · have hk' : Equiv.swap j (Fin.last n) k ≠ Fin.last n := by
        intro h
        apply hk
        apply (Equiv.swap j (Fin.last n)).injective
        simpa using h
      simp only [Function.comp_apply, Function.update_of_ne hk', Function.update_of_ne hk]
  rw [← hp]
  exact ha _ _

theorem ckSymmetric_hasFDerivAt_diagonal {n : ℕ} (a : CKCoeff E F (n + 1))
    (ha : ∀ (v : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))),
      a (v ∘ σ) = a v) (x : E) :
    HasFDerivAt (fun z : E => a (fun _ => z))
      ((n + 1 : ℝ) • a.curryRight (fun _ => x)) x := by
  let δ : E →L[ℝ] (Fin (n + 1) → E) :=
    ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E)
  have hd := (a.hasFDerivAt (δ x)).comp x δ.hasFDerivAt
  convert! hd using 1
  ext y
  simp only [δ, ContinuousLinearMap.smul_apply, ContinuousMultilinearMap.curryRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.id_apply]
  simp_rw [ckSymmetric_update_eq_snoc E F a ha x y]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one]

def ckPrimitiveDerivativeCoeffCLM [CompleteSpace F] (n : ℕ) :
    CKCoeff (CKTimeSpace E) F n →L[ℝ]
      CKCoeff (CKTimeSpace E) (CKTimeSpace E →L[ℝ] F) n :=
  (n + 1 : ℝ) • (ckSymmetrizeCLM (CKTimeSpace E) (CKTimeSpace E →L[ℝ] F) n).comp
    ((continuousMultilinearCurryRightEquiv' ℝ n (CKTimeSpace E) F).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ckPrimitiveCoeffCLM E F n))

theorem ckPrimitiveDerivativeCoeffCLM_apply [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) :
    ckPrimitiveDerivativeCoeffCLM E F n a =
      (n + 1 : ℝ) • ckSymmetrize (CKTimeSpace E) (CKTimeSpace E →L[ℝ] F)
        (ckPrimitiveCoeffCLM E F n a).curryRight := by
  simp only [ckPrimitiveDerivativeCoeffCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ckSymmetrizeCLM_apply]
  apply congrArg (fun b : CKCoeff (CKTimeSpace E) (CKTimeSpace E →L[ℝ] F) n =>
    (n + 1 : ℝ) • ckSymmetrize (CKTimeSpace E) (CKTimeSpace E →L[ℝ] F) b)
  ext v y
  rfl

theorem ckPrimitiveDerivativeCoeffCLM_norm_apply_le [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) : ‖ckPrimitiveDerivativeCoeffCLM E F n a‖ ≤ ‖a‖ := by
  rw [ckPrimitiveDerivativeCoeffCLM_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    (n + 1 : ℝ) * ‖ckSymmetrize (CKTimeSpace E) (CKTimeSpace E →L[ℝ] F)
        (ckPrimitiveCoeffCLM E F n a).curryRight‖
      ≤ (n + 1 : ℝ) * ‖(ckPrimitiveCoeffCLM E F n a).curryRight‖ :=
        mul_le_mul_of_nonneg_left (ckSymmetrize_norm_le _ _ _) (by positivity)
    _ = (n + 1 : ℝ) * ‖ckPrimitiveCoeffCLM E F n a‖ := by rw [ContinuousMultilinearMap.curryRight_norm]
    _ ≤ (n + 1 : ℝ) * ((n + 1 : ℝ)⁻¹ * ‖a‖) :=
      mul_le_mul_of_nonneg_left (ckPrimitiveCoeffCLM_norm_apply_le E F a) (by positivity)
    _ = ‖a‖ := by rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_mul]

theorem ckPrimitiveDerivativeCoeffCLM_symmetric [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) (v : Fin n → CKTimeSpace E) (σ : Equiv.Perm (Fin n)) :
    ckPrimitiveDerivativeCoeffCLM E F n a (v ∘ σ) = ckPrimitiveDerivativeCoeffCLM E F n a v := by
  simp only [ckPrimitiveDerivativeCoeffCLM_apply, ContinuousMultilinearMap.smul_apply,
    ckSymmetrize_symmetric]

def ckPrimitiveDerivativeSeries [CompleteSpace F] (p : CKSeries (CKTimeSpace E) F) :
    CKSeries (CKTimeSpace E) (CKTimeSpace E →L[ℝ] F) :=
  CKSeries.ofCoeffs (fun n => ckPrimitiveDerivativeCoeffCLM E F n (p.coeff n))
    (p.summable_norm.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ckPrimitiveDerivativeCoeffCLM_norm_apply_le E F (p.coeff n)))
    (by rw [p.coeff_zero, map_zero])
    (fun n v σ => ckPrimitiveDerivativeCoeffCLM_symmetric E F (p.coeff n) v σ)

@[simp] theorem ckPrimitiveDerivativeSeries_coeff [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) (n : ℕ) :
    (ckPrimitiveDerivativeSeries E F p).coeff n =
      ckPrimitiveDerivativeCoeffCLM E F n (p.coeff n) := rfl

theorem ckPrimitiveDerivativeSeries_norm_le [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) : ‖ckPrimitiveDerivativeSeries E F p‖ ≤ ‖p‖ :=
  hasSum_le (fun n => ckPrimitiveDerivativeCoeffCLM_norm_apply_le E F (p.coeff n))
    (ckPrimitiveDerivativeSeries E F p).hasSum_norm p.hasSum_norm

def timePrimitiveDerivative [CompleteSpace F] :
    CKSeries (CKTimeSpace E) F →L[ℝ] CKSeries (CKTimeSpace E) (CKTimeSpace E →L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun := ckPrimitiveDerivativeSeries E F
      map_add' := by
        intro p q
        apply CKSeries.ext
        intro n
        simp only [ckPrimitiveDerivativeSeries_coeff, CKSeries.coeff_add, map_add]
      map_smul' := by
        intro c p
        apply CKSeries.ext
        intro n
        simp only [ckPrimitiveDerivativeSeries_coeff, CKSeries.coeff_smul, map_smul] }
    1 (fun p => by simpa only [one_mul] using ckPrimitiveDerivativeSeries_norm_le E F p)

@[simp] theorem timePrimitiveDerivative_coeff [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) (n : ℕ) :
    (timePrimitiveDerivative E F p).coeff n =
      ckPrimitiveDerivativeCoeffCLM E F n (p.coeff n) := rfl

theorem timePrimitiveDerivative_norm_le [CompleteSpace F] : ‖timePrimitiveDerivative E F‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (timePrimitiveDerivative E F) zero_le_one
  intro p
  change ‖ckPrimitiveDerivativeSeries E F p‖ ≤ 1 * ‖p‖
  simpa only [one_mul] using ckPrimitiveDerivativeSeries_norm_le E F p

theorem ckPrimitiveCoeffCLM_hasFDerivAt_diagonal [CompleteSpace F] {n : ℕ}
    (a : CKCoeff (CKTimeSpace E) F n) (z : CKTimeSpace E) :
    HasFDerivAt (fun w : CKTimeSpace E => ckPrimitiveCoeffCLM E F n a (fun _ => w))
      (ckPrimitiveDerivativeCoeffCLM E F n a (fun _ => z)) z := by
  simpa only [ckPrimitiveDerivativeCoeffCLM_apply, ContinuousMultilinearMap.smul_apply,
    ckSymmetrize_diagonal] using
    ckSymmetric_hasFDerivAt_diagonal (CKTimeSpace E) F
      (ckPrimitiveCoeffCLM E F n a) (ckPrimitiveCoeffCLM_symmetric E F a) z

theorem timePrimitive_hasFDerivAt [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) {z : CKTimeSpace E} (hz : ‖z‖ < 1) :
    HasFDerivAt (timePrimitive E F p).eval ((timePrimitiveDerivative E F p).eval z) z := by
  let q := timePrimitive E F p
  let d := timePrimitiveDerivative E F p
  let u (n : ℕ) (w : CKTimeSpace E) := ckPrimitiveCoeffCLM E F n (p.coeff n) (fun _ => w)
  have hz' : z ∈ Metric.ball (0 : CKTimeSpace E) 1 := by simpa using hz
  have hd : HasFDerivAt (fun w => ∑' n, u n w)
      (∑' n, d.coeff n (fun _ => z)) z := by
    apply hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (f := u)
      (f' := fun n w => d.coeff n (fun _ => w)) (x₀ := 0) (x := z)
      p.summable_norm Metric.isOpen_ball
      (convex_ball (0 : CKTimeSpace E) (1 : ℝ)).isPreconnected
    · intro n w _
      exact ckPrimitiveCoeffCLM_hasFDerivAt_diagonal E F (p.coeff n) w
    · intro n w hw
      have hw' : ‖w‖ < 1 := by simpa using hw
      exact ((d.coeff n).unit_le_opNorm
        ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun _ => hw'.le)).trans
          (ckPrimitiveDerivativeCoeffCLM_norm_apply_le E F (p.coeff n))
    · exact Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1)
    · change Summable (fun n => ckPrimitiveCoeffCLM E F n (p.coeff n) 0)
      simp only [ContinuousMultilinearMap.map_zero]
      exact summable_zero
    · exact hz'
  have heq : q.eval =ᶠ[𝓝 z] (fun w => ∑' n, u n w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz'] with w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    calc
      q.eval w = ∑' n, q.coeff n (fun _ => w) := (q.hasSum_eval hw').tsum_eq.symm
      _ = q.coeff 0 (fun _ => w) + ∑' n, q.coeff (n + 1) (fun _ => w) :=
        (q.hasSum_eval hw').summable.tsum_eq_zero_add
      _ = ∑' n, u n w := by simp [q, u]
  rw [(d.hasSum_eval hz).tsum_eq] at hd
  exact hd.congr_of_eventuallyEq heq

theorem timePrimitiveDerivative_eval_eq_fderiv [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) {z : CKTimeSpace E} (hz : ‖z‖ < 1) :
    (timePrimitiveDerivative E F p).eval z = fderiv ℝ (timePrimitive E F p).eval z :=
  (timePrimitive_hasFDerivAt E F p hz).fderiv.symm

@[simp] theorem ckSpaceInclude_apply (x : E) :
    ckSpaceInclude E x = WithLp.toLp 1 (0, x) := rfl

theorem ckSpaceInclude_norm_le : ‖ckSpaceInclude E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (ckSpaceInclude E) zero_le_one
  intro x
  simp [ckSpaceInclude_apply, WithLp.prod_norm_eq_of_L1]

def ckSpatialRestriction : (CKTimeSpace E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
  (ContinuousLinearMap.compL ℝ E (CKTimeSpace E) F).flip (ckSpaceInclude E)

@[simp] theorem ckSpatialRestriction_apply (L : CKTimeSpace E →L[ℝ] F) :
    ckSpatialRestriction E F L = L.comp (ckSpaceInclude E) := rfl

theorem ckSpatialRestriction_norm_le : ‖ckSpatialRestriction E F‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (ckSpatialRestriction E F) zero_le_one
  intro L
  calc
    ‖ckSpatialRestriction E F L‖ ≤ ‖L‖ * ‖ckSpaceInclude E‖ :=
      ContinuousLinearMap.opNorm_comp_le L (ckSpaceInclude E)
    _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left (ckSpaceInclude_norm_le E) (norm_nonneg L)
    _ = 1 * ‖L‖ := by ring

def spatialPrimitive [CompleteSpace F] :
    CKSeries (CKTimeSpace E) F →L[ℝ] CKSeries (CKTimeSpace E) (E →L[ℝ] F) :=
  (CKSeries.postcomposeCLM (ckSpatialRestriction E F)).comp (timePrimitiveDerivative E F)

theorem spatialPrimitive_norm_le [CompleteSpace F] : ‖spatialPrimitive E F‖ ≤ 1 := by
  calc
    ‖spatialPrimitive E F‖ ≤ ‖CKSeries.postcomposeCLM (E := CKTimeSpace E) (ckSpatialRestriction E F)‖ *
        ‖timePrimitiveDerivative E F‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      ((CKSeries.norm_postcomposeCLM_le (ckSpatialRestriction E F)).trans (ckSpatialRestriction_norm_le E F))
      (timePrimitiveDerivative_norm_le E F) (timePrimitiveDerivative E F).opNorm_nonneg zero_le_one
    _ = 1 := by norm_num

theorem spatialPrimitive_eval_eq_fderiv [CompleteSpace F]
    (p : CKSeries (CKTimeSpace E) F) {z : CKTimeSpace E} (hz : ‖z‖ < 1) :
    (spatialPrimitive E F p).eval z =
      (fderiv ℝ (timePrimitive E F p).eval z).comp (ckSpaceInclude E) := by
  simp only [spatialPrimitive, ContinuousLinearMap.comp_apply, CKSeries.postcomposeCLM_apply,
    CKSeries.eval_postcompose _ _ hz, ckSpatialRestriction_apply,
    timePrimitiveDerivative_eval_eq_fderiv E F p hz]

end

end NSEGR.NativeLiterature
