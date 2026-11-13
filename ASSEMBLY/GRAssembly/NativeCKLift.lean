import Mathlib
import GRAssembly.NativeCKSeries

/-!
Bounded operations on the concrete symmetric `ℓ¹` coefficient space.
All coefficient and evaluation maps are derived from that space itself.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology BigOperators ENNReal

namespace NSEGR.NativeLiterature

noncomputable section

namespace CKSeries

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def coeffCLM (n : ℕ) : CKSeries E F →L[ℝ] CKCoeff E F n :=
  (lp.evalCLM ℝ (CKCoeff E F) 1 n).comp (CKSeriesSpace E F).subtypeL

@[simp] theorem coeffCLM_apply (n : ℕ) (p : CKSeries E F) :
    coeffCLM n p = p.coeff n := rfl

theorem coeff_tsum {ι : Type*} (p : ι → CKSeries E F) (hp : Summable p) (n : ℕ) :
    (∑' i, p i).coeff n = ∑' i, (p i).coeff n :=
  (coeffCLM n).map_tsum hp

def postcompose (L : F →L[ℝ] G) (p : CKSeries E F) : CKSeries E G :=
  ofCoeffs (fun n => L.compContinuousMultilinearMap (p.coeff n))
    ((p.summable_norm.mul_left ‖L‖).of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => L.norm_compContinuousMultilinearMap_le (p.coeff n)))
    (by ext v; simp)
    (by intro n v σ; exact congrArg L (p.coeff_symm n v σ))

@[simp] theorem postcompose_coeff (L : F →L[ℝ] G) (p : CKSeries E F) (n : ℕ) :
    (postcompose L p).coeff n = L.compContinuousMultilinearMap (p.coeff n) := rfl

theorem norm_postcompose_le (L : F →L[ℝ] G) (p : CKSeries E F) :
    ‖postcompose L p‖ ≤ ‖L‖ * ‖p‖ := by
  apply hasSum_le (fun n => L.norm_compContinuousMultilinearMap_le (p.coeff n))
    (postcompose L p).hasSum_norm (p.hasSum_norm.mul_left ‖L‖)

@[simp] theorem postcompose_add (L : F →L[ℝ] G) (p q : CKSeries E F) :
    postcompose L (p + q) = postcompose L p + postcompose L q := by
  ext n v
  simp

@[simp] theorem postcompose_smul (L : F →L[ℝ] G) (c : ℝ) (p : CKSeries E F) :
    postcompose L (c • p) = c • postcompose L p := by
  ext n v
  simp

def postcomposeCLM (L : F →L[ℝ] G) : CKSeries E F →L[ℝ] CKSeries E G :=
  LinearMap.mkContinuous
    { toFun := postcompose L
      map_add' := postcompose_add L
      map_smul' := postcompose_smul L }
    ‖L‖ (norm_postcompose_le L)

@[simp] theorem postcomposeCLM_apply (L : F →L[ℝ] G) (p : CKSeries E F) :
    postcomposeCLM L p = postcompose L p := rfl

theorem norm_postcomposeCLM_le (L : F →L[ℝ] G) : ‖postcomposeCLM (E := E) L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (norm_nonneg L)
  exact norm_postcompose_le L

def single (n : ℕ) (a : CKCoeff E F n) (hzero : n = 0 → a = 0)
    (hsymm : ∀ (v : Fin n → E) (σ : Equiv.Perm (Fin n)), a (v ∘ σ) = a v) :
    CKSeries E F := by
  classical
  refine ⟨lp.single 1 n a, ?_, ?_⟩
  · by_cases hn : n = 0
    · subst n
      simp [hzero rfl]
    · exact lp.single_apply_ne 1 n a (Ne.symm hn)
  · intro k v σ
    by_cases hk : k = n
    · subst k
      simpa only [lp.single_apply_self] using hsymm v σ
    · simp only [lp.single_apply_ne 1 n a hk, ContinuousMultilinearMap.zero_apply]

@[simp] theorem single_coeff_self (n : ℕ) (a : CKCoeff E F n) (hzero hsymm) :
    (single n a hzero hsymm).coeff n = a := by
  exact lp.single_apply_self 1 n a

theorem single_coeff_ne (n : ℕ) (a : CKCoeff E F n) (hzero hsymm) {k : ℕ}
    (hk : k ≠ n) : (single n a hzero hsymm).coeff k = 0 :=
  lp.single_apply_ne 1 n a hk

@[simp] theorem norm_single (n : ℕ) (a : CKCoeff E F n) (hzero hsymm) :
    ‖single n a hzero hsymm‖ = ‖a‖ :=
  lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1) n a

variable [CompleteSpace F]

@[simp] theorem eval_add (p q : CKSeries E F) {x : E} (hx : ‖x‖ < 1) :
    (p + q).eval x = p.eval x + q.eval x := by
  apply HasSum.unique ((p + q).hasSum_eval hx)
  simpa only [coeff_add, ContinuousMultilinearMap.add_apply] using
    (p.hasSum_eval hx).add (q.hasSum_eval hx)

@[simp] theorem eval_smul (c : ℝ) (p : CKSeries E F) {x : E} (hx : ‖x‖ < 1) :
    (c • p).eval x = c • p.eval x := by
  apply HasSum.unique ((c • p).hasSum_eval hx)
  simpa only [coeff_smul, ContinuousMultilinearMap.smul_apply] using
    (p.hasSum_eval hx).const_smul c

def evalCLM (x : E) (hx : ‖x‖ < 1) : CKSeries E F →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun p => p.eval x
      map_add' := fun p q => eval_add p q hx
      map_smul' := fun c p => eval_smul c p hx }
    1 (by intro p; simpa using p.norm_eval_le hx)

@[simp] theorem evalCLM_apply (x : E) (hx : ‖x‖ < 1) (p : CKSeries E F) :
    evalCLM x hx p = p.eval x := rfl

theorem eval_tsum {ι : Type*} (p : ι → CKSeries E F) (hp : Summable p)
    {x : E} (hx : ‖x‖ < 1) :
    (∑' i, p i).eval x = ∑' i, (p i).eval x :=
  (evalCLM x hx).map_tsum hp

@[simp] theorem eval_postcompose [CompleteSpace G] (L : F →L[ℝ] G)
    (p : CKSeries E F) {x : E} (hx : ‖x‖ < 1) :
    (postcompose L p).eval x = L (p.eval x) := by
  apply HasSum.unique ((postcompose L p).hasSum_eval hx)
  exact L.hasSum (p.hasSum_eval hx)

@[simp] theorem eval_single (n : ℕ) (a : CKCoeff E F n) (hzero hsymm)
    {x : E} (hx : ‖x‖ < 1) :
    (single n a hzero hsymm).eval x = a (fun _ => x) := by
  classical
  apply HasSum.unique ((single n a hzero hsymm).hasSum_eval hx)
  have heq : (fun k => (single n a hzero hsymm).coeff k (fun _ => x)) =
      fun k => if k = n then a (fun _ => x) else 0 := by
    funext k
    by_cases hk : k = n
    · subst k
      simp
    · simp [single_coeff_ne n a hzero hsymm hk, hk]
  rw [heq]
  exact hasSum_ite_eq n (a (fun _ => x))

end CKSeries

end

end NSEGR.NativeLiterature
