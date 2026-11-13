import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.WithLp
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
Native coefficient spaces for the analytic CK construction.
The constant coefficient is zero and every coefficient is symmetric.
No existence or analytic-PDE law is included as a structure field.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators ENNReal

namespace NSEGR.NativeLiterature

noncomputable section

abbrev CKTimeSpace (E : Type*) := WithLp 1 (ℝ × E)

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev CKCoeff (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F

def CKSeriesSpace : Submodule ℝ (lp (CKCoeff E F) 1) where
  carrier := {p | p 0 = 0 ∧ ∀ (n : ℕ) (v : Fin n → E) (σ : Equiv.Perm (Fin n)),
    p n (v ∘ σ) = p n v}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    constructor
    · change p 0 + q 0 = 0
      rw [hp.1, hq.1, add_zero]
    · intro n v σ
      change p n (v ∘ σ) + q n (v ∘ σ) = p n v + q n v
      rw [hp.2 n v σ, hq.2 n v σ]
  smul_mem' := by
    intro c p hp
    constructor
    · change c • p 0 = 0
      rw [hp.1, smul_zero]
    · intro n v σ
      change c • p n (v ∘ σ) = c • p n v
      rw [hp.2 n v σ]

abbrev CKSeries := CKSeriesSpace E F

theorem ckSeriesSpace_isClosed : IsClosed (CKSeriesSpace E F : Set (lp (CKCoeff E F) 1)) := by
  have hc (n : ℕ) (v : Fin n → E) :
      Continuous (fun p : lp (CKCoeff E F) 1 => p n v) :=
    (continuous_eval_const v).comp (lp.evalCLM ℝ (CKCoeff E F) 1 n).continuous
  change IsClosed {p : lp (CKCoeff E F) 1 | p 0 = 0 ∧
    ∀ (n : ℕ) (v : Fin n → E) (σ : Equiv.Perm (Fin n)), p n (v ∘ σ) = p n v}
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isClosed_eq (lp.evalCLM ℝ (CKCoeff E F) 1 0).continuous continuous_const).inter
    (isClosed_iInter fun n => isClosed_iInter fun v => isClosed_iInter fun σ =>
      isClosed_eq (hc n (v ∘ σ)) (hc n v))

instance ckSeries_completeSpace [CompleteSpace F] : CompleteSpace (CKSeries E F) :=
  (ckSeriesSpace_isClosed E F).isComplete.completeSpace_coe

namespace CKSeries

variable {E F}

def coeff (p : CKSeries E F) (n : ℕ) : CKCoeff E F n := p.val n

def formal (p : CKSeries E F) : FormalMultilinearSeries ℝ E F := p.coeff

@[simp] theorem coeff_zero (p : CKSeries E F) : p.coeff 0 = 0 := p.property.1

theorem coeff_symm (p : CKSeries E F) (n : ℕ) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) : p.coeff n (v ∘ σ) = p.coeff n v := p.property.2 n v σ

@[simp] theorem coeff_add (p q : CKSeries E F) (n : ℕ) :
    (p + q).coeff n = p.coeff n + q.coeff n := rfl

@[simp] theorem coeff_smul (c : ℝ) (p : CKSeries E F) (n : ℕ) :
    (c • p).coeff n = c • p.coeff n := rfl

@[simp] theorem coeff_sub (p q : CKSeries E F) (n : ℕ) :
    (p - q).coeff n = p.coeff n - q.coeff n := rfl

@[simp] theorem coeff_zero_series (n : ℕ) : (0 : CKSeries E F).coeff n = 0 := rfl

@[ext] theorem ext {p q : CKSeries E F} (h : ∀ n, p.coeff n = q.coeff n) : p = q := by
  apply Subtype.ext
  apply lp.ext
  exact h

theorem hasSum_norm (p : CKSeries E F) : HasSum (fun n => ‖p.coeff n‖) ‖p‖ := by
  simpa [coeff] using lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) p.val

theorem summable_norm (p : CKSeries E F) : Summable (fun n => ‖p.coeff n‖) :=
  p.hasSum_norm.summable

theorem norm_eq_tsum (p : CKSeries E F) : ‖p‖ = ∑' n, ‖p.coeff n‖ :=
  p.hasSum_norm.tsum_eq.symm

theorem coeff_norm_le (p : CKSeries E F) (n : ℕ) : ‖p.coeff n‖ ≤ ‖p‖ :=
  lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞) ≠ 0) p.val n

def ofCoeffs (q : FormalMultilinearSeries ℝ E F)
    (hq : Summable (fun n => ‖q n‖)) (hzero : q 0 = 0)
    (hsym : ∀ (n : ℕ) (v : Fin n → E) (σ : Equiv.Perm (Fin n)), q n (v ∘ σ) = q n v) :
    CKSeries E F :=
  ⟨⟨q, by simpa [Memℓp] using hq⟩, hzero, hsym⟩

@[simp] theorem ofCoeffs_coeff (q : FormalMultilinearSeries ℝ E F)
    (hq : Summable (fun n => ‖q n‖)) (hzero : q 0 = 0)
    (hsym : ∀ (n : ℕ) (v : Fin n → E) (σ : Equiv.Perm (Fin n)), q n (v ∘ σ) = q n v)
    (n : ℕ) : (ofCoeffs q hq hzero hsym).coeff n = q n := rfl

theorem one_le_radius (p : CKSeries E F) : (1 : ℝ≥0∞) ≤ p.formal.radius := by
  have h := p.formal.le_radius_of_summable (r := (1 : ℝ≥0))
    (by simpa [formal] using p.summable_norm)
  simpa using h

theorem radius_pos (p : CKSeries E F) : 0 < p.formal.radius :=
  lt_of_lt_of_le (by norm_num) p.one_le_radius

def eval (p : CKSeries E F) : E → F := p.formal.sum

theorem hasFPowerSeriesOnBall [CompleteSpace F] (p : CKSeries E F) :
    HasFPowerSeriesOnBall p.eval p.formal 0 1 := by
  exact (p.formal.hasFPowerSeriesOnBall p.radius_pos).mono (by norm_num) p.one_le_radius

theorem analyticAt_zero [CompleteSpace F] (p : CKSeries E F) : AnalyticAt ℝ p.eval 0 :=
  p.hasFPowerSeriesOnBall.analyticAt

theorem analyticAt [CompleteSpace F] (p : CKSeries E F) {x : E} (hx : ‖x‖ < 1) :
    AnalyticAt ℝ p.eval x := by
  apply p.hasFPowerSeriesOnBall.analyticAt_of_mem
  change x ∈ Metric.eball (0 : E) ((1 : ℝ≥0) : ℝ≥0∞)
  rw [Metric.eball_coe]
  simpa using hx

@[simp] theorem eval_zero [CompleteSpace F] (p : CKSeries E F) : p.eval 0 = 0 := by
  have h := p.hasFPowerSeriesOnBall.coeff_zero (fun i => Fin.elim0 i)
  simpa [formal, p.coeff_zero] using h.symm

theorem hasSum_eval [CompleteSpace F] (p : CKSeries E F) {x : E} (hx : ‖x‖ < 1) :
    HasSum (fun n => p.coeff n (fun _ => x)) (p.eval x) := by
  have hx' : x ∈ Metric.eball (0 : E) (1 : ℝ≥0∞) := by
    change x ∈ Metric.eball (0 : E) ((1 : ℝ≥0) : ℝ≥0∞)
    rw [Metric.eball_coe]
    simpa using hx
  simpa [formal] using p.hasFPowerSeriesOnBall.hasSum hx'

theorem norm_eval_le [CompleteSpace F] (p : CKSeries E F) {x : E} (hx : ‖x‖ < 1) :
    ‖p.eval x‖ ≤ ‖p‖ := by
  apply (p.hasSum_eval hx).norm_le_of_bounded p.hasSum_norm
  intro n
  exact (p.coeff n).unit_le_opNorm ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun _ => hx.le)

end CKSeries

end

end NSEGR.NativeLiterature
