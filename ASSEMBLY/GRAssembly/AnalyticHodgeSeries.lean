import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic

/-!
Uniform real analytic derivative bounds on compact sets.  The recentering
majorant is an actual summable family from Mathlib's multilinear series;
no complexification or independent analytic estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly

open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology ContDiff

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def analyticShiftMajorant (p : FormalMultilinearSeries ℝ E F)
    (r : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ∑' s : Σ l : ℕ, {s : Finset (Fin (n + l)) // s.card = l},
    ‖p (n + s.1)‖₊ * r ^ s.1

theorem analyticShiftMajorant_summable (p : FormalMultilinearSeries ℝ E F)
    {r : ℝ≥0} (hr : (r + r : ℝ≥0∞) < p.radius) :
    Summable (fun n : ℕ => analyticShiftMajorant p r n * r ^ n) := by
  have hs := (NNReal.summable_sigma.1 (p.changeOriginSeries_summable_aux₁ hr)).2
  simpa only [analyticShiftMajorant, NNReal.tsum_mul_right] using hs

theorem changeOrigin_uniform_coefficient_bound (p : FormalMultilinearSeries ℝ E F)
    {r : ℝ≥0} (hr : (r + r : ℝ≥0∞) < p.radius)
    {h : E} (hh : ‖h‖₊ ≤ r) (n : ℕ) :
    ‖p.changeOrigin h n‖₊ * r ^ n ≤
      ∑' j : ℕ, analyticShiftMajorant p r j * r ^ j := by
  have hr' : (r : ℝ≥0∞) < p.radius :=
    (le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ r from zero_le _)).trans_lt hr
  have hh' : (‖h‖₊ : ℝ≥0∞) < p.radius :=
    (ENNReal.coe_le_coe.mpr hh).trans_lt hr'
  have hb : ‖p.changeOrigin h n‖₊ ≤ analyticShiftMajorant p r n := by
    refine (p.nnnorm_changeOrigin_le n hh').trans ?_
    exact (p.changeOriginSeries_summable_aux₂ hh' n).tsum_le_tsum
      (fun s => mul_le_mul_left' (pow_le_pow_left' hh s.1) _)
      (p.changeOriginSeries_summable_aux₂ hr' n)
  exact (mul_le_mul_right' hb _).trans
    ((analyticShiftMajorant_summable p hr).le_tsum' n)

theorem HasFPowerSeriesOnBall.norm_iteratedFDeriv_le_factorial
    {f : E → F} {p : FormalMultilinearSeries ℝ E F} {x : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (n.factorial : ℝ) * ‖p n‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [hf.iteratedFDeriv_eq_sum_of_completeSpace]
  calc
    ‖∑ σ : Equiv.Perm (Fin n), p n (fun i => v (σ i))‖ ≤
        ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i => v (σ i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Equiv.prod_comp] using (p n).le_opNorm (fun i => v (σ i))
    _ = ((n.factorial : ℝ) * ‖p n‖) * ∏ i, ‖v i‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]
      ring

theorem analyticAt_exists_uniform_iteratedFDeriv_bound
    {f : E → F} {x : E} (hf : AnalyticAt ℝ f x) :
    ∃ r M A : ℝ, 0 < r ∧ 0 < M ∧ 0 < A ∧
      ∀ (n : ℕ) (y : E), y ∈ ball x r →
        ‖iteratedFDeriv ℝ n f y‖ ≤ M * A ^ n * (n.factorial : ℝ) := by
  classical
  rcases hf with ⟨p, R, hp⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos with ⟨s, hs0, hsR⟩
  have hspos : 0 < s := ENNReal.coe_pos.1 hs0
  let r : ℝ≥0 := s / 3
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrrs : r + r < s := by dsimp [r]; nlinarith
  have hrr : (r + r : ℝ≥0∞) < p.radius := by
    have h : ((r + r : ℝ≥0) : ℝ≥0∞) < (s : ℝ≥0∞) :=
      ENNReal.coe_lt_coe.mpr hrrs
    exact (by simpa only [ENNReal.coe_add] using h).trans (hsR.trans_le hp.r_le)
  let M : ℝ≥0 := (∑' j : ℕ, analyticShiftMajorant p r j * r ^ j) + 1
  have hMpos : 0 < M := by dsimp [M]; positivity
  refine ⟨(r : ℝ), (M : ℝ), (r : ℝ)⁻¹, by exact_mod_cast hrpos,
    by exact_mod_cast hMpos, by positivity, ?_⟩
  intro n y hy
  have hy' : ‖y - x‖₊ ≤ r := by
    apply le_of_lt
    exact_mod_cast (show ‖y - x‖ < (r : ℝ) from by simpa only [mem_ball, dist_eq_norm] using hy)
  have hyr : (‖y - x‖₊ : ℝ≥0∞) < R := by
    have hrs : r < s := (lt_add_of_pos_right r hrpos).trans hrrs
    exact (ENNReal.coe_le_coe.mpr hy').trans_lt
      ((ENNReal.coe_lt_coe.mpr hrs).trans hsR)
  have hpy : HasFPowerSeriesOnBall f (p.changeOrigin (y - x)) y
      (R - (‖y - x‖₊ : ℝ≥0∞)) := by
    simpa only [add_sub_cancel] using hp.changeOrigin hyr
  have hprod : ‖p.changeOrigin (y - x) n‖₊ * r ^ n ≤ M :=
    (changeOrigin_uniform_coefficient_bound p hrr hy' n).trans (by
      dsimp [M]
      exact le_add_of_nonneg_right zero_le_one)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have hb : ‖p.changeOrigin (y - x) n‖ ≤ (M : ℝ) / (r : ℝ) ^ n := by
    apply (le_div_iff₀ (pow_pos hrR n)).mpr
    exact_mod_cast hprod
  calc
    ‖iteratedFDeriv ℝ n f y‖ ≤ (n.factorial : ℝ) * ‖p.changeOrigin (y - x) n‖ :=
      hpy.norm_iteratedFDeriv_le_factorial n
    _ ≤ (n.factorial : ℝ) * ((M : ℝ) / (r : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (M : ℝ) * ((r : ℝ)⁻¹) ^ n * (n.factorial : ℝ) := by
      rw [div_eq_mul_inv, inv_pow]
      ring

theorem analyticOnNhd_compact_uniform_iteratedFDeriv_bound
    {f : E → F} {K : Set E} (hK : IsCompact K) (hf : AnalyticOnNhd ℝ f K) :
    ∃ M A : ℝ, 0 < M ∧ 0 < A ∧ ∀ (n : ℕ) (y : E), y ∈ K →
      ‖iteratedFDeriv ℝ n f y‖ ≤ M * A ^ n * (n.factorial : ℝ) := by
  classical
  have hlocal : ∀ x : K, ∃ r M A : ℝ, 0 < r ∧ 0 < M ∧ 0 < A ∧
      ∀ (n : ℕ) (y : E), y ∈ ball (x : E) r →
        ‖iteratedFDeriv ℝ n f y‖ ≤ M * A ^ n * (n.factorial : ℝ) :=
    fun x => analyticAt_exists_uniform_iteratedFDeriv_bound (hf x x.property)
  choose r M A hr hM hA hb using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : E) (r x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  let M' : ℝ := 1 + ∑ x ∈ s, M x
  let A' : ℝ := 1 + ∑ x ∈ s, A x
  have hMsum : 0 ≤ ∑ x ∈ s, M x := Finset.sum_nonneg (fun x _ => (hM x).le)
  have hAsum : 0 ≤ ∑ x ∈ s, A x := Finset.sum_nonneg (fun x _ => (hA x).le)
  refine ⟨M', A', by dsimp [M']; linarith, by dsimp [A']; linarith, ?_⟩
  intro n y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (hs hy)
  have hMx : M x ≤ M' := by
    have h := Finset.single_le_sum (fun i _ => (hM i).le) hx
    dsimp [M']
    linarith
  have hAx : A x ≤ A' := by
    have h := Finset.single_le_sum (fun i _ => (hA i).le) hx
    dsimp [A']
    linarith
  exact (hb x n y hxy).trans (by gcongr)

end
end NSEGR.Assembly
