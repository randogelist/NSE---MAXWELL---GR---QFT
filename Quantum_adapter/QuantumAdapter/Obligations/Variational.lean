import QuantumAdapter.Assembly.FlowDependence
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.ODE.Gronwall

/-!
Quantitative edges for initial-data differentiation of the native flow.
The remainder theorem constructs a Frechet derivative from a genuine
variational curve and a quadratic vector-field remainder. It does not
assert existence of the variational curve by means of an axiom.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter Metric
open scoped Topology ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local quadratic remainder gives the exact Frechet derivative. -/
theorem hasFDerivAt_of_quadratic_remainder
    (f : E → E) (x : E) (J : E →L[ℝ] E) (C : ℝ)
    (hrem : ∀ᶠ h in 𝓝 (0 : E),
      ‖f (x + h) - f x - J h‖ ≤ C * ‖h‖ ^ 2) :
    HasFDerivAt f J x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hd : 0 < ε / (|C| + 1) := div_pos hε (by positivity)
  filter_upwards [hrem, ball_mem_nhds (0 : E) hd] with h hh hball
  have hsmall : ‖h‖ < ε / (|C| + 1) := by
    simpa only [mem_ball, dist_zero_right] using hball
  have hmul : ‖h‖ * (|C| + 1) < ε :=
    (lt_div_iff₀ (by positivity : 0 < |C| + 1)).mp hsmall
  have hn : 0 ≤ ‖h‖ := norm_nonneg h
  calc
    ‖f (x + h) - f x - J h‖ ≤ C * ‖h‖ ^ 2 := hh
    _ ≤ |C| * ‖h‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
    _ ≤ ε * ‖h‖ := by
      have hp := mul_le_mul_of_nonneg_right hmul.le hn
      nlinarith [sq_nonneg ‖h‖]

/-- The scalar Gronwall majorant is linear in a zero-initial-data source. -/
theorem gronwallBound_zero_source_mul (K ε c t : ℝ) :
    gronwallBound 0 K (ε * c) t = gronwallBound 0 K ε t * c := by
  unfold gronwallBound
  split_ifs <;> ring

/-- The derivative of a continuous-linear-map valued curve can be evaluated. -/
theorem hasDerivAt_variational_apply
    {J : ℝ → E →L[ℝ] E} {A : E →L[ℝ] E} {t : ℝ}
    (hJ : HasDerivAt J (A.comp (J t)) t) (h : E) :
    HasDerivAt (fun s => J s h) (A (J t h)) t := by
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.comp_apply] using
    (ContinuousLinearMap.apply ℝ E h).hasFDerivAt.comp_hasDerivAt t hJ

/-- Exact remainder ODE, before estimating any term. -/
theorem hasDerivAt_flow_variational_remainder
    (b : E → E) (Φ : ℝ → E → E) (J : ℝ → E →L[ℝ] E)
    (A : ℝ → E →L[ℝ] E) (x y : E) (t : ℝ)
    (hx : HasDerivAt (fun s => Φ s x) (b (Φ t x)) t)
    (hy : HasDerivAt (fun s => Φ s y) (b (Φ t y)) t)
    (hJ : HasDerivAt J ((A t).comp (J t)) t) :
    HasDerivAt (fun s => Φ s y - Φ s x - J s (y - x))
      (b (Φ t y) - b (Φ t x) - A t (J t (y - x))) t :=
  (hy.sub hx).sub (hasDerivAt_variational_apply hJ (y - x))

/-- Quantitative quadratic flow remainder from the actual variational ODE. -/
theorem flow_variational_remainder_bound
    (b : E → E) (Φ : ℝ → E → E) (J : ℝ → E →L[ℝ] E)
    (A : ℝ → E →L[ℝ] E) (x y : E) {T K C L : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hzero : ∀ z, Φ 0 z = z)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hΦ : ∀ z s, HasDerivAt (fun t => Φ t z) (b (Φ s z)) s)
    (hJ : ∀ s, HasDerivAt J ((A s).comp (J s)) s)
    (hA : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    (hclose : ∀ s ∈ Icc 0 T, ‖Φ s y - Φ s x‖ ≤ L * ‖y - x‖)
    (hquad : ∀ s ∈ Icc 0 T,
      ‖b (Φ s y) - b (Φ s x) - A s (Φ s y - Φ s x)‖ ≤
        C * ‖Φ s y - Φ s x‖ ^ 2) :
    ‖Φ T y - Φ T x - J T (y - x)‖ ≤
      gronwallBound 0 K (C * L ^ 2) T * ‖y - x‖ ^ 2 := by
  let R : ℝ → E := fun s => Φ s y - Φ s x - J s (y - x)
  let R' : ℝ → E := fun s => b (Φ s y) - b (Φ s x) - A s (J s (y - x))
  have hd (s : ℝ) : HasDerivAt R (R' s) s :=
    hasDerivAt_flow_variational_remainder b Φ J A x y s (hΦ x s) (hΦ y s) (hJ s)
  have hRzero : R 0 = 0 := by simp [R, hzero, hJzero]
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      ‖R' s‖ ≤ K * ‖R s‖ + (C * L ^ 2) * ‖y - x‖ ^ 2 := by
    have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
    have heq : R' s =
        (b (Φ s y) - b (Φ s x) - A s (Φ s y - Φ s x)) + A s (R s) := by
      simp only [R', R, map_sub]
      abel
    have hsq : ‖Φ s y - Φ s x‖ ^ 2 ≤ (L * ‖y - x‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).2 (hclose s hs')
    calc
      ‖R' s‖ = ‖(b (Φ s y) - b (Φ s x) - A s (Φ s y - Φ s x)) + A s (R s)‖ :=
        congrArg norm heq
      _ ≤ ‖b (Φ s y) - b (Φ s x) - A s (Φ s y - Φ s x)‖ + ‖A s (R s)‖ :=
        norm_add_le _ _
      _ ≤ C * ‖Φ s y - Φ s x‖ ^ 2 + ‖A s‖ * ‖R s‖ :=
        add_le_add (hquad s hs') ((A s).le_opNorm (R s))
      _ ≤ C * (L * ‖y - x‖) ^ 2 + K * ‖R s‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hsq hC)
          (mul_le_mul_of_nonneg_right (hA s hs') (norm_nonneg _))
      _ = K * ‖R s‖ + (C * L ^ 2) * ‖y - x‖ ^ 2 := by ring
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (a := 0) (b := T) (δ := 0)
    (K := K) (ε := (C * L ^ 2) * ‖y - x‖ ^ 2)
    ((continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn)
    (fun s _ => (hd s).hasDerivWithinAt)
    (by simp [hRzero]) hb T ⟨hT, le_rfl⟩
  simpa only [R, sub_zero, gronwallBound_zero_source_mul] using hgr

/-- A variational solution and uniform local Taylor control imply a flow derivative. -/
theorem flow_hasFDerivAt_of_variational_remainder
    (b : E → E) (Φ : ℝ → E → E) (J : ℝ → E →L[ℝ] E)
    (A : ℝ → E →L[ℝ] E) (x : E) {T K C L : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hzero : ∀ z, Φ 0 z = z)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hΦ : ∀ z s, HasDerivAt (fun t => Φ t z) (b (Φ s z)) s)
    (hJ : ∀ s, HasDerivAt J ((A s).comp (J s)) s)
    (hA : ∀ s ∈ Icc 0 T, ‖A s‖ ≤ K)
    (hlocal : ∀ᶠ h in 𝓝 (0 : E),
      (∀ s ∈ Icc 0 T, ‖Φ s (x + h) - Φ s x‖ ≤ L * ‖h‖) ∧
      (∀ s ∈ Icc 0 T,
        ‖b (Φ s (x + h)) - b (Φ s x) - A s (Φ s (x + h) - Φ s x)‖ ≤
          C * ‖Φ s (x + h) - Φ s x‖ ^ 2)) :
    HasFDerivAt (Φ T) (J T) x := by
  apply hasFDerivAt_of_quadratic_remainder (Φ T) x (J T)
    (gronwallBound 0 K (C * L ^ 2) T)
  filter_upwards [hlocal] with h hh
  have hb := flow_variational_remainder_bound b Φ J A x (x + h)
    hT hC hL hzero hJzero hΦ hJ hA
    (by simpa only [add_sub_cancel_left] using hh.1) hh.2
  simpa only [add_sub_cancel_left] using hb

/-- The actual drift derivative along a native orbit is continuous. -/
theorem continuous_native_variational_coefficient
    {ν : ℝ} (F : PhaseFlow ν) (N : ℕ) (q : Phase N) :
    Continuous (fun t => fderiv ℝ (drift ν N) (F.map N t q)) := by
  apply ((Assembly.contDiff_drift ν N).continuous_fderiv (by simp)).comp
  exact continuous_iff_continuousAt.mpr (fun t => (F.orbit_derivative N q t).continuousAt)

/-- Every finite native orbit segment has a finite variational-coefficient bound. -/
theorem native_variational_coefficient_bounded
    {ν : ℝ} (F : PhaseFlow ν) (N : ℕ) (q : Phase N) (a b : ℝ) :
    ∃ K : ℝ, ∀ t ∈ Icc a b, ‖fderiv ℝ (drift ν N) (F.map N t q)‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn
    (f := fun t : ℝ => fderiv ℝ (drift ν N) (F.map N t q))
    (continuous_native_variational_coefficient F N q).continuousOn
  exact ⟨K, hK⟩

/-- The initial native time map has the identity derivative. -/
theorem phaseFlow_zero_hasFDerivAt
    {ν : ℝ} (F : PhaseFlow ν) (N : ℕ) (q : Phase N) :
    HasFDerivAt (F.map N 0) (ContinuousLinearMap.id ℝ (Phase N)) q := by
  have heq : F.map N 0 = id := funext (F.map_zero N)
  rw [heq]
  exact hasFDerivAt_id q

end
end QuantumAdapter.Obligations
