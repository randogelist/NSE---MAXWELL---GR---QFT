import QuantumAdapter.Assembly.Flow
import QuantumAdapter.Assembly.Fourier
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Finite-time continuation edges for the native drift

These statements concern arbitrary local solutions of the actual native ODE.
They do not assume a PhaseFlow record. A bounded local solution has limits at
both finite endpoints. Dissipation supplies the bound at a forward endpoint.
Construction of a maximal compatible family and its final gluing are separate.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter Metric
open scoped BigOperators ContDiff Topology NNReal

namespace QuantumAdapter.Assembly

noncomputable section

open SingularClosure

/-- The coefficient energy identity is local and does not require a flow record. -/
theorem energy0_hasDerivAt_of_drift {ν : ℝ} {N : ℕ}
    {q : ℝ → Phase N} {t : ℝ}
    (hq : HasDerivAt q (drift ν N (q t)) t) :
    HasDerivAt (fun s => energy0 N (q s))
      ((-2 * ν) * dissipation N (q t)) t := by
  have hc (k : Frequency) (i : Fin 3) :
      HasDerivAt (fun s => phaseCoeff (q s) k i)
        (phaseCoeff (drift ν N (q t)) k i) t := by
    simpa only [Function.comp_def, phaseCoordinate_apply] using
      (phaseCoordinate N k i).hasFDerivAt.comp_hasDerivAt t hq
  rw [← rawRhs_energy_rate ν N (q t)]
  unfold energy0
  apply HasDerivAt.fun_sum
  intro k hk
  apply HasDerivAt.fun_sum
  intro i hi
  have h := hasDerivWithinAt_complex_normSq
    ((hc k i).hasDerivWithinAt (s := (univ : Set ℝ)))
  simpa only [phaseCoeff, drift_eq_rawRhs] using
    h.hasDerivAt (by simp)

/-- Actual local solutions have decreasing energy on their entire interval. -/
theorem local_energy0_antitoneOn {ν : ℝ} (hν : 0 ≤ ν) {N : ℕ}
    {q : ℝ → Phase N} {a b : ℝ}
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t) :
    AntitoneOn (fun t => energy0 N (q t)) (Ioo a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo a b)
    (f' := fun t => (-2 * ν) * dissipation N (q t))
  · intro t ht
    exact (energy0_hasDerivAt_of_drift (hq t ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (energy0_hasDerivAt_of_drift (hq t (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hν) (dissipation_nonneg N (q t))

/-- A local integrating factor controls the backward energy growth. -/
theorem local_weighted_energy0_monotoneOn {ν : ℝ} (hν : 0 ≤ ν) {N : ℕ}
    {q : ℝ → Phase N} {a b : ℝ}
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t) :
    MonotoneOn (fun t => Real.exp ((2 * ν * finiteLaplaceTrace N) * t) *
      energy0 N (q t)) (Ioo a b) := by
  let d : ℝ := 2 * ν * finiteLaplaceTrace N
  have hd (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s => Real.exp (d * s) * energy0 N (q s))
        (Real.exp (d * t) * (d * energy0 N (q t) - 2 * ν * dissipation N (q t))) t := by
    have hexp := (hasDerivAt_const_mul (x := t) d).exp
    have hp := hexp.fun_mul (energy0_hasDerivAt_of_drift (hq t ht))
    have hs : (Real.exp (d * t) * d) * energy0 N (q t) +
        Real.exp (d * t) * ((-2 * ν) * dissipation N (q t)) =
        Real.exp (d * t) * (d * energy0 N (q t) - 2 * ν * dissipation N (q t)) := by
      ring
    rw [hs] at hp
    exact hp
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo a b)
    (f' := fun t => Real.exp (d * t) *
      (d * energy0 N (q t) - 2 * ν * dissipation N (q t)))
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hd t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    apply mul_nonneg (Real.exp_nonneg _)
    have hb := mul_le_mul_of_nonneg_left
      (dissipation_le_finiteLaplaceTrace_mul_energy0 N (q t))
      (show 0 ≤ 2 * ν by positivity)
    dsimp [d]
    nlinarith

/-- The actual vector field is bounded on every phase ball. -/
theorem drift_bounded_on_closedBall (ν : ℝ) (N : ℕ) (R : ℝ) :
    ∃ C : ℝ≥0, ∀ x ∈ closedBall (0 : Phase N) R, ‖drift ν N x‖₊ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Phase N) R).exists_bound_of_continuousOn
    (contDiff_drift ν N).continuous.continuousOn
  refine ⟨⟨max C 0, le_max_right C 0⟩, ?_⟩
  intro x hx
  have h : ‖drift ν N x‖ ≤ max C 0 := (hC x hx).trans (le_max_left C 0)
  exact_mod_cast h

/-- A local native solution with bounded phase norm is uniformly Lipschitz. -/
theorem local_drift_solution_lipschitz_of_norm_bound (ν : ℝ) (N : ℕ)
    {q : ℝ → Phase N} {a b R : ℝ}
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t)
    (hb : ∀ t ∈ Ioo a b, ‖q t‖ ≤ R) :
    ∃ C : ℝ≥0, LipschitzOnWith C q (Ioo a b) := by
  obtain ⟨C, hC⟩ := drift_bounded_on_closedBall ν N R
  refine ⟨C, (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (hq t ht).hasDerivWithinAt) ?_⟩
  intro t ht
  exact hC (q t) (by simpa only [mem_closedBall, dist_zero_right] using hb t ht)

/-- Bounded native local solutions have actual limits at both finite endpoints. -/
theorem local_drift_solution_endpoint_limits_of_norm_bound (ν : ℝ) (N : ℕ)
    {q : ℝ → Phase N} {a b R : ℝ} (hab : a < b)
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t)
    (hb : ∀ t ∈ Ioo a b, ‖q t‖ ≤ R) :
    (∃ x : Phase N, Tendsto q (𝓝[>] a) (𝓝 x)) ∧
      (∃ y : Phase N, Tendsto q (𝓝[<] b) (𝓝 y)) := by
  obtain ⟨C, hC⟩ := local_drift_solution_lipschitz_of_norm_bound ν N hq hb
  have hleft : Cauchy (𝓝[>] a) := cauchy_nhds.mono nhdsWithin_le_nhds
  have hright : Cauchy (𝓝[<] b) := cauchy_nhds.mono nhdsWithin_le_nhds
  constructor
  · apply cauchy_map_iff_exists_tendsto.mp
    exact hleft.map_of_le hC.uniformContinuousOn
      (le_principal_iff.mpr (Ioo_mem_nhdsGT hab))
  · apply cauchy_map_iff_exists_tendsto.mp
    exact hright.map_of_le hC.uniformContinuousOn
      (le_principal_iff.mpr (Ioo_mem_nhdsLT hab))

/-- Coercivity turns a local energy bound into both finite endpoint limits. -/
theorem local_drift_solution_endpoint_limits_of_energy_bound (ν : ℝ) (N : ℕ)
    {q : ℝ → Phase N} {a b C : ℝ} (hab : a < b)
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t)
    (hb : ∀ t ∈ Ioo a b, energy0 N (q t) ≤ C) :
    (∃ x : Phase N, Tendsto q (𝓝[>] a) (𝓝 x)) ∧
      (∃ y : Phase N, Tendsto q (𝓝[<] b) (𝓝 y)) := by
  apply local_drift_solution_endpoint_limits_of_norm_bound ν N hab hq
    (R := Real.sqrt C)
  intro t ht
  have h := Real.sqrt_le_sqrt (hb t ht)
  simpa only [energy0_eq_norm_sq, Real.sqrt_sq (norm_nonneg (q t))] using h

/-- Dissipation excludes escape at any finite forward endpoint, with no supplied bound. -/
theorem local_drift_solution_has_forward_limit {ν : ℝ} (hν : 0 ≤ ν)
    (N : ℕ) {q : ℝ → Phase N} {a b : ℝ} (hab : a < b)
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t) :
    ∃ x : Phase N, Tendsto q (𝓝[<] b) (𝓝 x) := by
  let c : ℝ := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hct : c ∈ Ioo a b := ⟨hac, hcb⟩
  have henergy : ∀ t ∈ Ioo c b, energy0 N (q t) ≤ energy0 N (q c) := by
    intro t ht
    exact local_energy0_antitoneOn hν hq hct ⟨hac.trans ht.1, ht.2⟩ ht.1.le
  exact (local_drift_solution_endpoint_limits_of_energy_bound ν N hcb
    (fun t ht => hq t ⟨hac.trans ht.1, ht.2⟩) henergy).2

/-- The cutoff-dependent integrating factor excludes finite backward escape. -/
theorem local_drift_solution_has_backward_limit {ν : ℝ} (hν : 0 ≤ ν)
    (N : ℕ) {q : ℝ → Phase N} {a b : ℝ} (hab : a < b)
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t) :
    ∃ x : Phase N, Tendsto q (𝓝[>] a) (𝓝 x) := by
  let c : ℝ := (a + b) / 2
  let d : ℝ := 2 * ν * finiteLaplaceTrace N
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hd : 0 ≤ d := by
    dsimp [d]
    exact mul_nonneg (mul_nonneg (by norm_num) hν) (finiteLaplaceTrace_nonneg N)
  have hct : c ∈ Ioo a b := ⟨hac, hcb⟩
  let C : ℝ := Real.exp (-(d * a)) * (Real.exp (d * c) * energy0 N (q c))
  have henergy : ∀ t ∈ Ioo a c, energy0 N (q t) ≤ C := by
    intro t ht
    have h := local_weighted_energy0_monotoneOn hν hq
      ⟨ht.1, ht.2.trans hcb⟩ hct ht.2.le
    change Real.exp (d * t) * energy0 N (q t) ≤
      Real.exp (d * c) * energy0 N (q c) at h
    have hm := mul_le_mul_of_nonneg_left h (Real.exp_nonneg (-(d * t)))
    have hE : energy0 N (q t) ≤
        Real.exp (-(d * t)) * (Real.exp (d * c) * energy0 N (q c)) := by
      simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, one_mul] using hm
    have he : Real.exp (-(d * t)) ≤ Real.exp (-(d * a)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact hE.trans (mul_le_mul_of_nonneg_right he
      (mul_nonneg (Real.exp_nonneg _) (energy0_nonneg N (q c))))
  exact (local_drift_solution_endpoint_limits_of_energy_bound ν N hac
    (fun t ht => hq t ⟨ht.1, ht.2.trans hcb⟩) henergy).1

/-- Native local existence has a uniform time radius near each phase point. -/
theorem exists_uniform_local_drift_solutions (ν : ℝ) (N : ℕ) (x₀ : Phase N) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ (t₀ : ℝ) (x : Phase N),
      x ∈ closedBall x₀ r →
      ∃ q : ℝ → Phase N, q t₀ = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt q (drift ν N (q t)) t := by
  have hd : ContDiff ℝ 1 (drift ν N) := (contDiff_drift ν N).of_le (by simp)
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ :=
    IsPicardLindelof.of_contDiffAt_one hd.contDiffAt
  refine ⟨r, hr, ε, hε, ?_⟩
  intro t₀ x hx
  obtain ⟨q, hq₀, hq⟩ := (hPL t₀).exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨q, hq₀, ?_⟩
  intro t ht
  exact (hq t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- At every finite forward endpoint the native ODE can be restarted at its limit. -/
theorem local_drift_solution_forward_limit_restart {ν : ℝ} (hν : 0 ≤ ν)
    (N : ℕ) {q : ℝ → Phase N} {a b : ℝ} (hab : a < b)
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t) :
    ∃ x : Phase N, Tendsto q (𝓝[<] b) (𝓝 x) ∧
      ∃ p : ℝ → Phase N, p b = x ∧ ∃ ε > (0 : ℝ),
        ∀ t ∈ Ioo (b - ε) (b + ε),
          HasDerivAt p (drift ν N (p t)) t := by
  obtain ⟨x, hx⟩ := local_drift_solution_has_forward_limit hν N hab hq
  exact ⟨x, hx, exists_local_drift_solution ν N x b⟩

end

end QuantumAdapter.Assembly

