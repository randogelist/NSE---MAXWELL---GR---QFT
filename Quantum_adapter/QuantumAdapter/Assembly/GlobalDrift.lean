import QuantumAdapter.Assembly.CompleteFlow
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option autoImplicit false
set_option Elab.async true

open Set Filter Metric
open scoped BigOperators ContDiff Topology NNReal

namespace QuantumAdapter.Assembly

noncomputable section

/-- Native local solutions agreeing initially agree on their entire common interval. -/
theorem local_drift_solutions_unique (ν : ℝ) (N : ℕ)
    {q r : ℝ → Phase N} {a b t₀ : ℝ}
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t)
    (hr : ∀ t ∈ Ioo a b, HasDerivAt r (drift ν N (r t)) t)
    (ht₀ : t₀ ∈ Ioo a b) (h₀ : q t₀ = r t₀) : EqOn q r (Ioo a b) := by
  intro t ht
  let l : ℝ := min t₀ t
  let u : ℝ := max t₀ t
  have hdom : Icc l u ⊆ Ioo a b := by
    intro s hs
    have hl : a < l := lt_min ht₀.1 ht.1
    have hu : u < b := max_lt ht₀.2 ht.2
    exact ⟨hl.trans_le hs.1, hs.2.trans_lt hu⟩
  have hqc : ContinuousOn q (Icc l u) :=
    HasDerivAt.continuousOn (fun s hs => hq s (hdom hs))
  have hrc : ContinuousOn r (Icc l u) :=
    HasDerivAt.continuousOn (fun s hs => hr s (hdom hs))
  obtain ⟨Cq, hCq⟩ := isCompact_Icc.exists_bound_of_continuousOn hqc
  obtain ⟨Cr, hCr⟩ := isCompact_Icc.exists_bound_of_continuousOn hrc
  let R : ℝ := max Cq Cr
  have hd : ContDiff ℝ 1 (drift ν N) := (contDiff_drift ν N).of_le (by simp)
  obtain ⟨K, hK⟩ := hd.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : Phase N) R) (isCompact_closedBall (0 : Phase N) R)
  have hbq (s : ℝ) (hs : s ∈ Icc l u) : q s ∈ closedBall (0 : Phase N) R := by
    simp only [mem_closedBall, dist_zero_right]
    exact (hCq s hs).trans (le_max_left Cq Cr)
  have hbr (s : ℝ) (hs : s ∈ Icc l u) : r s ∈ closedBall (0 : Phase N) R := by
    simp only [mem_closedBall, dist_zero_right]
    exact (hCr s hs).trans (le_max_right Cq Cr)
  rcases le_total t₀ t with hle | hle
  · have hlu : l = t₀ ∧ u = t := ⟨min_eq_left hle, max_eq_right hle⟩
    have heq := ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => drift ν N) (s := fun _ => closedBall (0 : Phase N) R)
      (a := l) (b := u) (K := K) (fun _ _ => hK) hqc
      (fun s hs => (hq s (hdom (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun s hs => hbq s (Ico_subset_Icc_self hs)) hrc
      (fun s hs => (hr s (hdom (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun s hs => hbr s (Ico_subset_Icc_self hs)) (by simpa only [hlu.1] using h₀)
    exact heq (by rw [hlu.1, hlu.2]; exact ⟨hle, le_rfl⟩)
  · have hlu : l = t ∧ u = t₀ := ⟨min_eq_right hle, max_eq_left hle⟩
    have heq := ODE_solution_unique_of_mem_Icc_left
      (v := fun _ => drift ν N) (s := fun _ => closedBall (0 : Phase N) R)
      (a := l) (b := u) (K := K) (fun _ _ => hK) hqc
      (fun s hs => (hq s (hdom (Ioc_subset_Icc_self hs))).hasDerivWithinAt)
      (fun s hs => hbq s (Ioc_subset_Icc_self hs)) hrc
      (fun s hs => (hr s (hdom (Ioc_subset_Icc_self hs))).hasDerivWithinAt)
      (fun s hs => hbr s (Ioc_subset_Icc_self hs)) (by simpa only [hlu.2] using h₀)
    exact heq (by rw [hlu.1, hlu.2]; exact ⟨le_rfl, hle⟩)

/-- Actual local ODE solutions glue on overlapping open intervals. -/
theorem local_drift_solutions_piecewise (ν : ℝ) (N : ℕ)
    {q r : ℝ → Phase N} {a b c d t₀ : ℝ}
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (drift ν N (q t)) t)
    (hr : ∀ t ∈ Ioo c d, HasDerivAt r (drift ν N (r t)) t)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d) (h₀ : q t₀ = r t₀) :
    ∀ t ∈ Ioo a b ∪ Ioo c d,
      HasDerivAt (piecewise (Ioo a b) q r)
        (drift ν N (piecewise (Ioo a b) q r t)) t := by
  classical
  have heq : EqOn q r (Ioo (max a c) (min b d)) :=
    local_drift_solutions_unique ν N
      (fun t ht => hq t ⟨(le_max_left a c).trans_lt ht.1,
        ht.2.trans_le (min_le_left b d)⟩)
      (fun t ht => hr t ⟨(le_max_right a c).trans_lt ht.1,
        ht.2.trans_le (min_le_right b d)⟩)
      ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩ h₀
  have hright : EqOn (piecewise (Ioo a b) q r) r (Ioo c d) := by
    intro t ht
    by_cases hleft : t ∈ Ioo a b
    · rw [piecewise, if_pos hleft]
      exact heq ⟨max_lt hleft.1 ht.1, lt_min hleft.2 ht.2⟩
    · rw [piecewise, if_neg hleft]
  intro t ht
  by_cases hleft : t ∈ Ioo a b
  · have hnear : piecewise (Ioo a b) q r =ᶠ[𝓝 t] q := by
      filter_upwards [Ioo_mem_nhds hleft.1 hleft.2] with s hs
      simp only [piecewise, if_pos hs]
    have hd := (hq t hleft).congr_of_eventuallyEq hnear
    rw [← hnear.eq_of_nhds] at hd
    exact hd
  · have htr : t ∈ Ioo c d := ht.resolve_left hleft
    have hnear : piecewise (Ioo a b) q r =ᶠ[𝓝 t] r := by
      filter_upwards [Ioo_mem_nhds htr.1 htr.2] with s hs
      exact hright hs
    have hd := (hr t htr).congr_of_eventuallyEq hnear
    rw [← hnear.eq_of_nhds] at hd
    exact hd

/-- Signed-time energy control applies before a complete flow has been constructed. -/
theorem local_drift_energy0_bound_abs {ν : ℝ} (hν : 0 ≤ ν) (N : ℕ)
    {q : ℝ → Phase N} {a : ℝ} (ha : 0 < a)
    (hq : ∀ t ∈ Ioo (-a) a, HasDerivAt q (drift ν N (q t)) t)
    {t : ℝ} (ht : t ∈ Ioo (-a) a) :
    energy0 N (q t) ≤ Real.exp ((2 * ν * finiteLaplaceTrace N) * |t|) * energy0 N (q 0) := by
  have hzero : (0 : ℝ) ∈ Ioo (-a) a := ⟨neg_lt_zero.mpr ha, ha⟩
  rcases le_total 0 t with h0t | ht0
  · have he := local_energy0_antitoneOn hν hq hzero ht h0t
    have he1 : 1 ≤ Real.exp ((2 * ν * finiteLaplaceTrace N) * |t|) :=
      Real.one_le_exp_iff.mpr (by
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hν) (finiteLaplaceTrace_nonneg N))
          (abs_nonneg t))
    exact he.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right he1 (energy0_nonneg N (q 0)))
  · have he := local_weighted_energy0_monotoneOn hν hq ht hzero ht0
    simp only [mul_zero, Real.exp_zero, one_mul] at he
    have hm := mul_le_mul_of_nonneg_left he
      (Real.exp_nonneg (-((2 * ν * finiteLaplaceTrace N) * t)))
    simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_mul, abs_of_nonpos ht0, mul_neg] using hm

/-- One positive existence time works for every initial phase in a fixed bounded ball. -/
theorem exists_uniform_local_drift_solutions_on_ball (ν : ℝ) (N : ℕ) (R : ℝ≥0) :
    ∃ ε > (0 : ℝ), ∀ (t₀ : ℝ) (x : Phase N),
      x ∈ closedBall (0 : Phase N) R →
      ∃ q : ℝ → Phase N, q t₀ = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt q (drift ν N (q t)) t := by
  have hd : ContDiff ℝ 1 (drift ν N) := (contDiff_drift ν N).of_le (by simp)
  obtain ⟨K, hK⟩ := hd.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : Phase N) ((R : ℝ) + 1))
    (isCompact_closedBall (0 : Phase N) ((R : ℝ) + 1))
  obtain ⟨L, hL⟩ := drift_bounded_on_closedBall ν N ((R : ℝ) + 1)
  let ε : ℝ := 1 / ((L : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, ?_⟩
  intro t₀ x hx
  have hPL : IsPicardLindelof (fun _ => drift ν N)
      (tmin := t₀ - ε) (tmax := t₀ + ε)
      ⟨t₀, by simp [hε.le]⟩ (0 : Phase N) (R + 1) R L K := by
    apply IsPicardLindelof.of_time_independent
    · intro z hz
      have hn := hL z hz
      exact_mod_cast hn
    · exact hK
    · simp only [add_sub_cancel_left, sub_sub_cancel, max_self,
        NNReal.coe_add, NNReal.coe_one]
      have hm : (L : ℝ) * ε ≤ 1 := by
        dsimp [ε]
        rw [mul_one_div, div_le_one (by positivity : (0 : ℝ) < L + 1)]
        linarith
      linarith
  obtain ⟨q, hq₀, hq⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨q, hq₀, ?_⟩
  intro t ht
  exact (hq t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

set_option maxHeartbeats 1000000 in
/-- The native ODE has a solution on every prescribed finite symmetric interval. -/
theorem exists_drift_solution_on_arbitrary_interval {ν : ℝ} (hν : 0 ≤ ν)
    (N : ℕ) (q₀ : Phase N) (T : ℝ) :
    ∃ q : ℝ → Phase N, q 0 = q₀ ∧
      ∀ t ∈ Ioo (-T) T, HasDerivAt q (drift ν N (q t)) t := by
  classical
  let S : Set ℝ := {a | ∃ q : ℝ → Phase N, q 0 = q₀ ∧
    ∀ t ∈ Ioo (-a) a, HasDerivAt q (drift ν N (q t)) t}
  obtain ⟨qinit, hinit, ε₀, hε₀, hqinit⟩ := exists_local_drift_solution ν N q₀ 0
  have hinitS : ε₀ ∈ S := ⟨qinit, hinit, by simpa only [zero_sub, zero_add] using hqinit⟩
  have hne : S.Nonempty := ⟨ε₀, hinitS⟩
  suffices hunbdd : ¬ BddAbove S by
    obtain ⟨a, ⟨q, hq₀, hq⟩, hTa⟩ := not_bddAbove_iff.mp hunbdd T
    refine ⟨q, hq₀, fun t ht => hq t ?_⟩
    exact ⟨(neg_lt_neg hTa).trans ht.1, ht.2.trans hTa⟩
  intro hbdd
  let A : ℝ := sSup S
  have hA₀ : 0 < A := hε₀.trans_le (le_csSup hbdd hinitS)
  let d : ℝ := 2 * ν * finiteLaplaceTrace N
  have hd : 0 ≤ d :=
    mul_nonneg (mul_nonneg (by norm_num) hν) (finiteLaplaceTrace_nonneg N)
  let R : ℝ≥0 := ⟨Real.sqrt (Real.exp (d * A) * energy0 N q₀), Real.sqrt_nonneg _⟩
  have hq₀ball : q₀ ∈ closedBall (0 : Phase N) R := by
    have hexp : 1 ≤ Real.exp (d * A) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hd hA₀.le)
    have hE : energy0 N q₀ ≤ Real.exp (d * A) * energy0 N q₀ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp (energy0_nonneg N q₀)
    have hn := Real.sqrt_le_sqrt hE
    simp only [mem_closedBall, dist_zero_right]
    change ‖q₀‖ ≤ Real.sqrt (Real.exp (d * A) * energy0 N q₀)
    simpa only [energy0_eq_norm_sq, Real.sqrt_sq (norm_nonneg q₀)] using hn
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_local_drift_solutions_on_ball ν N R
  have hεS : ε ∈ S := by
    obtain ⟨p, hp₀, hp⟩ := hlocal 0 q₀ hq₀ball
    exact ⟨p, hp₀, by simpa only [zero_sub, zero_add] using hp⟩
  have hεA : ε ≤ A := le_csSup hbdd hεS
  obtain ⟨a, haS, hnear⟩ := Real.add_neg_lt_sSup hne (ε := -(ε / 2)) (by linarith)
  have hnear' : A - ε / 2 < a := by simpa only [sub_eq_add_neg] using hnear
  obtain ⟨q, hq₀, hq⟩ := haS
  let τ : ℝ := A - ε / 2
  have hτ₀ : 0 < τ := by dsimp [τ]; linarith
  have hτa : τ < a := hnear'
  have ha₀ : 0 < a := hτ₀.trans hτa
  have hτA : τ ≤ A := by dsimp [τ]; linarith
  have hbound (s : ℝ) (hs : s ∈ Ioo (-a) a) (hsA : |s| ≤ A) :
      q s ∈ closedBall (0 : Phase N) R := by
    have hE := local_drift_energy0_bound_abs hν N ha₀ hq hs
    rw [hq₀] at hE
    have he : Real.exp (d * |s|) ≤ Real.exp (d * A) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsA hd)
    have hE' : energy0 N (q s) ≤ Real.exp (d * A) * energy0 N q₀ :=
      hE.trans (mul_le_mul_of_nonneg_right he (energy0_nonneg N q₀))
    have hn := Real.sqrt_le_sqrt hE'
    simp only [mem_closedBall, dist_zero_right]
    change ‖q s‖ ≤ Real.sqrt (Real.exp (d * A) * energy0 N q₀)
    simpa only [energy0_eq_norm_sq, Real.sqrt_sq (norm_nonneg (q s))] using hn
  have hτmem : τ ∈ Ioo (-a) a := ⟨by linarith, hτa⟩
  have hnτmem : -τ ∈ Ioo (-a) a := ⟨by linarith, by linarith⟩
  have hτabs : |τ| ≤ A := by simpa only [abs_of_pos hτ₀] using hτA
  have hnτabs : |-τ| ≤ A := by simpa only [abs_neg] using hτabs
  obtain ⟨qleft, hleft₀, hleft⟩ := hlocal (-τ) (q (-τ)) (hbound (-τ) hnτmem hnτabs)
  obtain ⟨qright, hright₀, hright⟩ := hlocal τ (q τ) (hbound τ hτmem hτabs)
  let U : ℝ := A + ε / 2
  let qmid : ℝ → Phase N := piecewise (Ioo (-a) a) q qleft
  have hmid : ∀ t ∈ Ioo (-U) a, HasDerivAt qmid (drift ν N (qmid t)) t := by
    have hglue := local_drift_solutions_piecewise ν N hq hleft
      (t₀ := -τ) ⟨hnτmem, ⟨by linarith, by linarith⟩⟩ hleft₀.symm
    intro t ht
    apply hglue t
    by_cases hlow : -a < t
    · exact Or.inl ⟨hlow, ht.2⟩
    · apply Or.inr
      constructor
      · have htlow := ht.1
        dsimp [U, τ] at htlow ⊢
        linarith
      · linarith
  let qext : ℝ → Phase N := piecewise (Ioo (-U) a) qmid qright
  have hext₀ : qext 0 = q₀ := by
    have hU : 0 < U := by dsimp [U]; linarith
    simp only [qext, qmid, piecewise, if_pos (show (0 : ℝ) ∈ Ioo (-U) a from
      ⟨neg_lt_zero.mpr hU, ha₀⟩), if_pos (show (0 : ℝ) ∈ Ioo (-a) a from
      ⟨neg_lt_zero.mpr ha₀, ha₀⟩), hq₀]
  have hext : ∀ t ∈ Ioo (-U) U, HasDerivAt qext (drift ν N (qext t)) t := by
    have hτmid : τ ∈ Ioo (-U) a := by dsimp [U, τ]; constructor <;> linarith
    have hmideq : qmid τ = qright τ := by
      simp only [qmid, piecewise, if_pos hτmem]
      exact hright₀.symm
    have hglue := local_drift_solutions_piecewise ν N hmid hright
      (t₀ := τ) ⟨hτmid, ⟨by linarith, by linarith⟩⟩ hmideq
    intro t ht
    apply hglue t
    by_cases hhigh : t < a
    · exact Or.inl ⟨ht.1, hhigh⟩
    · apply Or.inr
      constructor
      · linarith
      · have hthigh := ht.2
        dsimp [U, τ] at hthigh ⊢
        linarith
  have hUS : U ∈ S := ⟨qext, hext₀, hext⟩
  have hUA : U ≤ A := le_csSup hbdd hUS
  dsimp [U] at hUA
  linarith

/-- The actual finite native drift has a complete orbit through every phase point. -/
theorem exists_complete_drift_orbit {ν : ℝ} (hν : 0 ≤ ν)
    (N : ℕ) (q₀ : Phase N) :
    ∃ q : ℝ → Phase N, q 0 = q₀ ∧
      ∀ t : ℝ, HasDerivAt q (drift ν N (q t)) t := by
  classical
  choose q hq₀ hq using exists_drift_solution_on_arbitrary_interval hν N q₀
  let g : ℝ → Phase N := fun t => q (|t| + 1) t
  have hagree {A : ℝ} (hA : 0 < A) : EqOn g (q A) (Ioo (-A) A) := by
    intro t ht
    have hB : 0 < |t| + 1 := by positivity
    have htB : t ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
      abs_lt.mp (lt_add_one |t|)
    dsimp [g]
    rcases le_total (|t| + 1) A with hle | hle
    · exact local_drift_solutions_unique ν N (hq (|t| + 1))
        (fun s hs => hq A s ⟨(neg_le_neg hle).trans_lt hs.1, hs.2.trans_le hle⟩)
        ⟨neg_lt_zero.mpr hB, hB⟩ (by rw [hq₀, hq₀]) htB
    · exact local_drift_solutions_unique ν N
        (fun s hs => hq (|t| + 1) s
          ⟨(neg_le_neg hle).trans_lt hs.1, hs.2.trans_le hle⟩)
        (hq A) ⟨neg_lt_zero.mpr hA, hA⟩ (by rw [hq₀, hq₀]) ht
  refine ⟨g, hq₀ (|0| + 1), ?_⟩
  intro t
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one |t|)
  have hnear : g =ᶠ[𝓝 t] q (|t| + 1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hagree (by positivity) hs
  have hd := (hq (|t| + 1) t ht).congr_of_eventuallyEq hnear
  rw [← hnear.eq_of_nhds] at hd
  exact hd

/-- Complete native orbits are uniquely determined by their initial phase. -/
theorem exists_unique_complete_drift_orbit {ν : ℝ} (hν : 0 ≤ ν)
    (N : ℕ) (q₀ : Phase N) :
    ∃! q : ℝ → Phase N, q 0 = q₀ ∧
      ∀ t : ℝ, HasDerivAt q (drift ν N (q t)) t := by
  obtain ⟨q, hq₀, hq⟩ := exists_complete_drift_orbit hν N q₀
  refine ⟨q, ⟨hq₀, hq⟩, ?_⟩
  intro r hr
  exact drift_solutions_unique ν N hr.2 hq (t₀ := 0) (hr.1.trans hq₀.symm)

/-- The actual polynomial drift gives smooth time dependence along every complete orbit. -/
theorem contDiff_complete_drift_orbit (ν : ℝ) (N : ℕ) {q : ℝ → Phase N}
    (hq : ∀ t : ℝ, HasDerivAt q (drift ν N (q t)) t) : ContDiff ℝ ∞ q := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hf : ContDiff ℝ ∞ (fun p : ℝ × Phase N => drift ν N p.2) :=
    (contDiff_drift ν N).comp contDiff_snd
  have hi : ContDiffOn ℝ ∞ q (Icc (t - 1) (t + 1)) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun _ => drift ν N) (u := univ) hf.contDiffOn
      (fun s _ => (hq s).hasDerivWithinAt) (fun _ _ => mem_univ _)
  exact (hi t ⟨by linarith, by linarith⟩).contDiffAt
    (Icc_mem_nhds (by linarith) (by linarith))

end

end QuantumAdapter.Assembly
