import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Complete continuous linear ordinary differential equations

On each bounded time interval the local existence time is independent of the
initial vector: enlarge the state ball proportionally to its initial norm.
Continuation consequently needs no finite-dimensional compactness assumption.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter Metric
open scoped Topology NNReal

namespace QuantumAdapter.Obligations

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem local_linear_ode_solutions_unique
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    {q r : ℝ → E} {a b t₀ : ℝ}
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (A t (q t)) t)
    (hr : ∀ t ∈ Ioo a b, HasDerivAt r (A t (r t)) t)
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
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hA.continuousOn : ContinuousOn A (Icc l u))
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hK (s : ℝ) (hs : s ∈ Icc l u) : ‖A s‖₊ ≤ K := by
    change ‖A s‖ ≤ max C 0
    exact (hC s hs).trans (le_max_left _ _)
  have hlip (s : ℝ) (hs : s ∈ Icc l u) :
      LipschitzOnWith K (A s) (univ : Set E) :=
    ((A s).lipschitz.weaken (hK s hs)).lipschitzOnWith
  rcases le_total t₀ t with hle | hle
  · have hlu : l = t₀ ∧ u = t := ⟨min_eq_left hle, max_eq_right hle⟩
    have heq := ODE_solution_unique_of_mem_Icc_right
      (v := fun s => A s) (s := fun _ => univ) (a := l) (b := u) (K := K)
      (fun s hs => hlip s (Ico_subset_Icc_self hs)) hqc
      (fun s hs => (hq s (hdom (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hrc
      (fun s hs => (hr s (hdom (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ => mem_univ _) (by simpa only [hlu.1] using h₀)
    exact heq (by rw [hlu.1, hlu.2]; exact ⟨hle, le_rfl⟩)
  · have hlu : l = t ∧ u = t₀ := ⟨min_eq_right hle, max_eq_left hle⟩
    have heq := ODE_solution_unique_of_mem_Icc_left
      (v := fun s => A s) (s := fun _ => univ) (a := l) (b := u) (K := K)
      (fun s hs => hlip s (Ioc_subset_Icc_self hs)) hqc
      (fun s hs => (hq s (hdom (Ioc_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ => mem_univ _) hrc
      (fun s hs => (hr s (hdom (Ioc_subset_Icc_self hs))).hasDerivWithinAt)
      (fun _ _ => mem_univ _) (by simpa only [hlu.2] using h₀)
    exact heq (by rw [hlu.1, hlu.2]; exact ⟨le_rfl, hle⟩)

theorem local_linear_ode_solutions_piecewise
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    {q r : ℝ → E} {a b c d t₀ : ℝ}
    (hq : ∀ t ∈ Ioo a b, HasDerivAt q (A t (q t)) t)
    (hr : ∀ t ∈ Ioo c d, HasDerivAt r (A t (r t)) t)
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo c d) (h₀ : q t₀ = r t₀) :
    ∀ t ∈ Ioo a b ∪ Ioo c d,
      HasDerivAt (piecewise (Ioo a b) q r)
        (A t (piecewise (Ioo a b) q r t)) t := by
  classical
  have heq : EqOn q r (Ioo (max a c) (min b d)) :=
    local_linear_ode_solutions_unique A hA
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

/-- A common local existence time for all state vectors at bounded times. -/
theorem exists_uniform_local_linear_ode
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (B : ℝ) (hB : 0 ≤ B) :
    ∃ ε > (0 : ℝ), ∀ t₀ : ℝ, |t₀| ≤ B → ∀ x : E,
      ∃ q : ℝ → E, q t₀ = x ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt q (A t (q t)) t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hA.continuousOn : ContinuousOn A (Icc (-B - 1) (B + 1)))
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hK (t : ℝ) (ht : t ∈ Icc (-B - 1) (B + 1)) : ‖A t‖ ≤ K :=
    (hC t ht).trans (le_max_left _ _)
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heq : (2 * ((K : ℝ) + 1)) * ε = 1 := by
    dsimp [ε]
    field_simp [show (K : ℝ) + 1 ≠ 0 by positivity]
  have hε1 : ε ≤ 1 := by
    have hp := mul_nonneg K.property hε.le
    nlinarith
  have hKε : (K : ℝ) * ε ≤ 1 / 2 := by nlinarith
  refine ⟨ε, hε, ?_⟩
  intro t₀ ht₀ x
  let r : ℝ≥0 := ‖x‖₊
  let a : ℝ≥0 := 2 * (r + 1)
  let L : ℝ≥0 := K * a
  have htime (t : ℝ) (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) :
      t ∈ Icc (-B - 1) (B + 1) := by
    have habs := abs_le.mp ht₀
    constructor <;> linarith
  have hPL : IsPicardLindelof (fun t z => A t z)
      (tmin := t₀ - ε) (tmax := t₀ + ε)
      ⟨t₀, by constructor <;> linarith⟩ (0 : E) a r L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      have hn : ‖A t‖₊ ≤ K := by exact_mod_cast hK t (htime t ht)
      exact ((A t).lipschitz.weaken hn).lipschitzOnWith
    · intro z hz
      exact (hA.clm_apply continuous_const).continuousOn
    · intro t ht z hz
      have hz' : ‖z‖ ≤ (a : ℝ) := by
        simpa only [mem_closedBall, dist_zero_right] using hz
      calc
        ‖A t z‖ ≤ ‖A t‖ * ‖z‖ := (A t).le_opNorm z
        _ ≤ (K : ℝ) * (a : ℝ) :=
          mul_le_mul (hK t (htime t ht)) hz' (norm_nonneg z) K.property
        _ = (L : ℝ) := rfl
    · simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
      change ((K : ℝ) * (2 * ((r : ℝ) + 1))) * ε ≤
        2 * ((r : ℝ) + 1) - (r : ℝ)
      have hm := mul_le_mul_of_nonneg_right hKε
        (by positivity : 0 ≤ 2 * ((r : ℝ) + 1))
      have hr := r.property
      nlinarith
  have hx : x ∈ closedBall (0 : E) r := by
    simp only [mem_closedBall, dist_zero_right]
    exact le_rfl
  obtain ⟨q, hq₀, hq⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hx
  refine ⟨q, hq₀, ?_⟩
  intro t ht
  exact (hq t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

set_option maxHeartbeats 1000000 in
theorem exists_linear_ode_on_arbitrary_interval
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x₀ : E) (T : ℝ) :
    ∃ q : ℝ → E, q 0 = x₀ ∧
      ∀ t ∈ Ioo (-T) T, HasDerivAt q (A t (q t)) t := by
  classical
  let S : Set ℝ := {a | ∃ q : ℝ → E, q 0 = x₀ ∧
    ∀ t ∈ Ioo (-a) a, HasDerivAt q (A t (q t)) t}
  obtain ⟨ε₀, hε₀, hlocal₀⟩ := exists_uniform_local_linear_ode A hA 1 (by norm_num)
  obtain ⟨qinit, hinit, hqinit⟩ := hlocal₀ 0 (by norm_num) x₀
  have hinitS : ε₀ ∈ S :=
    ⟨qinit, hinit, by simpa only [zero_sub, zero_add] using hqinit⟩
  have hne : S.Nonempty := ⟨ε₀, hinitS⟩
  suffices hunbdd : ¬ BddAbove S by
    obtain ⟨a, ⟨q, hq₀, hq⟩, hTa⟩ := not_bddAbove_iff.mp hunbdd T
    refine ⟨q, hq₀, fun t ht => hq t ?_⟩
    exact ⟨(neg_lt_neg hTa).trans ht.1, ht.2.trans hTa⟩
  intro hbdd
  let R : ℝ := sSup S
  have hR₀ : 0 < R := hε₀.trans_le (le_csSup hbdd hinitS)
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_local_linear_ode A hA R hR₀.le
  have hεS : ε ∈ S := by
    obtain ⟨p, hp₀, hp⟩ := hlocal 0 (by simpa using hR₀.le) x₀
    exact ⟨p, hp₀, by simpa only [zero_sub, zero_add] using hp⟩
  have hεR : ε ≤ R := le_csSup hbdd hεS
  obtain ⟨a, haS, hnear⟩ := Real.add_neg_lt_sSup hne (ε := -(ε / 2)) (by linarith)
  have hnear' : R - ε / 2 < a := by simpa only [sub_eq_add_neg] using hnear
  obtain ⟨q, hq₀, hq⟩ := haS
  let τ : ℝ := R - ε / 2
  have hτ₀ : 0 < τ := by dsimp [τ]; linarith
  have hτa : τ < a := hnear'
  have ha₀ : 0 < a := hτ₀.trans hτa
  have hτR : τ ≤ R := by dsimp [τ]; linarith
  have hτmem : τ ∈ Ioo (-a) a := ⟨by linarith, hτa⟩
  have hnτmem : -τ ∈ Ioo (-a) a := ⟨by linarith, by linarith⟩
  have hτabs : |τ| ≤ R := by simpa only [abs_of_pos hτ₀] using hτR
  have hnτabs : |-τ| ≤ R := by simpa only [abs_neg] using hτabs
  obtain ⟨qleft, hleft₀, hleft⟩ := hlocal (-τ) hnτabs (q (-τ))
  obtain ⟨qright, hright₀, hright⟩ := hlocal τ hτabs (q τ)
  let U : ℝ := R + ε / 2
  let qmid : ℝ → E := piecewise (Ioo (-a) a) q qleft
  have hmid : ∀ t ∈ Ioo (-U) a, HasDerivAt qmid (A t (qmid t)) t := by
    have hglue := local_linear_ode_solutions_piecewise A hA hq hleft
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
  let qext : ℝ → E := piecewise (Ioo (-U) a) qmid qright
  have hext₀ : qext 0 = x₀ := by
    have hU : 0 < U := by dsimp [U]; linarith
    simp only [qext, qmid, piecewise, if_pos (show (0 : ℝ) ∈ Ioo (-U) a from
      ⟨neg_lt_zero.mpr hU, ha₀⟩), if_pos (show (0 : ℝ) ∈ Ioo (-a) a from
      ⟨neg_lt_zero.mpr ha₀, ha₀⟩), hq₀]
  have hext : ∀ t ∈ Ioo (-U) U, HasDerivAt qext (A t (qext t)) t := by
    have hτmid : τ ∈ Ioo (-U) a := by dsimp [U, τ]; constructor <;> linarith
    have hmideq : qmid τ = qright τ := by
      simp only [qmid, piecewise, if_pos hτmem]
      exact hright₀.symm
    have hglue := local_linear_ode_solutions_piecewise A hA hmid hright
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
  have hUR : U ≤ R := le_csSup hbdd hUS
  dsimp [U] at hUR
  linarith

/-- Every continuous time-dependent bounded-linear vector field is complete. -/
theorem exists_complete_linear_ode
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) (x₀ : E) :
    ∃ q : ℝ → E, q 0 = x₀ ∧ ∀ t : ℝ, HasDerivAt q (A t (q t)) t := by
  classical
  choose q hq₀ hq using exists_linear_ode_on_arbitrary_interval A hA x₀
  let g : ℝ → E := fun t => q (|t| + 1) t
  have hagree {R : ℝ} (hR : 0 < R) : EqOn g (q R) (Ioo (-R) R) := by
    intro t ht
    have hB : 0 < |t| + 1 := by positivity
    have htB : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one |t|)
    dsimp [g]
    rcases le_total (|t| + 1) R with hle | hle
    · exact local_linear_ode_solutions_unique A hA (hq (|t| + 1))
        (fun s hs => hq R s ⟨(neg_le_neg hle).trans_lt hs.1, hs.2.trans_le hle⟩)
        ⟨neg_lt_zero.mpr hB, hB⟩ (by rw [hq₀, hq₀]) htB
    · exact local_linear_ode_solutions_unique A hA
        (fun s hs => hq (|t| + 1) s
          ⟨(neg_le_neg hle).trans_lt hs.1, hs.2.trans_le hle⟩)
        (hq R) ⟨neg_lt_zero.mpr hR, hR⟩ (by rw [hq₀, hq₀]) ht
  refine ⟨g, hq₀ (|0| + 1), ?_⟩
  intro t
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one |t|)
  have hnear : g =ᶠ[𝓝 t] q (|t| + 1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hagree (by positivity) hs
  have hd := (hq (|t| + 1) t ht).congr_of_eventuallyEq hnear
  rw [← hnear.eq_of_nhds] at hd
  exact hd

end
end QuantumAdapter.Obligations
