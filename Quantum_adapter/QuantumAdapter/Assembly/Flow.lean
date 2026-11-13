import QuantumAdapter.Dynamics
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Connected.Clopen

/-!
# Native finite-flow construction edges

The actual constrained Fourier drift is smooth. Local existence and global
uniqueness follow with no auxiliary regularity or Lipschitz hypotheses.
Every supplied complete PhaseFlow is consequently the same flow.

Complete-flow existence and the divergence identity are not asserted here.
Compilation and axiom auditing take place only in the external cached runner.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators ContDiff Topology

namespace QuantumAdapter.Assembly

noncomputable section

open SingularClosure

/-- Actual coefficient evaluation is a smooth real-linear coordinate. -/
theorem contDiff_phaseCoeff (N : ℕ) (k : Frequency) (i : Fin 3) :
    ContDiff ℝ ∞ (fun q : Phase N => phaseCoeff q k i) := by
  simpa only [phaseCoordinate_apply] using (phaseCoordinate N k i).contDiff

/-- Each actual finite convolution coefficient is smooth on the real phase. -/
theorem contDiff_fullTransport (N : ℕ) (k : Frequency) (i : Fin 3) :
    ContDiff ℝ ∞ (fun q : Phase N => fullTransport N (phaseCoeff q) k i) := by
  classical
  unfold fullTransport
  apply ContDiff.sum
  intro p hp
  apply ContDiff.mul
  · apply ContDiff.sum
    intro j hj
    exact (contDiff_phaseCoeff N p j).mul contDiff_const
  · exact contDiff_phaseCoeff N (k - p) i

/-- Leray projection introduces only fixed frequency-dependent scalars. -/
theorem contDiff_lerayTransport (N : ℕ) (k : Frequency) (i : Fin 3) :
    ContDiff ℝ ∞ (fun q : Phase N =>
      coefficientLeray k (fullTransport N (phaseCoeff q) k) i) := by
  classical
  by_cases hk : k = 0
  · simp only [coefficientLeray, hk, if_pos]
    exact contDiff_fullTransport N 0 i
  · simp only [coefficientLeray, if_neg hk]
    apply ContDiff.sub (contDiff_fullTransport N k i)
    apply ContDiff.div_const
    apply ContDiff.mul contDiff_const
    apply ContDiff.sum
    intro j hj
    exact contDiff_const.mul (contDiff_fullTransport N k j)

/-- Smoothness of the exact raw viscous Fourier RHS, including its frozen mean. -/
theorem contDiff_rawRhs (ν : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (rawRhs ν N) := by
  classical
  apply (contDiff_piLp 2).2
  intro ki
  change ContDiff ℝ ∞ (fun q : Phase N =>
    if ki.1.val = 0 then 0 else
      -((ν * laplaceSymbol ki.1.val : ℝ) : ℂ) * phaseCoeff q ki.1.val ki.2 -
        coefficientLeray ki.1.val (fullTransport N (phaseCoeff q) ki.1.val) ki.2)
  by_cases hk : ki.1.val = 0
  · simp only [if_pos hk]
    exact contDiff_const
  · simp only [if_neg hk]
    exact (contDiff_const.mul (contDiff_phaseCoeff N ki.1.val ki.2)).sub
      (contDiff_lerayTransport N ki.1.val ki.2)

/-- The native orthogonal projection preserves the established smoothness. -/
theorem contDiff_drift (ν : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (drift ν N) := by
  exact (phaseSubmodule N).orthogonalProjectionOnto.contDiff.comp (contDiff_rawRhs ν N)

/-- Local solutions of the actual drift exist through every phase point. -/
theorem exists_local_drift_solution (ν : ℝ) (N : ℕ)
    (q₀ : Phase N) (t₀ : ℝ) :
    ∃ q : ℝ → Phase N, q t₀ = q₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt q (drift ν N (q t)) t := by
  have hd : ContDiff ℝ 1 (drift ν N) :=
    (contDiff_drift ν N).of_le (by simp)
  exact hd.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀

/-- The native drift is Lipschitz on a neighborhood of each initial point. -/
theorem drift_locally_lipschitz (ν : ℝ) (N : ℕ) (q₀ : Phase N) :
    ∃ K : ℝ≥0, ∃ s : Set (Phase N), s ∈ 𝓝 q₀ ∧
      LipschitzOnWith K (drift ν N) s := by
  have hd : ContDiff ℝ 1 (drift ν N) :=
    (contDiff_drift ν N).of_le (by simp)
  exact hd.contDiffAt.exists_lipschitzOnWith

/-- Local uniqueness for two entire curves solving the actual finite ODE. -/
theorem drift_solutions_eventuallyEq (ν : ℝ) (N : ℕ)
    {q r : ℝ → Phase N} {t₀ : ℝ}
    (hq : ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (hr : ∀ t, HasDerivAt r (drift ν N (r t)) t)
    (h₀ : q t₀ = r t₀) :
    q =ᶠ[𝓝 t₀] r := by
  obtain ⟨K, s, hs, hl⟩ := drift_locally_lipschitz ν N (q t₀)
  have hqs : ∀ᶠ t in 𝓝 t₀, q t ∈ s := (hq t₀).continuousAt.eventually_mem hs
  have hrs : ∀ᶠ t in 𝓝 t₀, r t ∈ s := by
    have hs' : s ∈ 𝓝 (r t₀) := by simpa only [h₀] using hs
    exact (hr t₀).continuousAt.eventually_mem hs'
  exact ODE_solution_unique_of_eventually
    (v := fun _ => drift ν N) (s := fun _ => s)
    (Eventually.of_forall fun _ => hl)
    ((Eventually.of_forall hq).and hqs)
    ((Eventually.of_forall hr).and hrs) h₀

/-- Local uniqueness extends to all real times by connectedness. -/
theorem drift_solutions_unique (ν : ℝ) (N : ℕ)
    {q r : ℝ → Phase N} {t₀ : ℝ}
    (hq : ∀ t, HasDerivAt q (drift ν N (q t)) t)
    (hr : ∀ t, HasDerivAt r (drift ν N (r t)) t)
    (h₀ : q t₀ = r t₀) : q = r := by
  have hqc : Continuous q := continuous_iff_continuousAt.mpr
    (fun t => (hq t).continuousAt)
  have hrc : Continuous r := continuous_iff_continuousAt.mpr
    (fun t => (hr t).continuousAt)
  have hclosed : IsClosed {t | q t = r t} := isClosed_eq hqc hrc
  have hopen : IsOpen {t | q t = r t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact drift_solutions_eventuallyEq ν N hq hr ht
  have hset : {t | q t = r t} = univ :=
    (show IsClopen {t | q t = r t} from ⟨hclosed, hopen⟩).eq_univ ⟨t₀, h₀⟩
  funext t
  have ht : t ∈ {t | q t = r t} := by rw [hset]; trivial
  exact ht

/-- Any two native complete flow records have the same time maps. -/
theorem phaseFlow_map_unique {ν : ℝ} (F G : PhaseFlow ν)
    (N : ℕ) (t : ℝ) (q₀ : Phase N) :
    F.map N t q₀ = G.map N t q₀ := by
  have heq : (fun s => F.map N s q₀) = (fun s => G.map N s q₀) :=
    drift_solutions_unique ν N (F.orbit_derivative N q₀)
      (G.orbit_derivative N q₀) (t₀ := 0)
      (by rw [F.map_zero, G.map_zero])
  exact congrFun heq t

/-- The entire native flow structure is unique; proof fields add no choice. -/
theorem phaseFlow_unique {ν : ℝ} (F G : PhaseFlow ν) : F = G := by
  have hm : F.map = G.map := by
    funext N t q
    exact phaseFlow_map_unique F G N t q
  cases F
  cases G
  cases hm
  rfl

/-- A native complete flow fixes the zero phase for every real time. -/
theorem phaseFlow_zero {ν : ℝ} (F : PhaseFlow ν) (N : ℕ) (t : ℝ) :
    F.map N t 0 = 0 := by
  have hz : ∀ s : ℝ, HasDerivAt (fun _ : ℝ => (0 : Phase N))
      (drift ν N 0) s := by
    intro s
    simpa only [drift_zero] using hasDerivAt_const s (0 : Phase N)
  have heq := drift_solutions_unique ν N (F.orbit_derivative N 0) hz
    (t₀ := 0) (F.map_zero N 0)
  exact congrFun heq t

/-- Coefficient energy differentiation for arbitrary signed times of a native flow. -/
theorem phaseFlow_energy0_hasDerivAt {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q₀ : Phase N) (t : ℝ) :
    HasDerivAt (fun s => energy0 N (F.map N s q₀))
      ((-2 * ν) * dissipation N (F.map N t q₀)) t := by
  have hc (k : Frequency) (i : Fin 3) :
      HasDerivAt (fun s => phaseCoeff (F.map N s q₀) k i)
        (phaseCoeff (drift ν N (F.map N t q₀)) k i) t := by
    simpa only [Function.comp_def, phaseCoordinate_apply] using
      (phaseCoordinate N k i).hasFDerivAt.comp_hasDerivAt t
        (F.orbit_derivative N q₀ t)
  rw [← rawRhs_energy_rate ν N (F.map N t q₀)]
  unfold energy0
  apply HasDerivAt.fun_sum
  intro k hk
  apply HasDerivAt.fun_sum
  intro i hi
  have h := hasDerivWithinAt_complex_normSq
    ((hc k i).hasDerivWithinAt (s := (univ : Set ℝ)))
  simpa only [phaseCoeff, drift_eq_rawRhs] using
    h.hasDerivAt (by simp)

/-- The actual unweighted energy is nonincreasing on the whole time axis. -/
theorem phaseFlow_energy0_antitone {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (q₀ : Phase N) :
    Antitone (fun t => energy0 N (F.map N t q₀)) := by
  apply antitone_of_hasDerivAt_nonpos (phaseFlow_energy0_hasDerivAt F N q₀)
  intro t
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hν)
    (dissipation_nonneg N (F.map N t q₀))

/-- A finite spectral trace bounds each retained Laplace eigenvalue. -/
theorem laplaceSymbol_le_finiteLaplaceTrace (N : ℕ) (k : Frequency)
    (hk : k ∈ fullModes N) :
    laplaceSymbol k ≤ finiteLaplaceTrace N := by
  have hk0 := laplaceSymbol_nonneg k
  have hs : 2 * laplaceSymbol k ≤
      ∑ p ∈ fullModes N, 2 * laplaceSymbol p :=
    Finset.single_le_sum (fun p hp => mul_nonneg (by norm_num) (laplaceSymbol_nonneg p)) hk
  exact (by linarith : laplaceSymbol k ≤ 2 * laplaceSymbol k).trans hs

/-- A cutoff-dependent scalar upper bound for the actual dissipation. -/
theorem dissipation_le_finiteLaplaceTrace_mul_energy0 (N : ℕ) (q : Phase N) :
    dissipation N q ≤ finiteLaplaceTrace N * energy0 N q := by
  unfold dissipation energy0
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right (laplaceSymbol_le_finiteLaplaceTrace N k hk)
    (Complex.normSq_nonneg _)

/-- Every flow record yields the already proved forward energy bound. -/
theorem phaseFlow_energy0_le_initial {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (q₀ : Phase N) {t : ℝ} (ht : 0 ≤ t) :
    energy0 N (F.map N t q₀) ≤ energy0 N q₀ :=
  (phaseFlow_isTrajectory F N q₀).energy0_le_initial hν ht

/-- An integrating factor controls backward growth without dividing by energy. -/
theorem phaseFlow_weighted_energy0_monotone {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (q₀ : Phase N) :
    Monotone (fun t => Real.exp ((2 * ν * finiteLaplaceTrace N) * t) *
      energy0 N (F.map N t q₀)) := by
  apply monotone_of_hasDerivAt_nonneg
    (f' := fun t => Real.exp ((2 * ν * finiteLaplaceTrace N) * t) *
      ((2 * ν * finiteLaplaceTrace N) * energy0 N (F.map N t q₀) -
        2 * ν * dissipation N (F.map N t q₀)))
  · intro t
    convert (((hasDerivAt_id t).const_mul (2 * ν * finiteLaplaceTrace N)).exp).mul
      (phaseFlow_energy0_hasDerivAt F N q₀ t) using 1 <;> ring
  · intro t
    apply mul_nonneg (Real.exp_nonneg _)
    have hb := mul_le_mul_of_nonneg_left
      (dissipation_le_finiteLaplaceTrace_mul_energy0 N (F.map N t q₀))
      (show 0 ≤ 2 * ν by positivity)
    nlinarith

/-- Every fixed cutoff has an explicit finite backward energy bound. -/
theorem phaseFlow_energy0_backward_bound {ν : ℝ} (hν : 0 ≤ ν)
    (F : PhaseFlow ν) (N : ℕ) (q₀ : Phase N) {t : ℝ} (ht : t ≤ 0) :
    energy0 N (F.map N t q₀) ≤
      Real.exp (-((2 * ν * finiteLaplaceTrace N) * t)) * energy0 N q₀ := by
  have h := phaseFlow_weighted_energy0_monotone hν F N q₀ ht
  simp only [mul_zero, Real.exp_zero, one_mul, F.map_zero] at h
  have hm := mul_le_mul_of_nonneg_left h
    (Real.exp_nonneg (-((2 * ν * finiteLaplaceTrace N) * t)))
  simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_mul] using hm

end

end QuantumAdapter.Assembly

