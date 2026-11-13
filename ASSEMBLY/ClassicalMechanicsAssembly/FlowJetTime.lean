import ClassicalMechanicsAssembly.FlowSmooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-!
# Joint time increments from the actual integral equation

Joint continuity of the forcing term and the actual integral identity imply
the uniform time remainder used by `FlowSmooth`. All estimates stay inside
the closed slab, including at both boundary time slices.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set Filter ClassicalMechanics NSEMaxwell.Classical
open scoped Topology ContDiff Interval

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The initial-time integral identity gives differences between arbitrary slab times. -/
theorem flow_integral_difference {T : ℝ} {J P : ℝ × Vec → F}
    (hP : ContinuousOn P (finiteSpacetime T))
    (hbase : ∀ s ∈ Icc (0 : ℝ) T, ∀ b : Vec,
      J (s, b) = J (0, b) + ∫ r in (0 : ℝ)..s, P (r, b))
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T)
    (b : Vec) :
    J (s, b) - J (t, b) = ∫ r in t..s, P (r, b) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have h0t : IntervalIntegrable (fun r => P (r, b)) MeasureTheory.volume 0 t :=
    (hP.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => uIcc_subset_Icc h0 ht hr)).intervalIntegrable
  have hts : IntervalIntegrable (fun r => P (r, b)) MeasureTheory.volume t s :=
    (hP.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => uIcc_subset_Icc ht hs hr)).intervalIntegrable
  rw [hbase s hs b, hbase t ht b,
    ← intervalIntegral.integral_add_adjacent_intervals h0t hts]
  abel

/--
The uniform time remainder is a consequence of joint forcing continuity and
the actual integral equation, rather than a new differentiability assumption.
-/
theorem flow_time_remainder_of_integral {T : ℝ} {J P : ℝ × Vec → F}
    (hP : ContinuousOn P (finiteSpacetime T))
    (hbase : ∀ s ∈ Icc (0 : ℝ) T, ∀ b : Vec,
      J (s, b) = J (0, b) + ∫ r in (0 : ℝ)..s, P (r, b))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    (fun z : ℝ × Vec => J z - J (t, z.2) - (z.1 - t) • P (t, a))
      =o[𝓝[finiteSpacetime T] (t, a)] (fun z => z - (t, a)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  obtain ⟨δ, hδ, hnear⟩ :=
    Metric.continuousWithinAt_iff.mp (hP (t, a) ht) c hc
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨δ, hδ, ?_⟩
  rintro z ⟨hzball, hz⟩
  have hzdist : dist z (t, a) < δ := hzball
  have hslice : ContinuousOn (fun r => P (r, z.2)) (uIcc t z.1) :=
    hP.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => uIcc_subset_Icc ht hz hr)
  have hi := hslice.intervalIntegrable
  have heq : J z - J (t, z.2) - (z.1 - t) • P (t, a) =
      ∫ r in t..z.1, P (r, z.2) - P (t, a) := by
    rw [flow_integral_difference hP hbase hz ht z.2,
      intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
  rw [heq]
  calc
    ‖∫ r in t..z.1, P (r, z.2) - P (t, a)‖ ≤ c * |z.1 - t| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      have hri : r ∈ uIcc t z.1 := uIoc_subset_uIcc hr
      have hrs : (r, z.2) ∈ finiteSpacetime T := uIcc_subset_Icc ht hz hri
      have hd : dist (r, z.2) (t, a) ≤ dist z (t, a) := by
        simp only [Prod.dist_eq]
        apply max_le_max
        · simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc hri
        · exact le_rfl
      have hp := hnear hrs (hd.trans_lt hzdist)
      exact (by simpa only [dist_eq_norm] using hp.le)
    _ ≤ c * ‖z - (t, a)‖ := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      simpa only [Real.norm_eq_abs] using norm_fst_le (z - (t, a))

/--
Joint slab differentiability follows from the actual label derivative and
the integral identity with jointly continuous forcing. No uniform-remainder
hypothesis remains in this statement.
-/
theorem flow_hasFDerivWithinAt_of_integral {T : ℝ} {J P : ℝ × Vec → F}
    (hP : ContinuousOn P (finiteSpacetime T))
    (hbase : ∀ s ∈ Icc (0 : ℝ) T, ∀ b : Vec,
      J (s, b) = J (0, b) + ∫ r in (0 : ℝ)..s, P (r, b))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {a : Vec} {A : Vec →L[ℝ] F}
    (hlabel : HasFDerivAt (fun b => J (t, b)) A a) :
    HasFDerivWithinAt J (flowJointDerivative (P (t, a)) A)
      (finiteSpacetime T) (t, a) := by
  exact flow_hasFDerivWithinAt_of_time_remainder hlabel
    (flow_time_remainder_of_integral hP hbase ht a)

/--
The jet bootstrap with its joint-derivative obligation discharged by actual
label derivatives and integral equations. The finite-order forcing closure
remains explicit until the ODE partition formulas are assembled.
-/
theorem flowJet_tower_contDiffOn_of_integrals {T : ℝ} (hT : 0 < T)
    (J P : ∀ r : ℕ, ℝ × Vec → FlowJet r)
    (hcontinuous : ∀ r, ContinuousOn (J r) (finiteSpacetime T))
    (hlabel : ∀ r t, t ∈ Icc (0 : ℝ) T → ∀ a : Vec,
      HasFDerivAt (fun b => J r (t, b)) (J (r + 1) (t, a)).curryLeft a)
    (hbase : ∀ r s, s ∈ Icc (0 : ℝ) T → ∀ b : Vec,
      J r (s, b) = J r (0, b) + ∫ q in (0 : ℝ)..s, P r (q, b))
    (hforcing : ∀ n : ℕ,
      (∀ r, ContDiffOn ℝ n (J r) (finiteSpacetime T)) →
      ∀ r, ContDiffOn ℝ n (P r) (finiteSpacetime T)) :
    ∀ r, ContDiffOn ℝ ∞ (J r) (finiteSpacetime T) := by
  have hP : ∀ r, ContinuousOn (P r) (finiteSpacetime T) := by
    intro r
    exact (hforcing 0 (fun k => contDiffOn_zero.mpr (hcontinuous k)) r).continuousOn
  apply flowJet_tower_contDiffOn hT J P hcontinuous _ hforcing
  intro r z hz
  exact flow_hasFDerivWithinAt_of_integral (hP r) (hbase r) hz
    (hlabel r z.1 hz z.2)

/-- Zeroth-jet realization gives the literal finite-slab velocity regularity. -/
theorem smoothVelocityOn_of_flowJet_integrals {T : ℝ} (hT : 0 < T)
    {η : Velocity} (J P : ∀ r : ℕ, ℝ × Vec → FlowJet r)
    (hcontinuous : ∀ r, ContinuousOn (J r) (finiteSpacetime T))
    (hlabel : ∀ r t, t ∈ Icc (0 : ℝ) T → ∀ a : Vec,
      HasFDerivAt (fun b => J r (t, b)) (J (r + 1) (t, a)).curryLeft a)
    (hbase : ∀ r s, s ∈ Icc (0 : ℝ) T → ∀ b : Vec,
      J r (s, b) = J r (0, b) + ∫ q in (0 : ℝ)..s, P r (q, b))
    (hforcing : ∀ n : ℕ,
      (∀ r, ContDiffOn ℝ n (J r) (finiteSpacetime T)) →
      ∀ r, ContDiffOn ℝ n (P r) (finiteSpacetime T))
    (hzero : ∀ z ∈ finiteSpacetime T,
      η z.1 z.2 = continuousMultilinearCurryFin0 ℝ Vec Vec (J 0 z)) :
    SmoothVelocityOn T η := by
  have hj := flowJet_tower_contDiffOn_of_integrals hT J P hcontinuous hlabel hbase hforcing 0
  have hv := (continuousMultilinearCurryFin0 ℝ Vec Vec).contDiff.comp_contDiffOn hj
  exact hv.congr hzero

end

end ClassicalMechanicsAssembly
