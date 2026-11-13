import SingularClosure.PhysicalEnstrophy

/-!
# Fixed finite covering estimate for periodic physical integrals

The closed Euclidean ball of radius three is covered by the 343 integer
translates of the unit cube whose lower corners have coordinates -3,...,3.
Periodicity under arbitrary integer translations is derived from the three
unit-coordinate periods. All integrals use the physical Euclidean volume.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Metric
open scoped BigOperators

namespace SingularClosure

noncomputable section

def integerShift (z : Fin 3 → ℤ) : Vec :=
  ∑ i : Fin 3, z i • unitVector i

theorem integerShift_apply (z : Fin 3 → ℤ) (i : Fin 3) :
    integerShift z i = (z i : ℝ) := by
  simp [integerShift, unitVector, Finset.sum_apply, zsmul_eq_mul,
    Pi.single_apply, mul_ite]

theorem spatialPeriodic_integerShift {E : Type*} {f : Vec → E}
    (hp : SpatialPeriodic f) (z : Fin 3 → ℤ) :
    Function.Periodic f (integerShift z) := by
  have hcoord (i : Fin 3) : Function.Periodic f (z i • unitVector i) :=
    (show Function.Periodic f (unitVector i) from fun x => hp x i).zsmul (z i)
  have hsum (s : Finset (Fin 3)) :
      Function.Periodic f (∑ i ∈ s, z i • unitVector i) := by
    induction s using Finset.induction_on with
    | empty => simp [Function.Periodic]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hcoord i).add_period ih
  exact hsum Finset.univ

abbrev PeriodicCoverIndex := Fin 3 → Fin 7

def periodicCoverShift (k : PeriodicCoverIndex) : Vec :=
  integerShift (fun i => (k i : ℕ) - (3 : ℤ))

def periodicCoverCell (k : PeriodicCoverIndex) : Set Vec :=
  (fun x : Vec => x + periodicCoverShift k) '' unitCube

theorem periodicCoverShift_apply (k : PeriodicCoverIndex) (i : Fin 3) :
    periodicCoverShift k i = (k i : ℝ) - 3 := by
  simp [periodicCoverShift, integerShift_apply]

theorem isCompact_periodicCoverCell (k : PeriodicCoverIndex) :
    IsCompact (periodicCoverCell k) :=
  isCompact_unitCube.image (continuous_id.add continuous_const)

theorem periodicCoverCell_integral {f : Vec → ℝ}
    (hp : SpatialPeriodic f) (k : PeriodicCoverIndex) :
    (∫ x in periodicCoverCell k, f x) = ∫ x in unitCube, f x := by
  unfold periodicCoverCell
  rw [(measurePreserving_add_right (volume : Measure Vec) (periodicCoverShift k)).setIntegral_image_emb
      (Homeomorph.addRight (periodicCoverShift k)).measurableEmbedding f unitCube]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (spatialPeriodic_integerShift hp (fun i => (k i : ℕ) - (3 : ℤ)))

theorem closedBall_three_mem_periodicCover (x : Vec)
    (hx : x ∈ closedBall (0 : Vec) 3) :
    ∃ k : PeriodicCoverIndex, x ∈ periodicCoverCell k := by
  have hnorm : ‖x‖ ≤ 3 := by simpa only [mem_closedBall, dist_zero_right] using hx
  have habs (i : Fin 3) : |x i| ≤ 3 := by
    have h := PiLp.norm_apply_le x i
    exact (show |x i| ≤ ‖x‖ by simpa only [Real.norm_eq_abs] using h).trans hnorm
  have hlo (i : Fin 3) : (-3 : ℤ) ≤ ⌊x i⌋ := by
    apply Int.le_floor.mpr
    simpa using (abs_le.mp (habs i)).1
  have hhi (i : Fin 3) : ⌊x i⌋ ≤ (3 : ℤ) := by
    apply Int.floor_le_iff.mpr
    have h := (abs_le.mp (habs i)).2
    norm_num
    linarith
  let k : PeriodicCoverIndex := fun i =>
    ⟨(⌊x i⌋ + 3).toNat, by have := hlo i; have := hhi i; omega⟩
  have hk (i : Fin 3) : periodicCoverShift k i = (⌊x i⌋ : ℝ) := by
    rw [periodicCoverShift_apply]
    have hnonneg : 0 ≤ ⌊x i⌋ + 3 := by have := hlo i; omega
    have hz : ((k i : ℕ) : ℤ) = ⌊x i⌋ + 3 := by
      exact Int.toNat_of_nonneg hnonneg
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at hr
    linarith
  refine ⟨k, x - periodicCoverShift k, ?_, sub_add_cancel x _⟩
  intro i
  change 0 ≤ x i - periodicCoverShift k i ∧ x i - periodicCoverShift k i ≤ 1
  rw [hk]
  constructor
  · exact sub_nonneg.mpr (Int.floor_le (x i))
  · have h := Int.lt_floor_add_one (x i)
    linarith

/-- Uniform finite covering bound, independent of datum, Fourier cutoff and
viscosity. The nonnegative physical integrand is explicitly assumed. -/
theorem periodic_closedBall_three_integral_le (f : Vec → ℝ)
    (hf : Continuous f) (hp : SpatialPeriodic f) (hn : ∀ x, 0 ≤ f x) :
    (∫ x in closedBall (0 : Vec) 3, f x) ≤
      343 * ∫ x in unitCube, f x := by
  classical
  have hbmeas : MeasurableSet (closedBall (0 : Vec) 3) :=
    isClosed_closedBall.measurableSet
  have hbint : Integrable ((closedBall (0 : Vec) 3).indicator f) volume :=
    (integrable_indicator_iff hbmeas).mpr
      (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
  have hcmeas (k : PeriodicCoverIndex) : MeasurableSet (periodicCoverCell k) :=
    (isCompact_periodicCoverCell k).measurableSet
  have hcint (k : PeriodicCoverIndex) :
      Integrable ((periodicCoverCell k).indicator f) volume :=
    (integrable_indicator_iff (hcmeas k)).mpr
      (hf.continuousOn.integrableOn_compact (isCompact_periodicCoverCell k))
  have hsint : Integrable
      (fun x => ∑ k : PeriodicCoverIndex, (periodicCoverCell k).indicator f x)
      volume := integrable_finsetSum Finset.univ (fun k _ => hcint k)
  have hpoint (x : Vec) : (closedBall (0 : Vec) 3).indicator f x ≤
      ∑ k : PeriodicCoverIndex, (periodicCoverCell k).indicator f x := by
    have hnonneg (k : PeriodicCoverIndex) : 0 ≤ (periodicCoverCell k).indicator f x := by
      by_cases hxk : x ∈ periodicCoverCell k <;> simp [hxk, hn x]
    by_cases hxb : x ∈ closedBall (0 : Vec) 3
    · obtain ⟨k, hk⟩ := closedBall_three_mem_periodicCover x hxb
      rw [Set.indicator_of_mem hxb]
      calc
        f x = (periodicCoverCell k).indicator f x := (Set.indicator_of_mem hk f).symm
        _ ≤ ∑ j : PeriodicCoverIndex, (periodicCoverCell j).indicator f x :=
          Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ k)
    · rw [Set.indicator_of_notMem hxb]
      exact Finset.sum_nonneg (fun k _ => hnonneg k)
  have h := integral_mono_ae hbint hsint (Filter.Eventually.of_forall hpoint)
  rw [integral_indicator hbmeas,
    integral_finsetSum Finset.univ (fun k _ => hcint k)] at h
  simp_rw [integral_indicator (hcmeas _), periodicCoverCell_integral hp] at h
  simpa [PeriodicCoverIndex, Fintype.card_pi_const, nsmul_eq_mul] using h

end

end SingularClosure
