import NSEMaxwell.PeriodicIntegration

/-!
# Exact periodicity of the concrete Fourier operators

These declarations concern the total cosine-series operators from Classical.
They require no summability premise: translation by an integer coordinate
period preserves every individual summand before any infinite sum is taken.
No inversion, convergence, or differentiability theorem is inferred from these
identities.
-/

set_option autoImplicit false

namespace NSEMaxwell.FourierPeriodic

open NSEMaxwell.Classical NSEMaxwell.PeriodicIntegration
open scoped BigOperators

noncomputable section

theorem cosineKernel_add_unit_left (k : Frequency) (x y : Vec) (i : Fin 3) :
    cosineKernel k (x + unitVector i) y = cosineKernel k x y := by
  have hsum :
      (∑ j : Fin 3, (k j : ℝ) * ((x + unitVector i) j - y j)) =
        (∑ j : Fin 3, (k j : ℝ) * (x j - y j)) + (k i : ℝ) := by
    calc
      (∑ j : Fin 3, (k j : ℝ) * ((x + unitVector i) j - y j)) =
          ∑ j : Fin 3,
            ((k j : ℝ) * (x j - y j) + (k j : ℝ) * unitVector i j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [PiLp.add_apply]
        ring
      _ = (∑ j : Fin 3, (k j : ℝ) * (x j - y j)) + (k i : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [unitVector, PiLp.single_apply, mul_ite]
  unfold cosineKernel
  rw [hsum]
  have hphase :
      2 * Real.pi * ((∑ j : Fin 3, (k j : ℝ) * (x j - y j)) + (k i : ℝ)) =
        2 * Real.pi * (∑ j : Fin 3, (k j : ℝ) * (x j - y j)) +
          (k i : ℝ) * (2 * Real.pi) := by ring
  rw [hphase]
  exact Real.cos_add_int_mul_two_pi _ _

theorem cosineKernel_symm (k : Frequency) (x y : Vec) :
    cosineKernel k x y = cosineKernel k y x := by
  have hphase :
      2 * Real.pi * (∑ i : Fin 3, (k i : ℝ) * (x i - y i)) =
        -(2 * Real.pi * (∑ i : Fin 3, (k i : ℝ) * (y i - x i))) := by
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold cosineKernel
  rw [hphase, Real.cos_neg]

theorem cosineKernel_add_unit_right (k : Frequency) (x y : Vec) (i : Fin 3) :
    cosineKernel k x (y + unitVector i) = cosineKernel k x y := by
  rw [cosineKernel_symm k x (y + unitVector i),
    cosineKernel_add_unit_left, cosineKernel_symm]

/-- Every total vector inverse-Laplacian output is spatially periodic. -/
theorem vectorL_periodic (a : Field) : SpatialPeriodic (vectorL a) := by
  intro x i
  simp only [vectorL, cosineKernel_add_unit_left]

/-- Every total scalar inverse-Laplacian output is spatially periodic. -/
theorem scalarL_periodic (f : ScalarField) : SpatialPeriodic (scalarL f) := by
  intro x i
  simp only [scalarL, cosineKernel_add_unit_left]

theorem K_periodic (B : Field) : SpatialPeriodic (K B) :=
  spatialCurl_periodic (vectorL_periodic B)

theorem U_periodic (m : Vec) (B : Field) : SpatialPeriodic (U m B) := by
  intro x i
  simp only [U, K_periodic B x i]

theorem G_periodic (ν : ℝ) (m : Vec) {B : Field} (hB : SpatialPeriodic B) :
    SpatialPeriodic (G ν m B) := by
  intro x i
  simp only [G, hB x i, U_periodic m B x i, spatialCurl_periodic hB x i]

theorem V_periodic (ν : ℝ) (m : Vec) {B : Field} (hB : SpatialPeriodic B) :
    SpatialPeriodic (V ν m B) := by
  intro x i
  simp only [V, spatialCurl_periodic (G_periodic ν m hB) x i]

theorem Q_periodic (ν : ℝ) (m : Vec) {B : Field} (hB : SpatialPeriodic B) :
    SpatialPeriodic (Q ν m B) :=
  divergence_periodic (G_periodic ν m hB)

theorem DG_periodic (ν : ℝ) (m : Vec) {B h : Field}
    (hB : SpatialPeriodic B) (hh : SpatialPeriodic h) :
    SpatialPeriodic (DG ν m B h) := by
  intro x i
  simp only [DG, hB x i, hh x i, U_periodic m B x i,
    K_periodic h x i, spatialCurl_periodic hh x i]

theorem current_periodic (ν c : ℝ) (m : Vec) {B : Field}
    (hB : SpatialPeriodic B) : SpatialPeriodic (current ν c m B) := by
  intro x i
  simp only [current, spatialCurl_periodic hB x i,
    DG_periodic ν m hB (V_periodic ν m hB) x i]

/-- Periodicity of the canonical pressure does not require a convergence hypothesis. -/
theorem canonicalPressure_periodic (ν : ℝ) (m : Vec) (B : Field) :
    SpatialPeriodic (canonicalPressure ν m B) := by
  intro x i
  simp only [canonicalPressure, scalarL_periodic (Q ν m B) x i, U_periodic m B x i]

theorem canonicalVelocity_periodic (m : Vec) (B : Velocity) :
    PeriodicVelocity (canonicalVelocity m B) := by
  intro t _
  exact U_periodic m (B t)

theorem canonicalElectric_periodic (ν : ℝ) (m : Vec) {B : Velocity}
    (hB : PeriodicVelocity B) : PeriodicVelocity (canonicalElectric ν m B) := by
  intro t ht
  exact G_periodic ν m (hB t ht)

theorem canonicalCharge_periodic (ν : ℝ) (m : Vec) {B : Velocity}
    (hB : PeriodicVelocity B) : PeriodicPressure (canonicalCharge ν m B) := by
  intro t ht
  exact Q_periodic ν m (hB t ht)

theorem canonicalCurrent_periodic (ν c : ℝ) (m : Vec) {B : Velocity}
    (hB : PeriodicVelocity B) : PeriodicVelocity (canonicalCurrent ν c m B) := by
  intro t ht
  exact current_periodic ν c m (hB t ht)

theorem canonicalPressureTrajectory_periodic (ν : ℝ) (m : Vec) (B : Velocity) :
    PeriodicPressure (canonicalPressureTrajectory ν m B) := by
  intro t _
  exact canonicalPressure_periodic ν m (B t)

end

end NSEMaxwell.FourierPeriodic
