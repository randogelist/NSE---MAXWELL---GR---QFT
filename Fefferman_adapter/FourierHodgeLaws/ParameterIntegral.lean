import NSEMaxwell.TemporalMean
import NSEMaxwell.AnalyticReduction

/-!
Smooth dependence of the actual cube mean on nonnegative time.
The induction uses the already proved right-derivative integral identity.
No spatial periodicity or Fourier premise occurs in these theorems.
-/

set_option autoImplicit false

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.TemporalMean
open Set MeasureTheory
open scoped ContDiff

noncomputable section

theorem spatialMean_contDiffOn_nat (n : ℕ) (u : Velocity)
    (hu : SmoothVelocity u) :
    ContDiffOn ℝ n (fun t : ℝ => spatialMean (u t)) (Ici (0 : ℝ)) := by
  induction n generalizing u with
  | zero =>
      apply contDiffOn_zero.mpr
      intro t ht
      exact (mean_time_hasDerivWithinAt hu ht).continuousWithinAt
  | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ici 0)]
      refine ⟨?_, by simp, ?_⟩
      · intro t ht
        exact (mean_time_hasDerivWithinAt hu ht).differentiableWithinAt
      · apply (ih (fun t => timeDerivative u t) (timeDerivative_smooth hu)).congr
        intro t ht
        exact mean_time_derivWithin hu ht

theorem spatialMean_contDiffOn (u : Velocity) (hu : SmoothVelocity u) :
    ContDiffOn ℝ ∞ (fun t : ℝ => spatialMean (u t)) (Ici (0 : ℝ)) := by
  rw [contDiffOn_infty]
  intro n
  exact spatialMean_contDiffOn_nat n u hu

theorem spatialMean_scalar_embed (f : ScalarField) :
    spatialMean (fun x : Vec => f x • unitVector 0) 0 = scalarMean f := by
  change (∫ x in unitCube, f x • unitVector 0) 0 = ∫ x in unitCube, f x
  rw [integral_smul_const]
  simp [unitVector, EuclideanSpace.single, PiLp.single_apply]

theorem scalarMean_contDiffOn (f : Pressure) (hf : SmoothPressure f) :
    ContDiffOn ℝ ∞ (fun t : ℝ => scalarMean (f t)) (Ici (0 : ℝ)) := by
  let u : Velocity := fun t x => f t x • unitVector 0
  have hu : SmoothVelocity u := hf.smul contDiffOn_const
  have hm := spatialMean_contDiffOn u hu
  have hc : ContDiffOn ℝ ∞ (fun t : ℝ => spatialMean (u t) 0) (Ici (0 : ℝ)) :=
    (contDiffOn_piLp 2).mp hm 0
  apply hc.congr
  intro t ht
  exact (spatialMean_scalar_embed (f t)).symm

theorem spatialMean_trajectory_smooth (u : Velocity) (hu : SmoothVelocity u) :
    SmoothVelocity (fun t _ => spatialMean (u t)) := by
  exact (spatialMean_contDiffOn u hu).comp contDiffOn_fst (fun _ hz => hz)

theorem scalarMean_trajectory_smooth (f : Pressure) (hf : SmoothPressure f) :
    SmoothPressure (fun t _ => scalarMean (f t)) := by
  exact (scalarMean_contDiffOn f hf).comp contDiffOn_fst (fun _ hz => hz)

theorem kineticMean_trajectory_smooth (u : Velocity) (hu : SmoothVelocity u) :
    SmoothPressure (fun t _ => scalarMean (fun x => ‖u t x‖ ^ 2)) := by
  exact scalarMean_trajectory_smooth _ (hu.norm_sq ℝ)

end

end NSEMaxwell.HodgeProof
