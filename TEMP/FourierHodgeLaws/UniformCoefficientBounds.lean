import FourierHodgeLaws.FourierCoefficients
import NSEMaxwell.Spacetime
import NSEMaxwell.PeriodicIntegration

/-!
Uniform summable Fourier majorants on finite nonnegative-time slabs.
Every bound is obtained from the actual joint smoothness hypothesis and
compactness. No uniform Fourier admission is left as a theorem premise.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.HodgeProof

open NSEMaxwell.Classical NSEMaxwell.Spacetime NSEMaxwell.PeriodicIntegration

noncomputable section

theorem compact_velocity_norm_bound (u : Velocity) (hu : SmoothVelocity u) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ unitCube, ‖u t x‖ ≤ C := by
  have hcompact : IsCompact (Icc (0 : ℝ) T ×ˢ unitCube) :=
    isCompact_Icc.prod isCompact_unitCube
  have hsub : Icc (0 : ℝ) T ×ˢ unitCube ⊆ forwardSpacetime := by
    intro z hz
    exact hz.1.1
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hu.continuousOn.mono hsub)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x hx
  exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)

theorem compact_componentL1_bound (u : Velocity) (hu : SmoothVelocity u) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3,
      (∫ x in unitCube, ‖u t x i‖) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := compact_velocity_norm_bound u hu T
  refine ⟨volume.real unitCube * C, by positivity, ?_⟩
  intro t ht i
  have hint : IntegrableOn (fun x : Vec => ‖u t x i‖) unitCube volume :=
    (((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
      (velocity_slice_smooth hu ht.1).continuous).norm).continuousOn.integrableOn_compact
        isCompact_unitCube
  have hconst : IntegrableOn (fun _ : Vec => C) unitCube volume :=
    integrableOn_unitCube_of_continuous continuous_const
  calc
    _ ≤ ∫ _x in unitCube, C := by
      apply integral_mono_ae hint hconst
      exact (ae_restrict_mem isCompact_unitCube.isClosed.measurableSet).mono
        (fun x hx => (PiLp.norm_apply_le (u t x) i).trans (hC t ht x hx))
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

theorem iteratedCoordinateDerivative_trajectory_smooth (u : Velocity)
    (hu : SmoothVelocity u) (j : Fin 3) (m : ℕ) :
    SmoothVelocity (fun t => SingularClosure.iteratedCoordinateDerivative j m (u t)) := by
  induction m with
  | zero => exact hu
  | succ m ih =>
      exact coordinateDerivative_trajectory_smooth ih j

theorem uniform_fourierDecayConstant (u : Velocity) (hu : SmoothVelocity u)
    (T : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      SingularClosure.fourierDecayConstant m (u t) ≤ C := by
  classical
  obtain ⟨C0, hC0non, hC0⟩ := compact_componentL1_bound u hu T
  have hder (j : Fin 3) := compact_componentL1_bound
    (fun t => SingularClosure.iteratedCoordinateDerivative j m (u t))
    (iteratedCoordinateDerivative_trajectory_smooth u hu j m) T
  choose C hCnon hC using hder
  refine ⟨∑ _i : Fin 3, (C0 + ∑ j : Fin 3, C j), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun _ _ =>
      add_nonneg hC0non (Finset.sum_nonneg (fun j _ => hCnon j)))
  · intro t ht
    unfold SingularClosure.fourierDecayConstant
    apply Finset.sum_le_sum
    intro i _
    apply add_le_add (hC0 t ht i)
    apply Finset.sum_le_sum
    intro j _
    exact hC j t ht i

/-- The majorant is independent of time and component on the entire slab. -/
theorem uniform_datumFourierCoeff_moment_bound (u : Velocity)
    (hu : SmoothVelocity u) (hp : PeriodicVelocity u) (T : ℝ) (m : ℕ) :
    ∃ M : Frequency → ℝ, Summable M ∧ (∀ k, 0 ≤ M k) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency, ∀ i : Fin 3,
        ‖SingularClosure.datumFourierCoeff (u t) k i‖ *
          ‖SingularClosure.fourierPhaseCLM k‖ ^ m ≤ M k := by
  obtain ⟨C, hCnon, hC⟩ := uniform_fourierDecayConstant u hu T (2 * (m + 4))
  let A : ℝ := (4 : ℝ) ^ (m + 4) * C
  let P : ℝ := SingularClosure.fourierPhaseWeightConstant
  let M : Frequency → ℝ := fun k =>
    (P ^ m * A) * (SingularClosure.torusSobolevWeight k)⁻¹ ^ 4
  have hAnon : 0 ≤ A := mul_nonneg (by positivity) hCnon
  have hPnon : 0 ≤ P := SingularClosure.fourierPhaseWeightConstant_nonneg
  refine ⟨M, SingularClosure.summable_torusSobolevWeight_inv_four.mul_left (P ^ m * A),
    (fun k => mul_nonneg (mul_nonneg (pow_nonneg hPnon _) hAnon) (by positivity)), ?_⟩
  intro t ht k i
  have hdec : SingularClosure.torusSobolevWeight k ^ (m + 4) *
      ‖SingularClosure.datumFourierCoeff (u t) k i‖ ≤ A := by
    have h := SingularClosure.smooth_datum_sobolev_decay (m + 2) (u t)
      (velocity_slice_smooth hu ht.1) (hp t ht.1) k i
    have hfirst : SingularClosure.torusSobolevWeight k ^ (m + 4) *
        ‖SingularClosure.datumFourierCoeff (u t) k i‖ ≤
        (4 : ℝ) ^ (m + 4) * SingularClosure.fourierDecayConstant (2 * (m + 4)) (u t) := by
      simpa [SingularClosure.smoothDatumDecayConstant, Nat.add_assoc] using h
    exact hfirst.trans (mul_le_mul_of_nonneg_left (hC t ht) (by positivity))
  have hproduct :
      ‖SingularClosure.datumFourierCoeff (u t) k i‖ * SingularClosure.torusSobolevWeight k ^ m =
      (SingularClosure.torusSobolevWeight k ^ (m + 4) *
        ‖SingularClosure.datumFourierCoeff (u t) k i‖) *
        (SingularClosure.torusSobolevWeight k)⁻¹ ^ 4 := by
    rw [pow_add]
    field_simp [(SingularClosure.torusSobolevWeight_pos k).ne'] <;> ring
  calc
    _ ≤ ‖SingularClosure.datumFourierCoeff (u t) k i‖ *
        (P * SingularClosure.torusSobolevWeight k) ^ m :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _)
          (SingularClosure.fourierPhaseCLM_norm_le_weight k) m) (norm_nonneg _)
    _ = P ^ m * (‖SingularClosure.datumFourierCoeff (u t) k i‖ *
        SingularClosure.torusSobolevWeight k ^ m) := by rw [mul_pow]; ring
    _ = P ^ m * ((SingularClosure.torusSobolevWeight k ^ (m + 4) *
        ‖SingularClosure.datumFourierCoeff (u t) k i‖) *
        (SingularClosure.torusSobolevWeight k)⁻¹ ^ 4) := by rw [hproduct]
    _ ≤ P ^ m * (A * (SingularClosure.torusSobolevWeight k)⁻¹ ^ 4) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdec (by positivity)) (pow_nonneg hPnon _)
    _ = M k := by dsimp [M]; ring

theorem scalarLift_trajectory_smooth (f : Pressure) (hf : SmoothPressure f) :
    SmoothVelocity (fun t => scalarLift (f t)) := by
  apply (contDiffOn_piLp 2).2
  intro i
  exact hf

theorem scalarLift_trajectory_periodic (f : Pressure) (hp : PeriodicPressure f) :
    PeriodicVelocity (fun t => scalarLift (f t)) := by
  intro t ht
  exact scalarLift_periodic (f t) (hp t ht)

theorem uniform_scalarCoeff_moment_bound (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f) (T : ℝ) (m : ℕ) :
    ∃ M : Frequency → ℝ, Summable M ∧ (∀ k, 0 ≤ M k) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency,
        ‖scalarCoeff (f t) k‖ * ‖SingularClosure.fourierPhaseCLM k‖ ^ m ≤ M k := by
  obtain ⟨M, hsum, hnon, hM⟩ := uniform_datumFourierCoeff_moment_bound
    (fun t => scalarLift (f t)) (scalarLift_trajectory_smooth f hf)
    (scalarLift_trajectory_periodic f hp) T m
  exact ⟨M, hsum, hnon, fun t ht k => hM t ht k 0⟩

theorem uniform_inverseScalarCoeff_moment_bound (f : Pressure)
    (hf : SmoothPressure f) (hp : PeriodicPressure f) (T : ℝ) (m : ℕ) :
    ∃ M : Frequency → ℝ, Summable M ∧ (∀ k, 0 ≤ M k) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency,
        ‖inverseScalarCoeff (f t) k‖ * ‖SingularClosure.fourierPhaseCLM k‖ ^ m ≤ M k := by
  obtain ⟨M, hsum, hnon, hM⟩ := uniform_scalarCoeff_moment_bound f hf hp T m
  refine ⟨M, hsum, hnon, ?_⟩
  intro t ht k
  have hcoeff : ‖inverseScalarCoeff (f t) k‖ ≤ ‖scalarCoeff (f t) k‖ := by
    rw [inverseScalarCoeff, norm_mul]
    exact (mul_le_mul_of_nonneg_right (inverseLaplacianSymbol_complex_norm_le_one k)
      (norm_nonneg _)).trans_eq (one_mul _)
  exact (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (norm_nonneg _) _)).trans
    (hM t ht k)

end

end NSEMaxwell.HodgeProof
