import QuantumAdapter.RegularityContracts
import SingularClosure.SmoothDatumSobolev

/-!
# Exact finite Fourier norm and initial-projection identities

The phase, coefficients and energies are the existing arbitrary-mean objects.
The weighted Euclidean linear map realizes the exact native H3 square root.
The native smooth-periodic Fourier summability theorem discharges the uniform
initial-projection contract, retaining the zero mode and every full shell.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace QuantumAdapter.Assembly

noncomputable section

open SingularClosure

theorem sum_fullModes_eq_sum_coordinates (N : ℕ) (f : Frequency → Fin 3 → ℝ) :
    (∑ k ∈ fullModes N, ∑ i : Fin 3, f k i) =
      ∑ ki : PhaseIndex N, f ki.1.val ki.2 := by
  rw [Fintype.sum_prod_type]
  change (∑ k ∈ fullModes N, ∑ i : Fin 3, f k i) =
    ∑ k : Mode N, ∑ i : Fin 3, f k.val i
  exact (Finset.sum_coe_sort (fullModes N) (fun k => ∑ i : Fin 3, f k i)).symm

theorem phaseCoeff_mode (N : ℕ) (q : Phase N) (ki : PhaseIndex N) :
    phaseCoeff q ki.1.val ki.2 = q.val ki := by
  simp [phaseCoeff, extendCoeff, ki.1.property]

theorem energy0_eq_norm_sq (N : ℕ) (q : Phase N) :
    energy0 N q = ‖q‖ ^ 2 := by
  rw [energy0, sum_fullModes_eq_sum_coordinates]
  change _ = ‖q.val‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro ki hki
  rw [phaseCoeff_mode, Complex.normSq_eq_norm_sq]

def weightedCoordinates (N : ℕ) : Phase N →ₗ[ℝ] AmbientPhase N where
  toFun q := WithLp.toLp 2 (fun ki : PhaseIndex N =>
    Real.sqrt (h3Weight ki.1.val) • q.val ki)
  map_add' := by
    intro q r
    ext ki
    exact smul_add (Real.sqrt (h3Weight ki.1.val)) (q.val ki) (r.val ki)
  map_smul' := by
    intro a q
    ext ki
    change Real.sqrt (h3Weight ki.1.val) • (a • q.val ki) =
      a • (Real.sqrt (h3Weight ki.1.val) • q.val ki)
    simp only [smul_smul]
    congr 1
    ring

@[simp]
theorem weightedCoordinates_apply (N : ℕ) (q : Phase N) (ki : PhaseIndex N) :
    weightedCoordinates N q ki = Real.sqrt (h3Weight ki.1.val) • q.val ki := rfl

theorem continuous_weightedCoordinates (N : ℕ) : Continuous (weightedCoordinates N) :=
  (weightedCoordinates N).continuous_of_finiteDimensional

theorem weightedCoordinates_norm_sq (N : ℕ) (q : Phase N) :
    ‖weightedCoordinates N q‖ ^ 2 = energy3 N q := by
  rw [EuclideanSpace.norm_sq_eq, energy3, sum_fullModes_eq_sum_coordinates]
  apply Finset.sum_congr rfl
  intro ki hki
  rw [weightedCoordinates_apply, phaseCoeff_mode]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (h3Weight_pos ki.1.val).le, Complex.normSq_eq_norm_sq]

theorem sqrt_energy3_eq_norm (N : ℕ) (q : Phase N) :
    Real.sqrt (energy3 N q) = ‖weightedCoordinates N q‖ := by
  rw [← weightedCoordinates_norm_sq]
  exact Real.sqrt_sq (norm_nonneg _)

theorem continuous_energy3 (N : ℕ) : Continuous (energy3 N) := by
  have h : Continuous (fun q : Phase N => ‖weightedCoordinates N q‖ ^ 2) :=
    (continuous_weightedCoordinates N).norm.pow 2
  simpa only [weightedCoordinates_norm_sq] using h

theorem continuous_sqrt_energy3 (N : ℕ) :
    Continuous (fun q : Phase N => Real.sqrt (energy3 N q)) := by
  simpa only [sqrt_energy3_eq_norm] using (continuous_weightedCoordinates N).norm

theorem sqrt_energy3_add_le (N : ℕ) (q r : Phase N) :
    Real.sqrt (energy3 N (q + r)) ≤
      Real.sqrt (energy3 N q) + Real.sqrt (energy3 N r) := by
  simp only [sqrt_energy3_eq_norm, map_add]
  exact norm_add_le _ _

theorem sqrt_energy3_sub_le (N : ℕ) (q r : Phase N) :
    Real.sqrt (energy3 N (q - r)) ≤
      Real.sqrt (energy3 N q) + Real.sqrt (energy3 N r) := by
  simp only [sqrt_energy3_eq_norm, map_sub]
  exact norm_sub_le _ _

theorem sqrt_energy3_le_add (N : ℕ) (q r : Phase N) :
    Real.sqrt (energy3 N q) ≤
      Real.sqrt (energy3 N (q - r)) + Real.sqrt (energy3 N r) := by
  simpa only [sub_add_cancel] using sqrt_energy3_add_le N (q - r) r

theorem abs_sqrt_energy3_sub_le (N : ℕ) (q r : Phase N) :
    |Real.sqrt (energy3 N q) - Real.sqrt (energy3 N r)| ≤
      Real.sqrt (energy3 N (q - r)) := by
  simp only [sqrt_energy3_eq_norm, map_sub]
  exact abs_norm_sub_norm_le _ _

def cutoffLambda (N : ℕ) : ℝ := 4 * Real.pi ^ 2 * (N : ℝ) ^ 2

def cutoffWeight (N : ℕ) : ℝ := (1 + cutoffLambda N) ^ 3

theorem cutoffLambda_nonneg (N : ℕ) : 0 ≤ cutoffLambda N := by
  unfold cutoffLambda
  positivity

theorem cutoffWeight_pos (N : ℕ) : 0 < cutoffWeight N := by
  have h := cutoffLambda_nonneg N
  unfold cutoffWeight
  positivity

theorem laplaceSymbol_le_cutoffLambda (N : ℕ) (k : Frequency)
    (hk : k ∈ fullModes N) : laplaceSymbol k ≤ cutoffLambda N := by
  rcases Finset.mem_insert.mp hk with hk | hk
  · subst k
    simpa [laplaceSymbol, galerkinFreqSq] using cutoffLambda_nonneg N
  · have hsq : galerkinFreqSq k ≤ (N : ℤ) ^ 2 :=
      ((mem_cutoffModes_iff N k).mp hk).2.2
    have hsqR : (galerkinFreqSq k : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast hsq
    have h := mul_le_mul_of_nonneg_left hsqR (sq_nonneg (2 * Real.pi))
    simpa only [laplaceSymbol, cutoffLambda, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num]
      using h

theorem one_le_h3Weight (k : Frequency) : 1 ≤ h3Weight k := by
  have h := laplaceSymbol_nonneg k
  have hsq := sq_nonneg (laplaceSymbol k)
  have hcube := mul_nonneg h hsq
  unfold h3Weight
  nlinarith

theorem h3Weight_le_cutoffWeight (N : ℕ) (k : Frequency)
    (hk : k ∈ fullModes N) : h3Weight k ≤ cutoffWeight N := by
  have h := laplaceSymbol_le_cutoffLambda N k hk
  have hnonneg := laplaceSymbol_nonneg k
  unfold h3Weight cutoffWeight
  gcongr <;> linarith

theorem energy0_le_energy3 (N : ℕ) (q : Phase N) :
    energy0 N q ≤ energy3 N q := by
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sum_le_sum
  intro i hi
  have hnorm : 0 ≤ Complex.normSq (phaseCoeff q k i) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_nonneg _
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_h3Weight k) hnorm

theorem energy3_le_cutoffWeight_mul_energy0 (N : ℕ) (q : Phase N) :
    energy3 N q ≤ cutoffWeight N * energy0 N q := by
  unfold energy3 energy0
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hnorm : 0 ≤ Complex.normSq (phaseCoeff q k i) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_nonneg _
  exact mul_le_mul_of_nonneg_right (h3Weight_le_cutoffWeight N k hk) hnorm

theorem dissipation_le_cutoffLambda_mul_energy0 (N : ℕ) (q : Phase N) :
    dissipation N q ≤ cutoffLambda N * energy0 N q := by
  unfold dissipation energy0
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hnorm : 0 ≤ Complex.normSq (phaseCoeff q k i) := by
    rw [Complex.normSq_eq_norm_sq]
    exact sq_nonneg _
  exact mul_le_mul_of_nonneg_right (laplaceSymbol_le_cutoffLambda N k hk) hnorm

theorem cutoffSobolevFactor_sq (N : ℕ) :
    cutoffSobolevFactor N ^ 2 = cutoffWeight N := by
  unfold cutoffSobolevFactor cutoffWeight cutoffLambda
  rw [Real.sq_sqrt]
  positivity

theorem energy3_le_cutoffSobolevFactor_sq_mul_norm_sq (N : ℕ) (q : Phase N) :
    energy3 N q ≤ cutoffSobolevFactor N ^ 2 * ‖q‖ ^ 2 := by
  rw [cutoffSobolevFactor_sq, ← energy0_eq_norm_sq]
  exact energy3_le_cutoffWeight_mul_energy0 N q

theorem norm_le_sqrt_energy3 (N : ℕ) (q : Phase N) :
    ‖q‖ ≤ Real.sqrt (energy3 N q) := by
  have h := Real.sqrt_le_sqrt (energy0_le_energy3 N q)
  simpa only [energy0_eq_norm_sq, Real.sqrt_sq (norm_nonneg q)] using h

theorem sqrt_energy3_le_cutoffSobolevFactor_mul_norm (N : ℕ) (q : Phase N) :
    Real.sqrt (energy3 N q) ≤ cutoffSobolevFactor N * ‖q‖ := by
  have h := Real.sqrt_le_sqrt (energy3_le_cutoffSobolevFactor_sq_mul_norm_sq N q)
  rw [← mul_pow, Real.sqrt_sq (mul_nonneg (cutoffSobolevFactor_pos N).le
    (norm_nonneg q))] at h
  exact h

theorem fullModes_mono {N M : ℕ} (hNM : N ≤ M) : fullModes N ⊆ fullModes M := by
  intro k hk
  rcases Finset.mem_insert.mp hk with hk | hk
  · subst k
    exact zero_mem_fullModes M
  · apply Finset.mem_insert_of_mem
    rcases (mem_cutoffModes_iff N k).mp hk with ⟨hcoord, hne, hsq⟩
    apply (mem_cutoffModes_iff M k).mpr
    have hNMZ : (N : ℤ) ≤ (M : ℤ) := by exact_mod_cast hNM
    refine ⟨?_, hne, ?_⟩
    · intro i
      exact ⟨le_trans (neg_le_neg hNMZ) (hcoord i).1,
        le_trans (hcoord i).2 hNMZ⟩
    · have hN : (0 : ℤ) ≤ N := by exact_mod_cast Nat.zero_le N
      have hM : (0 : ℤ) ≤ M := by exact_mod_cast Nat.zero_le M
      nlinarith

def initialEnergyDensity (a : Field) (k : Frequency) : ℝ :=
  ∑ i : Fin 3, h3Weight k * Complex.normSq (datumFourierCoeff a k i)

theorem initialEnergyDensity_nonneg (a : Field) (k : Frequency) :
    0 ≤ initialEnergyDensity a k := by
  apply Finset.sum_nonneg
  intro i hi
  rw [Complex.normSq_eq_norm_sq]
  exact mul_nonneg (h3Weight_pos k).le (sq_nonneg _)

theorem initialPhaseData_energy3_eq_sum (N : ℕ)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a) :
    energy3 N (initialPhaseData N a ha) =
      ∑ k ∈ fullModes N, initialEnergyDensity a k := by
  unfold energy3 initialEnergyDensity
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z : ℂ => h3Weight k * Complex.normSq z)
    ((initialPhase_coeff N a ha.smooth ha.periodic ha.divergence_free k i).trans
      (if_pos hk))

theorem initialPhaseData_energy3_mono {N M : ℕ} (hNM : N ≤ M)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a) :
    energy3 N (initialPhaseData N a ha) ≤ energy3 M (initialPhaseData M a ha) := by
  rw [initialPhaseData_energy3_eq_sum, initialPhaseData_energy3_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fullModes_mono hNM)
    (fun k hk hnot => initialEnergyDensity_nonneg a k)

/-- One coordinate of the native periodic integration-by-parts identity. -/
theorem integral_unitCube_fderiv_eq_zero (f : Vec → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (j : Fin 3) :
    (∫ x in unitCube, fderiv ℝ f x (unitVector j)) = 0 :=
  SingularClosure.integral_unitCube_directionalDerivative_eq_zero f hf hp j

/-- The Fourier component and the derivative direction are independent. -/
theorem datumFourierIntegrand_fderiv_coordinate {a : Field}
    (ha : Differentiable ℝ a) (k : Frequency) (i j : Fin 3) (x : Vec) :
    fderiv ℝ (datumFourierIntegrand a k i) x (unitVector j) =
      star (fourierCharacter k x) * (coordinateDerivative a j x i : ℂ) -
        derivativeSymbol j k * datumFourierIntegrand a k i x :=
  SingularClosure.datumFourierIntegrand_directionalDerivative ha k i j x

/-- Actual smooth periodic coefficient differentiation, without a mean restriction. -/
theorem datumFourierCoeff_coordinateDerivative (a : Field)
    (hs : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (k : Frequency) (i j : Fin 3) :
    datumFourierCoeff (coordinateDerivative a j) k i =
      derivativeSymbol j k * datumFourierCoeff a k i := by
  rw [SingularClosure.datumFourierCoeff_coordinateDerivative j a hs hp]
  rfl

/-- The native H3 energy and the source Fourier Sobolev space have exactly the same weight. -/
theorem h3Weight_eq_torusSobolevWeight_cube_sq (k : Frequency) :
    h3Weight k = (torusSobolevWeight k ^ 3) ^ 2 := by
  have hs : torusSobolevWeight k ^ 2 = 1 + laplaceSymbol k := by
    change Real.sqrt (1 + laplaceSymbol k) ^ 2 = 1 + laplaceSymbol k
    exact Real.sq_sqrt (by linarith [laplaceSymbol_nonneg k])
  calc
    _ = (torusSobolevWeight k ^ 2) ^ 3 :=
      congrArg (fun r : ℝ => r ^ 3) hs.symm
    _ = _ := by ring

theorem h3Coeff_eq_sobolevWeightedCoeff_sq (c : FourierCoeff) (k : Frequency)
    (i : Fin 3) :
    h3Weight k * Complex.normSq (c k i) =
      ‖sobolevWeightedCoeff 3 c (k, i)‖ ^ 2 := by
  rw [h3Weight_eq_torusSobolevWeight_cube_sq, Complex.normSq_eq_norm_sq]
  simp only [sobolevWeightedCoeff, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (torusSobolevWeight_pos k), mul_pow]

/-- A cutoff-independent, explicitly constructed bound from smooth datum derivatives. -/
def initialProjectionMajorant (a : Field) : ℝ :=
  3 * smoothDatumDecayConstant 3 a ^ 2 *
    ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4

theorem initialProjectionMajorant_nonneg (a : Field) :
    0 ≤ initialProjectionMajorant a := by
  unfold initialProjectionMajorant
  positivity

theorem initialEnergyDensity_le (a : Field) (hs : ContDiff ℝ ∞ a)
    (hp : SpatialPeriodic a) (k : Frequency) :
    initialEnergyDensity a k ≤
      3 * smoothDatumDecayConstant 3 a ^ 2 * (torusSobolevWeight k)⁻¹ ^ 4 := by
  calc
    _ ≤ ∑ i : Fin 3, smoothDatumDecayConstant 3 a ^ 2 *
        (torusSobolevWeight k)⁻¹ ^ 4 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [h3Coeff_eq_sobolevWeightedCoeff_sq]
      exact smooth_datum_weightedCoeff_sq_le 3 a hs hp (k, i)
    _ = _ := by simp; ring

/-- The exact full-shell initial energies are uniformly bounded, including arbitrary means. -/
theorem initialPhaseData_energy3_le_majorant (N : ℕ)
    (a : NSEMaxwell.Classical.Field) (ha : NSEMaxwell.Classical.Data a) :
    energy3 N (initialPhaseData N a ha) ≤ initialProjectionMajorant a := by
  rw [initialPhaseData_energy3_eq_sum]
  calc
    _ ≤ ∑ k ∈ fullModes N, 3 * smoothDatumDecayConstant 3 a ^ 2 *
        (torusSobolevWeight k)⁻¹ ^ 4 :=
      Finset.sum_le_sum (fun k hk => initialEnergyDensity_le a ha.smooth ha.periodic k)
    _ = 3 * smoothDatumDecayConstant 3 a ^ 2 *
        ∑ k ∈ fullModes N, (torusSobolevWeight k)⁻¹ ^ 4 := by
      rw [Finset.mul_sum]
    _ ≤ initialProjectionMajorant a := by
      apply mul_le_mul_of_nonneg_left
      · exact Summable.sum_le_tsum _ (fun k _ => by positivity)
          summable_torusSobolevWeight_inv_four
      · positivity

/-- The actual analytic initial-projection premise is discharged. -/
theorem initialProjectionBounds : InitialProjectionBounds := by
  intro a ha
  refine ⟨Real.sqrt (initialProjectionMajorant a), Real.sqrt_nonneg _, ?_⟩
  intro N hN
  rw [Real.sq_sqrt (initialProjectionMajorant_nonneg a)]
  exact initialPhaseData_energy3_le_majorant N a ha

/-- The full mean contributes no physical derivative. -/
theorem synthesis_coordinateDerivative (N : ℕ) (q : Phase N) (j : Fin 3) :
    coordinateDerivative (synthesis q) j =
      finiteSynthesis N (spectralMultiplier (derivativeSymbol j) (phaseCoeff q)) := by
  rw [← finiteSynthesis_coordinateDerivative]
  funext x
  unfold coordinateDerivative
  have hd := ((finiteSynthesis_contDiff N (phaseCoeff q)).differentiable
    (by simp) x).hasFDerivAt
  have hs : HasFDerivAt (fun y => meanVector q + finiteSynthesis N (phaseCoeff q) y)
      (fderiv ℝ (finiteSynthesis N (phaseCoeff q)) x) x := by
    exact (hasFDerivAt_const_add_iff (meanVector q)).mpr hd
  rw [synthesis_eq_mean_add_source, hs.fderiv]

/-- Each physical derivative multiplier is bounded by the exact Sobolev weight. -/
theorem derivativeSymbol_norm_le_torusSobolevWeight (j : Fin 3) (k : Frequency) :
    ‖derivativeSymbol j k‖ ≤ torusSobolevWeight k := by
  have hi : (k j : ℝ) ^ 2 ≤ (galerkinFreqSq k : ℝ) := by
    unfold galerkinFreqSq
    push_cast
    exact Finset.single_le_sum (fun l _ => sq_nonneg (k l : ℝ)) (Finset.mem_univ j)
  have hs : ‖derivativeSymbol j k‖ ^ 2 ≤ laplaceSymbol k := by
    rw [derivativeSymbol_norm, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left hi (sq_nonneg _)
  have hw : torusSobolevWeight k ^ 2 = 1 + laplaceSymbol k := by
    change Real.sqrt (1 + laplaceSymbol k) ^ 2 = 1 + laplaceSymbol k
    exact Real.sq_sqrt (by linarith [laplaceSymbol_nonneg k])
  nlinarith [torusSobolevWeight_pos k, norm_nonneg (derivativeSymbol j k)]

theorem derivative_weighted_sq_le_h3Coeff (c : FourierCoeff) (k : Frequency)
    (i j : Fin 3) :
    (torusSobolevWeight k ^ 2 * ‖derivativeSymbol j k * c k i‖) ^ 2 ≤
      h3Weight k * Complex.normSq (c k i) := by
  have h : torusSobolevWeight k ^ 2 * ‖derivativeSymbol j k * c k i‖ ≤
      torusSobolevWeight k ^ 3 * ‖c k i‖ := by
    rw [norm_mul]
    calc
      _ ≤ torusSobolevWeight k ^ 2 * (torusSobolevWeight k * ‖c k i‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (derivativeSymbol_norm_le_torusSobolevWeight j k) (norm_nonneg _))
          (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ (torusSobolevWeight k ^ 3 * ‖c k i‖) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (norm_nonneg _)) h 2
    _ = _ := by
      rw [mul_pow, ← h3Weight_eq_torusSobolevWeight_cube_sq,
        Complex.normSq_eq_norm_sq]

theorem finiteSynthesis_component_norm_le (N : ℕ) (c : FourierCoeff)
    (x : Vec) (i : Fin 3) :
    ‖finiteSynthesis N c x i‖ ≤ ∑ k ∈ cutoffModes N, ‖c k i‖ := by
  change ‖(∑ k ∈ cutoffModes N, fourierCharacter k x * c k i).re‖ ≤ _
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ‖∑ k ∈ cutoffModes N, fourierCharacter k x * c k i‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ k ∈ cutoffModes N, ‖fourierCharacter k x * c k i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, fourierCharacter_norm, one_mul]

theorem derivative_component_sq_le (N : ℕ) (q : Phase N)
    (x : Vec) (i j : Fin 3) :
    ‖coordinateDerivative (synthesis q) j x i‖ ^ 2 ≤
      latticeSobolevConstant * energy3 N q := by
  rw [synthesis_coordinateDerivative]
  have hcomponent := finiteSynthesis_component_norm_le N
    (spectralMultiplier (derivativeSymbol j) (phaseCoeff q)) x i
  have hCS := finite_l1_sq_le_H2_sq (cutoffModes N)
    (fun k => derivativeSymbol j k * phaseCoeff q k i)
  have hsum : (∑ k ∈ cutoffModes N,
      (torusSobolevWeight k ^ 2 * ‖derivativeSymbol j k * phaseCoeff q k i‖) ^ 2) ≤
      energy3 N q := by
    calc
      _ ≤ ∑ k ∈ cutoffModes N, h3Weight k * Complex.normSq (phaseCoeff q k i) :=
        Finset.sum_le_sum (fun k hk => derivative_weighted_sq_le_h3Coeff _ k i j)
      _ ≤ ∑ k ∈ cutoffModes N, ∑ l : Fin 3,
          h3Weight k * Complex.normSq (phaseCoeff q k l) := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun l : Fin 3 => h3Weight k * Complex.normSq (phaseCoeff q k l))
          (fun l hl => by
            rw [Complex.normSq_eq_norm_sq]
            exact mul_nonneg (h3Weight_pos k).le (sq_nonneg _))
          (Finset.mem_univ i)
      _ ≤ energy3 N q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_insert 0 (cutoffModes N)
        · intro k hk hnot
          apply Finset.sum_nonneg
          intro l hl
          rw [Complex.normSq_eq_norm_sq]
          exact mul_nonneg (h3Weight_pos k).le (sq_nonneg _)
  exact (pow_le_pow_left₀ (norm_nonneg _) hcomponent 2).trans
    (hCS.trans (mul_le_mul_of_nonneg_left hsum latticeSobolevConstant_pos.le))

/-- A dimension-dependent constant, independent of the Fourier cutoff and datum. -/
def gradientEmbeddingConstant : ℝ := 3 * Real.sqrt latticeSobolevConstant

theorem gradientEmbeddingConstant_pos : 0 < gradientEmbeddingConstant := by
  have h := latticeSobolevConstant_pos
  unfold gradientEmbeddingConstant
  positivity

theorem gradientEmbeddingConstant_sq :
    gradientEmbeddingConstant ^ 2 = 9 * latticeSobolevConstant := by
  unfold gradientEmbeddingConstant
  rw [mul_pow, Real.sq_sqrt latticeSobolevConstant_pos.le]
  norm_num

theorem gradientSquare_nonneg (N : ℕ) (q : Phase N) (x : Vec) :
    0 ≤ gradientSquare q x :=
  Finset.sum_nonneg (fun j hj => sq_nonneg _)

theorem gradientSquare_le_energy3 (N : ℕ) (q : Phase N) (x : Vec) :
    gradientSquare q x ≤ 9 * latticeSobolevConstant * energy3 N q := by
  unfold gradientSquare
  simp_rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ j : Fin 3, ∑ i : Fin 3, latticeSobolevConstant * energy3 N q := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum (fun i hi => derivative_component_sq_le N q x i j)
    _ = _ := by simp; ring

theorem sqrt_gradientSquare_le (N : ℕ) (q : Phase N) (x : Vec) :
    Real.sqrt (gradientSquare q x) ≤
      gradientEmbeddingConstant * Real.sqrt (energy3 N q) := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg gradientEmbeddingConstant_pos.le (Real.sqrt_nonneg _), ?_⟩
  rw [mul_pow, Real.sq_sqrt (energy3_nonneg N q), gradientEmbeddingConstant_sq]
  exact gradientSquare_le_energy3 N q x

theorem gradientObservable_range_bddAbove (N : ℕ) (q : Phase N) :
    BddAbove (Set.range (fun x : Vec => Real.sqrt (gradientSquare q x))) := by
  refine ⟨gradientEmbeddingConstant * Real.sqrt (energy3 N q), ?_⟩
  rintro y ⟨x, rfl⟩
  exact sqrt_gradientSquare_le N q x

/-- The literal spatial supremum is finite and nonnegative. -/
theorem gradientObservable_nonneg (N : ℕ) (q : Phase N) :
    0 ≤ gradientObservable q := by
  exact (Real.sqrt_nonneg (gradientSquare q 0)).trans
    (le_csSup (gradientObservable_range_bddAbove N q) (Set.mem_range_self 0))

/-- Actual cutoff-independent H3 to W1-infinity embedding for the native supremum. -/
theorem gradientObservable_le_sqrt_energy3 (N : ℕ) (q : Phase N) :
    gradientObservable q ≤ gradientEmbeddingConstant * Real.sqrt (energy3 N q) := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨x, rfl⟩
  exact sqrt_gradientSquare_le N q x

theorem phaseCoeff_add (N : ℕ) (q r : Phase N) :
    phaseCoeff (q + r) = phaseCoeff q + phaseCoeff r :=
  extendCoeff_add q.val r.val

theorem phaseCoeff_smul (N : ℕ) (a : ℝ) (q : Phase N) :
    phaseCoeff (a • q) = a • phaseCoeff q :=
  extendCoeff_real_smul a q.val

/-- Actual gradient matrix, with its Euclidean Frobenius norm. -/
def gradientCoordinates (N : ℕ) (x : Vec) :
    Phase N →ₗ[ℝ] EuclideanSpace ℝ (Fin 3 × Fin 3) where
  toFun q := WithLp.toLp 2 (fun ji =>
    (∑ k ∈ cutoffModes N, fourierCharacter k x *
      (derivativeSymbol ji.1 k * phaseCoeff q k ji.2)).re)
  map_add' := by
    intro q r
    ext ji
    change (∑ k ∈ cutoffModes N, fourierCharacter k x *
      (derivativeSymbol ji.1 k * phaseCoeff (q + r) k ji.2)).re = _
    simp [phaseCoeff_add, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a q
    ext ji
    change (∑ k ∈ cutoffModes N, fourierCharacter k x *
      (derivativeSymbol ji.1 k * phaseCoeff (a • q) k ji.2)).re =
      a * (∑ k ∈ cutoffModes N, fourierCharacter k x *
        (derivativeSymbol ji.1 k * phaseCoeff q k ji.2)).re
    rw [phaseCoeff_smul]
    change (∑ k ∈ cutoffModes N, fourierCharacter k x *
      (derivativeSymbol ji.1 k * ((a : ℂ) * phaseCoeff q k ji.2))).re = _
    calc
      _ = ((a : ℂ) * ∑ k ∈ cutoffModes N, fourierCharacter k x *
          (derivativeSymbol ji.1 k * phaseCoeff q k ji.2)).re := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by simp

@[simp]
theorem gradientCoordinates_apply (N : ℕ) (q : Phase N) (x : Vec)
    (ji : Fin 3 × Fin 3) :
    gradientCoordinates N x q ji = coordinateDerivative (synthesis q) ji.1 x ji.2 := by
  rw [synthesis_coordinateDerivative]
  rfl

theorem gradientCoordinates_norm_sq (N : ℕ) (q : Phase N) (x : Vec) :
    ‖gradientCoordinates N x q‖ ^ 2 = gradientSquare q x := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  unfold gradientSquare
  simp_rw [EuclideanSpace.norm_sq_eq, gradientCoordinates_apply]

theorem sqrt_gradientSquare_eq_norm (N : ℕ) (q : Phase N) (x : Vec) :
    Real.sqrt (gradientSquare q x) = ‖gradientCoordinates N x q‖ := by
  rw [← gradientCoordinates_norm_sq]
  exact Real.sqrt_sq (norm_nonneg _)

theorem gradientObservable_le_add (N : ℕ) (q r : Phase N) :
    gradientObservable q ≤ gradientEmbeddingConstant * Real.sqrt (energy3 N (q - r)) +
      gradientObservable r := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨x, rfl⟩
  change Real.sqrt (gradientSquare q x) ≤
    gradientEmbeddingConstant * Real.sqrt (energy3 N (q - r)) + gradientObservable r
  rw [sqrt_gradientSquare_eq_norm]
  calc
    _ ≤ ‖gradientCoordinates N x (q - r)‖ + ‖gradientCoordinates N x r‖ := by
      simpa only [map_sub, sub_add_cancel] using
        norm_add_le (gradientCoordinates N x (q - r)) (gradientCoordinates N x r)
    _ ≤ gradientEmbeddingConstant * Real.sqrt (energy3 N (q - r)) +
        gradientObservable r := by
      rw [← sqrt_gradientSquare_eq_norm, ← sqrt_gradientSquare_eq_norm]
      exact add_le_add (sqrt_gradientSquare_le N (q - r) x)
        (le_csSup (gradientObservable_range_bddAbove N r) (Set.mem_range_self x))

theorem abs_gradientObservable_sub_le (N : ℕ) (q r : Phase N) :
    |gradientObservable q - gradientObservable r| ≤
      gradientEmbeddingConstant * Real.sqrt (energy3 N (q - r)) := by
  have hqr := gradientObservable_le_add N q r
  have hrq := gradientObservable_le_add N r q
  have hsymm : Real.sqrt (energy3 N (r - q)) = Real.sqrt (energy3 N (q - r)) := by
    simp only [sqrt_energy3_eq_norm, map_sub, norm_sub_rev]
  rw [hsymm] at hrq
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def gradientLipschitzConstant (N : ℕ) : NNReal :=
  ⟨gradientEmbeddingConstant * cutoffSobolevFactor N,
    mul_nonneg gradientEmbeddingConstant_pos.le (cutoffSobolevFactor_pos N).le⟩

theorem lipschitz_gradientObservable (N : ℕ) :
    LipschitzWith (gradientLipschitzConstant N) (@gradientObservable N) := by
  apply LipschitzWith.of_dist_le_mul
  intro q r
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
  change |gradientObservable q - gradientObservable r| ≤
    (gradientEmbeddingConstant * cutoffSobolevFactor N) * ‖q - r‖
  calc
    _ ≤ gradientEmbeddingConstant * Real.sqrt (energy3 N (q - r)) :=
      abs_gradientObservable_sub_le N q r
    _ ≤ gradientEmbeddingConstant * (cutoffSobolevFactor N * ‖q - r‖) :=
      mul_le_mul_of_nonneg_left (sqrt_energy3_le_cutoffSobolevFactor_mul_norm N (q - r))
        gradientEmbeddingConstant_pos.le
    _ = _ := by ring

theorem continuous_gradientObservable (N : ℕ) : Continuous (@gradientObservable N) :=
  (lipschitz_gradientObservable N).continuous

/-- The literal native spatial supremum is integrable along every exact finite orbit. -/
theorem intervalIntegrable_gradientObservable {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (a b : ℝ) :
    IntervalIntegrable (fun t => gradientObservable (F.map N t q)) volume a b := by
  have hq : Continuous (fun t => F.map N t q) :=
    continuous_iff_continuousAt.mpr (fun t => (F.orbit_derivative N q t).continuousAt)
  exact ((continuous_gradientObservable N).comp hq).intervalIntegrable a b

end

end QuantumAdapter.Assembly
