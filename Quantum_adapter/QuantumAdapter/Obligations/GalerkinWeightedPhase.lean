import QuantumAdapter.Obligations.GalerkinSobolev
import QuantumAdapter.Obligations.TraceLaplacian
import QuantumAdapter.Obligations.EnergyBilinear

/-!
All integral Sobolev multipliers on the actual real Fourier phase, with exact
energy differentiation and the exact next-order dissipation difference.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure QuantumAdapter.Assembly

theorem torusSobolevWeight_sq_native (k : Frequency) :
    torusSobolevWeight k ^ 2 = 1 + laplaceSymbol k := by
  change Real.sqrt (1 + laplaceSymbol k) ^ 2 = 1 + laplaceSymbol k
  exact Real.sq_sqrt (by linarith [laplaceSymbol_nonneg k])

theorem torusSobolevWeight_neg_native (k : Frequency) :
    torusSobolevWeight (-k) = torusSobolevWeight k := by
  change Real.sqrt (1 + laplaceSymbol (-k)) = Real.sqrt (1 + laplaceSymbol k)
  rw [laplaceSymbol_neg_native]

def sobolevWeightedAmbient (s N : ℕ) (q : Phase N) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => (torusSobolevWeight ki.1.val : ℂ) ^ s *
    phaseCoeff q ki.1.val ki.2)

theorem sobolevWeightedAmbient_coeff (s N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    extendCoeff (sobolevWeightedAmbient s N q) k i =
      (torusSobolevWeight k : ℂ) ^ s * phaseCoeff q k i := by
  by_cases hk : k ∈ fullModes N
  · simp [sobolevWeightedAmbient, extendCoeff, hk]
  · simp [sobolevWeightedAmbient, extendCoeff, hk, phaseCoeff_support q k hk i]

theorem sobolevWeightedAmbient_mem (s N : ℕ) (q : Phase N) :
    sobolevWeightedAmbient s N q ∈ phaseSubmodule N := by
  constructor
  · intro k i
    rw [sobolevWeightedAmbient_coeff, sobolevWeightedAmbient_coeff,
      torusSobolevWeight_neg_native, phaseCoeff_reality q k i]
    simp [star_mul, mul_comm]
  · intro k
    simp_rw [sobolevWeightedAmbient_coeff]
    calc
      _ = (torusSobolevWeight k : ℂ) ^ s *
          ∑ i : Fin 3, (k i : ℂ) * phaseCoeff q k i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [phaseCoeff_solenoidal q k, mul_zero]

def sobolevWeightedPhase (s N : ℕ) : Phase N →ₗ[ℝ] Phase N where
  toFun q := ⟨sobolevWeightedAmbient s N q, sobolevWeightedAmbient_mem s N q⟩
  map_add' q r := by
    apply Subtype.ext
    ext ki
    simp [sobolevWeightedAmbient, phaseCoeff, extendCoeff, mul_add]
  map_smul' a q := by
    apply Subtype.ext
    ext ki
    simp [sobolevWeightedAmbient, phaseCoeff, extendCoeff, mul_left_comm]

def sobolevWeightedPhaseCLM (s N : ℕ) : Phase N →L[ℝ] Phase N :=
  { toLinearMap := sobolevWeightedPhase s N
    cont := (sobolevWeightedPhase s N).continuous_of_finiteDimensional }

theorem sobolevWeightedPhase_coeff (s N : ℕ) (q : Phase N)
    (k : Frequency) (i : Fin 3) :
    phaseCoeff (sobolevWeightedPhase s N q) k i =
      sobolevWeightedCoeff s (phaseCoeff q) (k, i) :=
  sobolevWeightedAmbient_coeff s N q k i

theorem sobolevWeightedPhase_norm_sq (s N : ℕ) (q : Phase N) :
    ‖sobolevWeightedPhaseCLM s N q‖ ^ 2 = sobolevEnergy s N q := by
  rw [← energy0_eq_norm_sq]
  change energy0 N (sobolevWeightedPhase s N q) = sobolevEnergy s N q
  unfold energy0 sobolevEnergy sobolevEnergyDensity
  simp only [sobolevWeightedPhase_coeff,
    Complex.normSq_eq_norm_sq]

theorem sobolevWeightedPhase_laplacian_commute (s N : ℕ) (q : Phase N) :
    sobolevWeightedPhase s N (phaseLaplacian N q) =
      phaseLaplacian N (sobolevWeightedPhase s N q) := by
  apply Subtype.ext
  apply extendCoeff_injective N
  funext k i
  change phaseCoeff (sobolevWeightedPhase s N (phaseLaplacian N q)) k i =
    phaseCoeff (phaseLaplacian N (sobolevWeightedPhase s N q)) k i
  rw [sobolevWeightedPhase_coeff, phaseLaplacian_coeff, sobolevWeightedPhase_coeff]
  simp only [sobolevWeightedCoeff, phaseLaplacian_coeff]
  ring

def sobolevDissipation (s N : ℕ) (q : Phase N) : ℝ :=
  ∑ k ∈ fullModes N, laplaceSymbol k * sobolevEnergyDensity s (phaseCoeff q) k

theorem sobolevDissipation_nonneg (s N : ℕ) (q : Phase N) :
    0 ≤ sobolevDissipation s N q := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (laplaceSymbol_nonneg k) (sobolevEnergyDensity_nonneg s _ k)

theorem complex_real_weight_inner (a : ℝ) (z : ℂ) :
    (star z * ((a : ℂ) * z)).re = a * ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.normSq_apply]
  ring

theorem sobolevWeighted_inner_laplacian (s N : ℕ) (q : Phase N) :
    inner ℝ (sobolevWeightedPhaseCLM s N q)
      (sobolevWeightedPhaseCLM s N (phaseLaplacian N q)) =
      sobolevDissipation s N q := by
  change inner ℝ (sobolevWeightedPhase s N q)
    (sobolevWeightedPhase s N (phaseLaplacian N q)) = _
  rw [sobolevWeightedPhase_laplacian_commute, phase_inner_eq_sum]
  simp_rw [phaseLaplacian_coeff, complex_real_weight_inner, sobolevWeightedPhase_coeff]
  unfold sobolevDissipation sobolevEnergyDensity
  simp only [Finset.mul_sum]

theorem sobolevEnergyDensity_succ (s : ℕ) (c : FourierCoeff) (k : Frequency) :
    sobolevEnergyDensity (s + 1) c k =
      (1 + laplaceSymbol k) * sobolevEnergyDensity s c k := by
  unfold sobolevEnergyDensity
  rw [← torusSobolevWeight_sq_native, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sobolevWeightedCoeff_norm_eq, sobolevWeightedCoeff_norm_eq, pow_succ]
  ring

theorem sobolevDissipation_eq_energy_succ_sub (s N : ℕ) (q : Phase N) :
    sobolevDissipation s N q = sobolevEnergy (s + 1) N q - sobolevEnergy s N q := by
  unfold sobolevDissipation sobolevEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sobolevEnergyDensity_succ]
  ring

theorem phaseFlow_sobolevEnergy_hasDerivAt {ν : ℝ} (F : PhaseFlow ν)
    (s N : ℕ) (q : Phase N) (t : ℝ) :
    HasDerivAt (fun r => sobolevEnergy s N (F.map N r q))
      (2 * inner ℝ (sobolevWeightedPhaseCLM s N (F.map N t q))
        (sobolevWeightedPhaseCLM s N (drift ν N (F.map N t q)))) t := by
  have h := HasDerivAt.norm_sq (F := Phase N)
    ((sobolevWeightedPhaseCLM s N).hasFDerivAt.comp_hasDerivAt t (F.orbit_derivative N q t))
  simpa only [Function.comp_def, sobolevWeightedPhase_norm_sq] using h

theorem phaseFlow_sobolevEnergy_dissipation_identity {ν : ℝ} (F : PhaseFlow ν)
    (s N : ℕ) (q : Phase N) (t : ℝ) :
    HasDerivAt (fun r => sobolevEnergy s N (F.map N r q))
      (2 * inner ℝ (sobolevWeightedPhaseCLM s N (F.map N t q))
        (sobolevWeightedPhaseCLM s N (drift 0 N (F.map N t q))) -
          2 * ν * sobolevDissipation s N (F.map N t q)) t := by
  have h := phaseFlow_sobolevEnergy_hasDerivAt F s N q t
  rw [drift_eq_inviscid_sub_laplacian, map_sub, map_smul,
    inner_sub_right, real_inner_smul_right, sobolevWeighted_inner_laplacian] at h
  convert h using 1 <;> ring

end
end QuantumAdapter.Obligations
