import SingularClosure.FiniteParseval

/-! Actual finite Hessian/Laplacian L² identity, with the physical derivative operators. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

def laplacianFrequency (k : Frequency) : ℝ :=
  (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)

def laplacianCoefficient (c : FourierCoeff) : FourierCoeff :=
  fun k j => -(laplacianFrequency k : ℂ) * c k j

theorem sum_derivativeScale_sq (k : Frequency) :
    (∑ i : Fin 3, (2 * Real.pi * (k i : ℝ)) ^ 2) = laplacianFrequency k := by
  unfold laplacianFrequency galerkinFreqSq
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem double_derivativeSymbol (i : Fin 3) (k : Frequency) (z : ℂ) :
    derivativeSymbol i k * (derivativeSymbol i k * z) =
      -(((2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ) * z := by
  unfold derivativeSymbol
  calc
    _ = (((2 * Real.pi * (k i : ℝ) : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) * z := by ring
    _ = _ := by rw [Complex.I_sq]; push_cast; ring

theorem sum_double_derivativeMultiplier (c : FourierCoeff) :
    (∑ i : Fin 3,
      spectralMultiplier (derivativeSymbol i) (spectralMultiplier (derivativeSymbol i) c)) =
        laplacianCoefficient c := by
  funext k j
  change (∑ i : Fin 3, derivativeSymbol i k * (derivativeSymbol i k * c k j)) =
    -(laplacianFrequency k : ℂ) * c k j
  simp_rw [double_derivativeSymbol]
  have hcast : (∑ i : Fin 3, (((2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ)) =
      (laplacianFrequency k : ℂ) := by
    calc
      _ = ((∑ i : Fin 3, (2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ) :=
        (map_sum Complex.ofRealHom _ _).symm
      _ = _ := congrArg (fun r : ℝ => (r : ℂ)) (sum_derivativeScale_sq k)
  calc
    _ = -(∑ i : Fin 3, (((2 * Real.pi * (k i : ℝ)) ^ 2 : ℝ) : ℂ)) * c k j := by
      simp [Finset.sum_mul, Finset.sum_neg_distrib]
    _ = _ := by rw [hcast]

theorem finiteSynthesis_laplacian (N : ℕ) (c : FourierCoeff) :
    laplacian (finiteSynthesis N c) = finiteSynthesis N (laplacianCoefficient c) := by
  funext x
  unfold laplacian
  change (∑ i : Fin 3,
    coordinateDerivative (coordinateDerivative (finiteSynthesis N c) i) i x) = _
  simp_rw [finiteSynthesis_coordinateDerivative]
  have h := congrArg (fun b : Field => b x)
    (finiteSynthesis_sum N Finset.univ (fun i : Fin 3 =>
      spectralMultiplier (derivativeSymbol i) (spectralMultiplier (derivativeSymbol i) c)))
  rw [sum_double_derivativeMultiplier] at h
  simpa using h.symm

theorem laplacianCoefficient_reality (c : FourierCoeff) (hreal : SpectralReality c) :
    SpectralReality (laplacianCoefficient c) := by
  intro k j
  have hfreq : laplacianFrequency (-k) = laplacianFrequency k := by
    simp [laplacianFrequency, galerkinFreqSq]
  simp [laplacianCoefficient, hfreq, hreal k j, Complex.star_def]

theorem coefficientDissipation_derivative_sum (N : ℕ) (c : FourierCoeff) :
    (∑ i : Fin 3, coefficientDissipation N (spectralMultiplier (derivativeSymbol i) c)) =
      coefficientEnergy N (laplacianCoefficient c) := by
  have hpoint (k : Frequency) (j : Fin 3) :
      (∑ i : Fin 3, laplacianFrequency k *
        Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j)) =
          Complex.normSq (laplacianCoefficient c k j) := by
    simp_rw [normSq_derivativeMultiplier]
    rw [← Finset.mul_sum, ← Finset.sum_mul, sum_derivativeScale_sq]
    simp [laplacianCoefficient, Complex.normSq_mul, Complex.normSq_apply, pow_two]
    ring
  change (∑ i : Fin 3, ∑ k ∈ cutoffModes N, ∑ j : Fin 3,
    laplacianFrequency k * Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j)) =
    ∑ k ∈ cutoffModes N, ∑ j : Fin 3, Complex.normSq (laplacianCoefficient c k j)
  calc
    _ = ∑ k ∈ cutoffModes N, ∑ i : Fin 3, ∑ j : Fin 3,
        laplacianFrequency k * Complex.normSq
          (spectralMultiplier (derivativeSymbol i) c k j) := Finset.sum_comm
    _ = ∑ k ∈ cutoffModes N, ∑ j : Fin 3, ∑ i : Fin 3,
        laplacianFrequency k * Complex.normSq
          (spectralMultiplier (derivativeSymbol i) c k j) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      exact hpoint k j

/-- The actual sum of squared physical Hessian components equals the squared
L² norm of the physical Laplacian. This is uniform in the cutoff. -/
theorem FINITE_HESSIAN_LAPLACIAN_EQ (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    (∑ i : Fin 3, ∫ x in unitCube,
      gradientSquareDensity (coordinateDerivative (finiteSynthesis N c) i) x) =
        ∫ x in unitCube, ‖laplacian (finiteSynthesis N c) x‖ ^ 2 := by
  calc
    _ = ∑ i : Fin 3, coefficientDissipation N (spectralMultiplier (derivativeSymbol i) c) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [finiteSynthesis_coordinateDerivative]
      exact FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N _ (derivativeMultiplier_reality c hreal i)
    _ = coefficientEnergy N (laplacianCoefficient c) :=
      coefficientDissipation_derivative_sum N c
    _ = physicalEnergy (finiteSynthesis N (laplacianCoefficient c)) :=
      (FINITE_PHYSICAL_ENERGY_PARSEVAL N _ (laplacianCoefficient_reality c hreal)).symm
    _ = _ := by
      rw [← finiteSynthesis_laplacian, physicalEnergy_eq_integral_norm_sq]

end

end SingularClosure
