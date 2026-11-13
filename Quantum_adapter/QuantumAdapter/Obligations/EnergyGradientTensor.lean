import QuantumAdapter.Obligations.EnergyDerivatives
import QuantumAdapter.Obligations.TensorInterpolation

/-! Actual native gradient tensors and cutoff-independent interpolation. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff

namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

def gradientTensor (N : ℕ) (q : Phase N) : Vec → EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  fun x => Assembly.gradientCoordinates N x q

theorem gradientTensor_apply (N : ℕ) (q : Phase N) (x : Vec) (ji : Fin 3 × Fin 3) :
    gradientTensor N q x ji = synthesis (phaseDerivative N ji.1 q) x ji.2 := by
  rw [synthesis_phaseDerivative]
  exact Assembly.gradientCoordinates_apply N q x ji

theorem gradientTensor_contDiff (N : ℕ) (q : Phase N) :
    ContDiff ℝ ∞ (gradientTensor N q) := by
  apply (contDiff_piLp 2).2
  intro ji
  simp only [gradientTensor_apply]
  exact (EuclideanSpace.proj ji.2 : Vec →L[ℝ] ℝ).contDiff.comp
    (synthesis_contDiff N (phaseDerivative N ji.1 q))

theorem gradientTensor_periodic (N : ℕ) (q : Phase N) : SpatialPeriodic (gradientTensor N q) := by
  intro x j
  ext ki
  simp only [gradientTensor_apply, synthesis_periodic N (phaseDerivative N ki.1 q) x j]

theorem gradientTensor_norm_sq (N : ℕ) (q : Phase N) (x : Vec) :
    ‖gradientTensor N q x‖ ^ 2 = gradientSquare q x :=
  Assembly.gradientCoordinates_norm_sq N q x

theorem gradientTensor_norm_le (N : ℕ) (q : Phase N) (x : Vec) :
    ‖gradientTensor N q x‖ ≤ gradientObservable q := by
  change ‖Assembly.gradientCoordinates N x q‖ ≤ gradientObservable q
  rw [← Assembly.sqrt_gradientSquare_eq_norm N q x]
  exact le_csSup (Assembly.gradientObservable_range_bddAbove N q) (Set.mem_range_self x)

theorem tensorDir_euclidean_apply {I : Type*} [Fintype I]
    (f : Vec → EuclideanSpace ℝ I) (hf : Differentiable ℝ f)
    (j : Fin 3) (x : Vec) (i : I) :
    tensorDir f j x i = tensorDir (fun y => f y i) j x := by
  have hd := (EuclideanSpace.proj i : EuclideanSpace ℝ I →L[ℝ] ℝ).hasFDerivAt.comp x
    (hf x).hasFDerivAt
  have hh := congrArg (fun A : Vec →L[ℝ] ℝ => A (unitVector j)) hd.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    EuclideanSpace.coe_proj, tensorDir] using hh.symm

theorem tensorDir_gradientTensor (N : ℕ) (q : Phase N) (j : Fin 3) :
    tensorDir (gradientTensor N q) j = gradientTensor N (phaseDerivative N j q) := by
  funext x
  ext ki
  calc
    _ = tensorDir (fun y => gradientTensor N q y ki) j x :=
      tensorDir_euclidean_apply _ ((gradientTensor_contDiff N q).differentiable (by simp)) j x ki
    _ = tensorDir (fun y => synthesis (phaseDerivative N ki.1 q) y ki.2) j x := by
      simp only [gradientTensor_apply]
    _ = tensorDir (synthesis (phaseDerivative N ki.1 q)) j x ki.2 :=
      (tensorDir_euclidean_apply _
        ((synthesis_contDiff N (phaseDerivative N ki.1 q)).differentiable (by simp)) j x ki.2).symm
    _ = synthesis (phaseDerivative N j (phaseDerivative N ki.1 q)) x ki.2 := by
      change coordinateDerivative (synthesis (phaseDerivative N ki.1 q)) j x ki.2 = _
      rw [← synthesis_phaseDerivative]
    _ = synthesis (phaseDerivative N ki.1 (phaseDerivative N j q)) x ki.2 := by
      rw [phaseDerivative_commute]
    _ = gradientTensor N (phaseDerivative N j q) x ki := (gradientTensor_apply _ _ _ _).symm

def gradientSecondDensity (N : ℕ) (q : Phase N) (x : Vec) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ‖synthesis (phaseDerivative N j (phaseDerivative N i q)) x‖ ^ 2

def gradientThirdDensity (N : ℕ) (q : Phase N) (x : Vec) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    ‖synthesis (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q))) x‖ ^ 2

theorem gradientSecondDensity_nonneg (N : ℕ) (q : Phase N) (x : Vec) :
    0 ≤ gradientSecondDensity N q x :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem gradientThirdDensity_nonneg (N : ℕ) (q : Phase N) (x : Vec) :
    0 ≤ gradientThirdDensity N q x :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem gradientSecondDensity_continuous (N : ℕ) (q : Phase N) :
    Continuous (gradientSecondDensity N q) :=
  continuous_finset_sum _ (fun i hi => continuous_finset_sum _ (fun j hj =>
    (synthesis_contDiff N (phaseDerivative N j (phaseDerivative N i q))).continuous.norm.pow 2))

theorem gradientThirdDensity_continuous (N : ℕ) (q : Phase N) :
    Continuous (gradientThirdDensity N q) :=
  continuous_finset_sum _ (fun i hi => continuous_finset_sum _ (fun j hj =>
    continuous_finset_sum _ (fun k hk => (synthesis_contDiff N
      (phaseDerivative N k (phaseDerivative N j (phaseDerivative N i q)))).continuous.norm.pow 2)))

theorem tensorGradSq_gradientTensor (N : ℕ) (q : Phase N) (x : Vec) :
    tensorGradSq (gradientTensor N q) x = gradientSecondDensity N q x := by
  simp only [tensorGradSq, tensorDir_gradientTensor, gradientTensor_norm_sq,
    gradientSquare, ← synthesis_phaseDerivative, gradientSecondDensity]

theorem tensorHessSq_gradientTensor (N : ℕ) (q : Phase N) (x : Vec) :
    tensorHessSq (gradientTensor N q) x = gradientThirdDensity N q x := by
  simp only [tensorHessSq, tensorDir_gradientTensor, gradientTensor_norm_sq,
    gradientSquare, ← synthesis_phaseDerivative, gradientThirdDensity]
  exact Finset.sum_comm

theorem gradientSecondDensity_eq_sum_gradientSquare (N : ℕ) (q : Phase N) (x : Vec) :
    gradientSecondDensity N q x = ∑ i : Fin 3, gradientSquare (phaseDerivative N i q) x := by
  simp only [gradientSecondDensity, gradientSquare, ← synthesis_phaseDerivative]

theorem gradientThirdDensity_eq_sum_second (N : ℕ) (q : Phase N) (x : Vec) :
    gradientThirdDensity N q x = ∑ i : Fin 3, gradientSecondDensity N (phaseDerivative N i q) x := rfl

theorem gradientSquare_continuous_native (N : ℕ) (q : Phase N) : Continuous (gradientSquare q) := by
  have h : (fun x => ‖gradientTensor N q x‖ ^ 2) = gradientSquare q :=
    funext (gradientTensor_norm_sq N q)
  rw [← h]
  exact (gradientTensor_contDiff N q).continuous.norm.pow 2

theorem integral_gradientSquare_frequencyEnergy (N : ℕ) (q : Phase N) :
    (∫ x in unitCube, gradientSquare q x) = frequencyEnergy 1 N q := by
  simp only [gradientSquare, ← synthesis_phaseDerivative]
  rw [integral_finsetSum Finset.univ (μ := volume.restrict unitCube)
    (f := fun j x => ‖synthesis (phaseDerivative N j q) x‖ ^ 2) (fun j hj =>
    ((synthesis_contDiff N (phaseDerivative N j q)).continuous.norm.pow 2).continuousOn.integrableOn_compact
      isCompact_unitCube)]
  simp_rw [integral_synthesis_norm_sq, ← frequencyEnergy_zero N]
  exact frequencyEnergy_derivative_sum 0 N q

theorem integral_gradientSecondDensity (N : ℕ) (q : Phase N) :
    (∫ x in unitCube, gradientSecondDensity N q x) = frequencyEnergy 2 N q := by
  simp_rw [gradientSecondDensity_eq_sum_gradientSquare]
  rw [integral_finsetSum Finset.univ (μ := volume.restrict unitCube)
    (f := fun j x => gradientSquare (phaseDerivative N j q) x) (fun j hj =>
    (gradientSquare_continuous_native N (phaseDerivative N j q)).continuousOn.integrableOn_compact
      isCompact_unitCube)]
  simp_rw [integral_gradientSquare_frequencyEnergy]
  exact frequencyEnergy_derivative_sum 1 N q

theorem integral_gradientThirdDensity (N : ℕ) (q : Phase N) :
    (∫ x in unitCube, gradientThirdDensity N q x) = frequencyEnergy 3 N q := by
  simp_rw [gradientThirdDensity_eq_sum_second]
  rw [integral_finsetSum Finset.univ (μ := volume.restrict unitCube)
    (f := fun j x => gradientSecondDensity N (phaseDerivative N j q) x) (fun j hj =>
    (gradientSecondDensity_continuous N (phaseDerivative N j q)).continuousOn.integrableOn_compact
      isCompact_unitCube)]
  simp_rw [integral_gradientSecondDensity]
  exact frequencyEnergy_derivative_sum 2 N q

/-- The actual second derivative tensor satisfies the cutoff-independent L4 bound. -/
theorem synthesis_second_derivative_interpolation (N : ℕ) (q : Phase N) :
    Real.sqrt (∫ x in unitCube, gradientSecondDensity N q x ^ 2) ≤
      4 * gradientObservable q * Real.sqrt (frequencyEnergy 3 N q) := by
  have h := periodic_tensor_interpolation (gradientTensor N q) (gradientTensor_contDiff N q)
    (gradientTensor_periodic N q) (gradientObservable q) (gradientTensor_norm_le N q)
  simpa only [tensorGradSq_gradientTensor, tensorHessSq_gradientTensor,
    integral_gradientThirdDensity] using h

end
end QuantumAdapter.Obligations
