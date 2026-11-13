import SingularClosure.FourierIntegral
import SingularClosure.PhysicalProjection
import SingularClosure.GalerkinReality
import SingularClosure.LerayPressure

/-!
# Actual finite Fourier pressure reconstruction

The scalar polynomial below is smooth, periodic, and has zero spatial mean.
Its literal physical gradient recovers the longitudinal correction of the
finite transport polynomial. Conjugate symmetry is proved for the actual
pressure coefficients. No infinite Fourier convergence or smooth-limit
pressure reconstruction is assumed or asserted here.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- Real scalar synthesis on the same actual nonzero frequency cutoff. -/
def finiteScalarSynthesis (N : ℕ) (b : Frequency → ℂ) (x : Vec) : ℝ :=
  (∑ k ∈ cutoffModes N, fourierCharacter k x * b k).re

theorem finiteScalarSynthesis_contDiff (N : ℕ) (b : Frequency → ℂ) :
    ContDiff ℝ ∞ (finiteScalarSynthesis N b) := by
  have hsum : ContDiff ℝ ∞
      (fun x : Vec => ∑ k ∈ cutoffModes N, fourierCharacter k x * b k) :=
    ContDiff.sum fun k _ => (fourierCharacter_contDiff k).mul contDiff_const
  exact Complex.reCLM.contDiff.comp hsum

theorem finiteScalarSynthesis_periodic (N : ℕ) (b : Frequency → ℂ) :
    SpatialPeriodic (finiteScalarSynthesis N b) := by
  intro x j
  unfold finiteScalarSynthesis
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [fourierCharacter_periodic k x j]

/-- Conjugate-symmetric coefficients synthesize an actually real complex sum. -/
theorem finiteScalarSynthesis_of_reality (N : ℕ) (b : Frequency → ℂ)
    (hb : ∀ k, b (-k) = star (b k)) (x : Vec) :
    (finiteScalarSynthesis N b x : ℂ) =
      ∑ k ∈ cutoffModes N, fourierCharacter k x * b k := by
  classical
  apply Complex.conj_eq_iff_re.mp
  change star (∑ k ∈ cutoffModes N, fourierCharacter k x * b k) = _
  symm
  rw [star_sum]
  apply Finset.sum_nbij' (fun k => -k) (fun k => -k)
    (fun k hk => cutoffModes_neg_mem hk) (fun k hk => cutoffModes_neg_mem hk)
  · intro k hk
    simp
  · intro k hk
    simp
  · intro k hk
    simp only [fourierCharacter_neg, hb, star_mul, star_star, mul_comm]

/-- The real integral is finite and vanishes on the physical fundamental cube. -/
theorem finiteScalarSynthesis_meanZero (N : ℕ) (b : Frequency → ℂ) :
    PressureMeanZero (finiteScalarSynthesis N b) := by
  classical
  have hterm (k : Frequency) : IntegrableOn
      (fun x : Vec => fourierCharacter k x * b k) unitCube volume :=
    ((fourierCharacter_contDiff k).continuous.mul continuous_const).continuousOn.integrableOn_compact
      isCompact_unitCube
  have hsum : IntegrableOn
      (fun x : Vec => ∑ k ∈ cutoffModes N, fourierCharacter k x * b k)
      unitCube volume := by
    exact integrable_finsetSum _ (fun k _ => hterm k)
  refine ⟨(finiteScalarSynthesis_contDiff N b).continuous.continuousOn.integrableOn_compact
    isCompact_unitCube, ?_⟩
  change (∫ x in unitCube,
    (∑ k ∈ cutoffModes N, fourierCharacter k x * b k).re) = 0
  have hz : (∑ k ∈ cutoffModes N,
      ∫ x in unitCube, fourierCharacter k x * b k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [integral_mul_const, integral_fourierCharacter]
    have hk0 : k ≠ 0 := fun h => cutoffModes_zero_not_mem N (h ▸ hk)
    simp [hk0]
  calc
    _ = (∫ x in unitCube,
        ∑ k ∈ cutoffModes N, fourierCharacter k x * b k).re :=
      Complex.reCLM.integral_comp_comm hsum
    _ = 0 := by
      rw [integral_finsetSum (cutoffModes N)
        (f := fun k x => fourierCharacter k x * b k) (fun k _ => hterm k), hz]
      rfl

/-- The scalar physical gradient is the actual Fourier derivative multiplier. -/
theorem finiteScalarSynthesis_gradient (N : ℕ) (b : Frequency → ℂ) :
    gradient (finiteScalarSynthesis N b) =
      finiteSynthesis N (fun k i => derivativeSymbol i k * b k) := by
  funext x
  ext i
  have hs : HasFDerivAt
      (fun y : Vec => ∑ k ∈ cutoffModes N, fourierCharacter k y * b k)
      (∑ k ∈ cutoffModes N,
        b k • (fourierCharacter k x • fourierPhaseCLM k)) x := by
    exact HasFDerivAt.fun_sum fun k _ =>
      (fourierCharacter_hasFDerivAt k x).mul_const (b k)
  have hr := Complex.reCLM.hasFDerivAt.comp x hs
  have hp := ((finiteScalarSynthesis_contDiff N b).differentiable (by simp) x).hasFDerivAt
  have heq := hp.unique hr
  have heval := congrArg (fun L : Vec →L[ℝ] ℝ => L (unitVector i)) heq
  change fderiv ℝ (finiteScalarSynthesis N b) x (unitVector i) =
    (∑ k ∈ cutoffModes N,
      fourierCharacter k x * (derivativeSymbol i k * b k)).re
  simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, fourierPhaseCLM_unitVector,
    mul_comm, mul_left_comm, mul_assoc] using heval

theorem pressureFromTransport_neg_star (k : Frequency) (v : Fin 3 → ℂ) :
    pressureFromTransport (-k) (fun i => star (v i)) =
      star (pressureFromTransport k v) := by
  by_cases hk : k = 0
  · subst k
    simp [pressureFromTransport]
  · simp [pressureFromTransport, hk, neg_ne_zero.mpr hk, Complex.star_def,
      map_sum, Finset.sum_neg_distrib, mul_comm, mul_left_comm, mul_assoc]

/-- Pressure polynomial for a prescribed finite transport coefficient family. -/
def finiteTransportPressure (N : ℕ) (v : FourierCoeff) : Vec → ℝ :=
  finiteScalarSynthesis N (fun k => pressureFromTransport k (v k))

theorem finiteTransportPressure_contDiff (N : ℕ) (v : FourierCoeff) :
    ContDiff ℝ ∞ (finiteTransportPressure N v) :=
  finiteScalarSynthesis_contDiff N _

theorem finiteTransportPressure_periodic (N : ℕ) (v : FourierCoeff) :
    SpatialPeriodic (finiteTransportPressure N v) :=
  finiteScalarSynthesis_periodic N _

theorem finiteTransportPressure_meanZero (N : ℕ) (v : FourierCoeff) :
    PressureMeanZero (finiteTransportPressure N v) :=
  finiteScalarSynthesis_meanZero N _

/-- Literal physical pressure-gradient recovery for the finite Fourier field. -/
theorem finiteTransportPressure_recovery (N : ℕ) (v : FourierCoeff) (x : Vec) :
    finiteSynthesis N v x + gradient (finiteTransportPressure N v) x =
      finiteSynthesis N (fun k => coefficientLeray k (v k)) x := by
  have hsymbol (k : Frequency) (i : Fin 3) :
      derivativeSymbol i k =
        ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (k i : ℂ) := by
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  have hcoeff : v + (fun k i => derivativeSymbol i k * pressureFromTransport k (v k)) =
      (fun k => coefficientLeray k (v k)) := by
    funext k i
    change v k i + derivativeSymbol i k * pressureFromTransport k (v k) = _
    rw [hsymbol]
    exact pressureFromTransport_recovery k (v k) i
  unfold finiteTransportPressure
  rw [finiteScalarSynthesis_gradient]
  calc
    _ = finiteSynthesis N
        (v + (fun k i => derivativeSymbol i k * pressureFromTransport k (v k))) x :=
      (congrFun (finiteSynthesis_add N v _) x).symm
    _ = _ := congrArg (fun a => finiteSynthesis N a x) hcoeff

/-- The concrete nonlinear Galerkin convolution produces real pressure coefficients. -/
theorem galerkinPressure_coeff_reality (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c) (k : Frequency) :
    pressureFromTransport (-k) (coefficientTransport N c (-k)) =
      star (pressureFromTransport k (coefficientTransport N c k)) := by
  have ht : coefficientTransport N c (-k) =
      fun i => star (coefficientTransport N c k i) := by
    funext i
    exact coefficientTransport_reality N c hc k i
  rw [ht, pressureFromTransport_neg_star]

theorem galerkinPressure_complex_synthesis (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c) (x : Vec) :
    (finiteTransportPressure N (coefficientTransport N c) x : ℂ) =
      ∑ k ∈ cutoffModes N,
        fourierCharacter k x * pressureFromTransport k (coefficientTransport N c k) :=
  finiteScalarSynthesis_of_reality N _ (galerkinPressure_coeff_reality N c hc) x

/-- Exact pressure correction for the actual finite transport coefficients. -/
theorem galerkinPressure_recovery (N : ℕ) (c : FourierCoeff) (x : Vec) :
    finiteSynthesis N (coefficientTransport N c) x +
      gradient (finiteTransportPressure N (coefficientTransport N c)) x =
      finiteSynthesis N (fun k => coefficientLeray k (coefficientTransport N c k)) x :=
  finiteTransportPressure_recovery N (coefficientTransport N c) x

end

end SingularClosure
