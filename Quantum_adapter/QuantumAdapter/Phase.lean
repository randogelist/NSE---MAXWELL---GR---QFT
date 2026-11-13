import SingularClosure.InitialFourier
import SingularClosure.GalerkinReality
import Mathlib.Analysis.InnerProductSpace.PiL2
import MaxwellEndpoint.Geometry

/-!
# Concrete full Fourier phase space

The zero Fourier mode is retained. The phase is the real submodule of the
finite complex Euclidean coefficient space cut out by actual conjugate reality
and solenoidality. The inherited real Hilbert norm is not the norm of a plain
finite Pi space. No mean-zero condition is imposed on initial data.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace QuantumAdapter

noncomputable section

open SingularClosure

def fullModes (N : ℕ) : Finset Frequency :=
  insert 0 (cutoffModes N)

abbrev Mode (N : ℕ) := ↥(fullModes N)
abbrev PhaseIndex (N : ℕ) := Mode N × Fin 3
abbrev AmbientPhase (N : ℕ) := EuclideanSpace ℂ (PhaseIndex N)

theorem zero_mem_fullModes (N : ℕ) : (0 : Frequency) ∈ fullModes N := by
  simp [fullModes]

theorem fullModes_neg_mem {N : ℕ} {k : Frequency}
    (hk : k ∈ fullModes N) : -k ∈ fullModes N := by
  rcases Finset.mem_insert.mp hk with h | h
  · subst k
    simpa using zero_mem_fullModes N
  · exact Finset.mem_insert_of_mem (cutoffModes_neg_mem h)

theorem fullModes_neg_mem_iff (N : ℕ) (k : Frequency) :
    -k ∈ fullModes N ↔ k ∈ fullModes N := by
  constructor
  · intro h
    simpa using fullModes_neg_mem h
  · exact fullModes_neg_mem

def extendCoeff {N : ℕ} (q : AmbientPhase N) : FourierCoeff :=
  fun k i => if hk : k ∈ fullModes N then q (⟨k, hk⟩, i) else 0

@[simp]
theorem extendCoeff_zero (N : ℕ) :
    extendCoeff (0 : AmbientPhase N) = 0 := by
  funext k i
  simp [extendCoeff]

@[simp]
theorem extendCoeff_add {N : ℕ} (q r : AmbientPhase N) :
    extendCoeff (q + r) = extendCoeff q + extendCoeff r := by
  funext k i
  by_cases hk : k ∈ fullModes N <;> simp [extendCoeff, hk]

@[simp]
theorem extendCoeff_real_smul {N : ℕ} (r : ℝ) (q : AmbientPhase N) :
    extendCoeff (r • q) = r • extendCoeff q := by
  funext k i
  by_cases hk : k ∈ fullModes N <;> simp [extendCoeff, hk]

theorem extendCoeff_injective (N : ℕ) :
    Function.Injective (@extendCoeff N) := by
  intro q r h
  ext ki
  have hi := congrArg (fun c : FourierCoeff => c ki.1.val ki.2) h
  simpa [extendCoeff, ki.1.property] using hi

/-- Reality and solenoidality are actual finite coefficient equations. -/
def phaseSubmodule (N : ℕ) : Submodule ℝ (AmbientPhase N) where
  carrier := {q | SpectralReality (extendCoeff q) ∧
    SpectralSolenoidal (extendCoeff q)}
  zero_mem' := by
    constructor
    · intro k i
      simp
    · intro k
      simp
  add_mem' := by
    intro q r hq hr
    constructor
    · intro k i
      simp only [extendCoeff_add, Pi.add_apply, star_add, hq.1 k i, hr.1 k i]
    · intro k
      simp only [extendCoeff_add, Pi.add_apply, mul_add, Finset.sum_add_distrib,
        hq.2 k, hr.2 k, add_zero]
  smul_mem' := by
    intro r q hq
    constructor
    · intro k i
      simp only [extendCoeff_real_smul, Pi.smul_apply]
      change (r : ℂ) * extendCoeff q (-k) i =
        star ((r : ℂ) * extendCoeff q k i)
      rw [hq.1 k i, star_mul]
      simp
    · intro k
      simp only [extendCoeff_real_smul, Pi.smul_apply]
      change (∑ i : Fin 3, (k i : ℂ) * ((r : ℂ) * extendCoeff q k i)) = 0
      calc
        _ = (r : ℂ) * ∑ i : Fin 3, (k i : ℂ) * extendCoeff q k i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = 0 := by rw [hq.2 k, mul_zero]

abbrev Phase (N : ℕ) := ↥(phaseSubmodule N)

instance phaseFiniteDimensional (N : ℕ) : FiniteDimensional ℝ (Phase N) := by
  infer_instance

instance phaseCompleteSpace (N : ℕ) : CompleteSpace (Phase N) := by
  infer_instance

def phaseCoeff {N : ℕ} (q : Phase N) : FourierCoeff :=
  extendCoeff q.val

theorem phaseCoeff_reality {N : ℕ} (q : Phase N) :
    SpectralReality (phaseCoeff q) := q.property.1

theorem phaseCoeff_solenoidal {N : ℕ} (q : Phase N) :
    SpectralSolenoidal (phaseCoeff q) := q.property.2

theorem phaseCoeff_support {N : ℕ} (q : Phase N) (k : Frequency)
    (hk : k ∉ fullModes N) (i : Fin 3) : phaseCoeff q k i = 0 := by
  simp [phaseCoeff, extendCoeff, hk]

@[simp]
theorem phaseCoeff_zero (N : ℕ) : phaseCoeff (0 : Phase N) = 0 := by
  exact extendCoeff_zero N

def meanAmbient (N : ℕ) (m : Vec) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => if ki.1.val = 0 then (m ki.2 : ℂ) else 0)

theorem meanAmbient_coeff (N : ℕ) (m : Vec) (k : Frequency) (i : Fin 3) :
    extendCoeff (meanAmbient N m) k i = if k = 0 then (m i : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [extendCoeff, meanAmbient, zero_mem_fullModes]
  · by_cases hm : k ∈ fullModes N <;> simp [extendCoeff, meanAmbient, hm, hk]

theorem meanAmbient_mem (N : ℕ) (m : Vec) : meanAmbient N m ∈ phaseSubmodule N := by
  constructor
  · intro k i
    rw [meanAmbient_coeff, meanAmbient_coeff]
    by_cases hk : k = 0 <;> simp [hk]
  · intro k
    simp_rw [meanAmbient_coeff]
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]

def meanPhase (N : ℕ) (m : Vec) : Phase N :=
  ⟨meanAmbient N m, meanAmbient_mem N m⟩

theorem meanPhase_coeff (N : ℕ) (m : Vec) (k : Frequency) (i : Fin 3) :
    phaseCoeff (meanPhase N m) k i = if k = 0 then (m i : ℂ) else 0 :=
  meanAmbient_coeff N m k i

theorem meanPhase_injective (N : ℕ) : Function.Injective (meanPhase N) := by
  intro m n h
  ext i
  have hi := congrArg (fun q : Phase N => (phaseCoeff q 0 i).re) h
  simpa [meanPhase_coeff] using hi

instance phaseNontrivial (N : ℕ) : Nontrivial (Phase N) :=
  Function.Injective.nontrivial (meanPhase_injective N)

theorem phase_finrank_pos (N : ℕ) : 0 < Module.finrank ℝ (Phase N) :=
  Module.finrank_pos

/-- The source Fourier-solenoidality argument uses no mean-zero premise. -/
theorem datumFourierCoeff_solenoidal (a : Field)
    (hs : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) :
    SpectralSolenoidal (datumFourierCoeff a) := by
  intro k
  have hzero := integral_unitCube_divergence_eq_zero
    (fun i => datumFourierIntegrand a k i)
    (fun i => datumFourierIntegrand_contDiff hs k i)
    (fun i x => datumFourierIntegrand_periodic hp k i x i)
  have hsum (x : Vec) :
      (∑ i : Fin 3, fderiv ℝ (datumFourierIntegrand a k i) x (unitVector i)) =
        -(∑ i : Fin 3, derivativeSymbol i k * datumFourierIntegrand a k i x) := by
    simp_rw [datumFourierIntegrand_coordinateDerivative
      (hs.differentiable (by simp))]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum]
    change star (fourierCharacter k x) * (divergence a x : ℂ) - _ = _
    rw [hd x]
    simp
  simp_rw [hsum] at hzero
  rw [integral_neg] at hzero
  have hcoeff : (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff a k i) = 0 := by
    have h := neg_eq_zero.mp hzero
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (datumFourierIntegrand_integrableOn hs.continuous k i).const_mul
        (derivativeSymbol i k))] at h
    simpa only [integral_const_mul, datumFourierCoeff] using h
  let C : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hfactor :
      (∑ i : Fin 3, derivativeSymbol i k * datumFourierCoeff a k i) =
        C * ∑ i : Fin 3, (k i : ℂ) * datumFourierCoeff a k i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_intCast, C]
    ring
  have hC : C ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  rw [hfactor] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left hC

def initialAmbient (N : ℕ) (a : Field) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => datumFourierCoeff a ki.1.val ki.2)

theorem initialAmbient_coeff (N : ℕ) (a : Field) (k : Frequency) (i : Fin 3) :
    extendCoeff (initialAmbient N a) k i =
      if k ∈ fullModes N then datumFourierCoeff a k i else 0 := by
  by_cases hk : k ∈ fullModes N <;> simp [extendCoeff, initialAmbient, hk]

theorem initialAmbient_mem (N : ℕ) (a : Field)
    (hs : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) :
    initialAmbient N a ∈ phaseSubmodule N := by
  constructor
  · intro k i
    rw [initialAmbient_coeff, initialAmbient_coeff]
    by_cases hk : k ∈ fullModes N
    · rw [if_pos hk, if_pos (fullModes_neg_mem hk)]
      exact datumFourierCoeff_reality a k i
    · rw [if_neg hk, if_neg ((fullModes_neg_mem_iff N k).not.mpr hk)]
      simp
  · intro k
    simp_rw [initialAmbient_coeff]
    by_cases hk : k ∈ fullModes N
    · simp only [if_pos hk]
      exact datumFourierCoeff_solenoidal a hs hp hd k
    · simp [hk]

def initialPhase (N : ℕ) (a : Field)
    (hs : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) : Phase N :=
  ⟨initialAmbient N a, initialAmbient_mem N a hs hp hd⟩

theorem initialPhase_coeff (N : ℕ) (a : Field)
    (hs : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) (k : Frequency) (i : Fin 3) :
    phaseCoeff (initialPhase N a hs hp hd) k i =
      if k ∈ fullModes N then datumFourierCoeff a k i else 0 :=
  initialAmbient_coeff N a k i

theorem initialPhase_mean (N : ℕ) (a : Field)
    (hs : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) (i : Fin 3) :
    phaseCoeff (initialPhase N a hs hp hd) 0 i = (spatialMean a i : ℂ) := by
  rw [initialPhase_coeff, if_pos (zero_mem_fullModes N)]
  exact datumFourierCoeff_zero
    (hs.continuous.continuousOn.integrableOn_compact isCompact_unitCube) i

/-- The exact arbitrary-mean datum contract of the parent repository. -/
def initialPhaseData (N : ℕ) (a : NSEMaxwell.Classical.Field)
    (ha : NSEMaxwell.Classical.Data a) : Phase N :=
  initialPhase N a ha.smooth ha.periodic ha.divergence_free

theorem initialPhaseData_mean (N : ℕ) (a : NSEMaxwell.Classical.Field)
    (ha : NSEMaxwell.Classical.Data a) (i : Fin 3) :
    phaseCoeff (initialPhaseData N a ha) 0 i =
      (NSEMaxwell.Classical.spatialMean a i : ℂ) :=
  initialPhase_mean N a ha.smooth ha.periodic ha.divergence_free i

end

end QuantumAdapter
