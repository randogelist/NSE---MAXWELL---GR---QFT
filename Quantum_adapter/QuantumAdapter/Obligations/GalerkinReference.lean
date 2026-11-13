import QuantumAdapter.Obligations.GalerkinBootstrap
import QuantumAdapter.Assembly.Galerkin

/-!
# The actual Fourier projection of a native classical reference solution

Spatial smoothness and divergence constraints are extracted from NSSolution.
The projected reference and the actual phase error retain arbitrary means.
The initial error is zero by the native strong initial trace. The finite-tail
assembly below uses their literal energy bounds; it is not itself P6.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations

open SingularClosure QuantumAdapter.Assembly NSEMaxwell.Classical

noncomputable section

variable {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}

/-- Every nonnegative-time spatial slice of the actual solution is native admissible data. -/
theorem NSSolution.spatial_data (h : NSSolution ν a u p) (t : ℝ) (ht : 0 ≤ t) :
    Data (u t) := by
  refine ⟨?_, h.velocity_periodic t ht, h.divergence_free t ht⟩
  have hmap : ContDiff ℝ ∞ (fun x : Vec => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using
    h.velocity_smooth.comp_contDiff hmap (fun x => ht)

/-- All integral Sobolev orders at a reference time are actual Methlib memberships. -/
theorem NSSolution.spatial_all_sobolev (h : NSSolution ν a u p)
    (t : ℝ) (ht : 0 ≤ t) (s : ℕ) :
    Memℓp (sobolevWeightedCoeff s (datumFourierCoeff (u t))) 2 :=
  SMOOTH_DATUM_MEM_TORUS_SOBOLEV s (u t)
    (h.spatial_data t ht).smooth (h.spatial_data t ht).periodic

/-- Full-mode Fourier projection of the actual reference solution.
The arbitrary negative-time branch is immaterial for all stated predicates. -/
def referenceProjection (h : NSSolution ν a u p) (N : ℕ) (t : ℝ) : Phase N :=
  if ht : 0 ≤ t then initialPhaseData N (u t) (h.spatial_data t ht) else 0

theorem referenceProjection_eq (h : NSSolution ν a u p) (N : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    referenceProjection h N t = initialPhaseData N (u t) (h.spatial_data t ht) := by
  simp only [referenceProjection, dif_pos ht]

theorem referenceProjection_coeff (h : NSSolution ν a u p) (N : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
    phaseCoeff (referenceProjection h N t) k i =
      if k ∈ fullModes N then datumFourierCoeff (u t) k i else 0 := by
  rw [referenceProjection_eq h N t ht]
  exact initialPhase_coeff N (u t) (h.spatial_data t ht).smooth
    (h.spatial_data t ht).periodic (h.spatial_data t ht).divergence_free k i

/-- The projected reference inherits the exact initial data, including its mean. -/
theorem referenceProjection_initial (h : NSSolution ν a u p)
    (ha : Data a) (N : ℕ) :
    referenceProjection h N 0 = initialPhaseData N a ha := by
  rw [referenceProjection_eq h N 0 le_rfl]
  cases h.initial
  rfl

/-- Each reference projection has a constructed all-order smooth-data bound. -/
theorem referenceProjection_sobolevEnergy_le (h : NSSolution ν a u p)
    (s N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    sobolevEnergy s N (referenceProjection h N t) ≤ initialSobolevMajorant s (u t) := by
  rw [referenceProjection_eq h N t ht]
  exact initialPhaseData_sobolevEnergy_le_majorant s N (u t) (h.spatial_data t ht)

/-- The exact phase error between the actual Galerkin orbit and projected reference. -/
def referenceError (F : PhaseFlow ν) (h : NSSolution ν a u p)
    (ha : Data a) (N : ℕ) (t : ℝ) : Phase N :=
  F.map N t (initialPhaseData N a ha) - referenceProjection h N t

/-- The actual initial trace makes the error zero without an approximation premise. -/
theorem referenceError_initial (F : PhaseFlow ν) (h : NSSolution ν a u p)
    (ha : Data a) (N : ℕ) : referenceError F h ha N 0 = 0 := by
  unfold referenceError
  rw [F.map_zero, referenceProjection_initial h ha N]
  exact sub_self _

/-- The exact native error energy at every Sobolev order starts at zero. -/
theorem referenceError_sobolevEnergy_initial (F : PhaseFlow ν)
    (h : NSSolution ν a u p) (ha : Data a) (s N : ℕ) :
    sobolevEnergy s N (referenceError F h ha N 0) = 0 := by
  rw [referenceError_initial, sobolevEnergy_zero]

/-- Literal H3 phase triangle, specialized to the actual projected reference. -/
theorem centralEnergy_sqrt_le_error_add_reference (F : PhaseFlow ν)
    (h : NSSolution ν a u p) (ha : Data a) (N : ℕ) (t : ℝ) :
    Real.sqrt (centralEnergy F N a ha t) ≤
      Real.sqrt (energy3 N (referenceError F h ha N t)) +
      Real.sqrt (energy3 N (referenceProjection h N t)) :=
  sqrt_energy3_le_add N (F.map N t (initialPhaseData N a ha)) (referenceProjection h N t)

/-- The constructed reference/error energies feed the existing finite-cutoff completion. -/
theorem galerkinBoundAt_of_reference_error_tail (F : PhaseFlow ν)
    (h : NSSolution ν a u p) (ha : Data a) (T : ℝ) (K : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (href : ∀ N : ℕ, K ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      energy3 N (referenceProjection h N t) ≤ A ^ 2)
    (herr : ∀ N : ℕ, K ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      energy3 N (referenceError F h ha N t) ≤ B ^ 2) :
    GalerkinBoundAt F a ha T := by
  apply galerkinBoundAt_of_tail F a ha T K ((A + B) ^ 2)
  intro N hN t ht hT
  have hr := Real.sqrt_le_sqrt (href N hN t ht hT)
  have he := Real.sqrt_le_sqrt (herr N hN t ht hT)
  rw [Real.sqrt_sq hA] at hr
  rw [Real.sqrt_sq hB] at he
  have htri := centralEnergy_sqrt_le_error_add_reference F h ha N t
  have hn := Real.sqrt_nonneg (centralEnergy F N a ha t)
  have hs : Real.sqrt (centralEnergy F N a ha t) ≤ A + B := by linarith
  have hsq := pow_le_pow_left₀ hn hs 2
  rwa [Real.sq_sqrt (energy3_nonneg N _)] at hsq

end
end QuantumAdapter.Obligations
