import QuantumAdapter.Obligations.TraceViscous

/-!
Explicit algebraic retraction from the ambient complex coefficient space
onto the constrained real phase. It supplies the cyclic-trace computation
without choosing a basis of every transverse plane.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure

def realityAverage (N : ℕ) (a : AmbientPhase N) : FourierCoeff :=
  fun k i => (extendCoeff a k i + star (extendCoeff a (-k) i)) / 2

theorem realityAverage_reality (N : ℕ) (a : AmbientPhase N) :
    SpectralReality (realityAverage N a) := by
  intro k i
  simp [realityAverage, add_comm]

theorem realityAverage_support (N : ℕ) (a : AmbientPhase N)
    (k : Frequency) (hk : k ∉ fullModes N) (i : Fin 3) :
    realityAverage N a k i = 0 := by
  simp [realityAverage, extendCoeff, hk, (fullModes_neg_mem_iff N k).not.mpr hk]

theorem realityAverage_add (N : ℕ) (a b : AmbientPhase N) :
    realityAverage N (a + b) = realityAverage N a + realityAverage N b := by
  funext k i
  simp only [realityAverage, extendCoeff_add, Pi.add_apply, star_add]
  ring

theorem realityAverage_smul (N : ℕ) (s : ℝ) (a : AmbientPhase N) :
    realityAverage N (s • a) = s • realityAverage N a := by
  funext k i
  simp only [realityAverage, extendCoeff_real_smul, Pi.smul_apply]
  change ((s : ℂ) * extendCoeff a k i + star ((s : ℂ) * extendCoeff a (-k) i)) / 2 =
    (s : ℂ) * ((extendCoeff a k i + star (extendCoeff a (-k) i)) / 2)
  rw [star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

def lerayRealityAmbient (N : ℕ) (a : AmbientPhase N) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => coefficientLeray ki.1.val (realityAverage N a ki.1.val) ki.2)

theorem lerayRealityAmbient_coeff (N : ℕ) (a : AmbientPhase N)
    (k : Frequency) (i : Fin 3) :
    extendCoeff (lerayRealityAmbient N a) k i =
      coefficientLeray k (realityAverage N a k) i := by
  by_cases hk : k ∈ fullModes N
  · simp [lerayRealityAmbient, extendCoeff, hk]
  · have hz : realityAverage N a k = 0 := by
      funext j
      exact realityAverage_support N a k hk j
    simp [lerayRealityAmbient, extendCoeff, hk, hz, coefficientLeray_zero]

theorem lerayRealityAmbient_mem (N : ℕ) (a : AmbientPhase N) :
    lerayRealityAmbient N a ∈ phaseSubmodule N := by
  constructor
  · intro k i
    rw [lerayRealityAmbient_coeff, lerayRealityAmbient_coeff]
    have hr : realityAverage N a (-k) = fun j => star (realityAverage N a k j) := by
      funext j
      exact realityAverage_reality N a k j
    rw [hr, coefficientLeray_neg_star]
  · intro k
    simp_rw [lerayRealityAmbient_coeff]
    exact coefficientLeray_solenoidal k (realityAverage N a k)

def phaseRetraction (N : ℕ) : AmbientPhase N →ₗ[ℝ] Phase N where
  toFun a := ⟨lerayRealityAmbient N a, lerayRealityAmbient_mem N a⟩
  map_add' a b := by
    apply Subtype.ext
    ext ki
    simp [lerayRealityAmbient, realityAverage_add, Pi.add_apply,
      coefficientLeray_add_native]
  map_smul' s a := by
    apply Subtype.ext
    ext ki
    simp [lerayRealityAmbient, realityAverage_smul, Pi.smul_apply,
      coefficientLeray_real_smul_native]

theorem phaseRetraction_coeff (N : ℕ) (a : AmbientPhase N)
    (k : Frequency) (i : Fin 3) :
    phaseCoeff (phaseRetraction N a) k i =
      coefficientLeray k (realityAverage N a k) i :=
  lerayRealityAmbient_coeff N a k i

theorem realityAverage_phase (N : ℕ) (q : Phase N) :
    realityAverage N q.val = phaseCoeff q := by
  funext k i
  change (phaseCoeff q k i + star (phaseCoeff q (-k) i)) / 2 = phaseCoeff q k i
  rw [phaseCoeff_reality q k i, star_star]
  ring

theorem coefficientLeray_phase (N : ℕ) (q : Phase N) (k : Frequency) :
    coefficientLeray k (phaseCoeff q k) = phaseCoeff q k := by
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp [coefficientLeray, hk, phaseCoeff_solenoidal q k]

theorem phaseRetraction_subtype (N : ℕ) (q : Phase N) :
    phaseRetraction N q.val = q := by
  apply Subtype.ext
  apply extendCoeff_injective N
  funext k i
  change phaseCoeff (phaseRetraction N q.val) k i = phaseCoeff q k i
  rw [phaseRetraction_coeff, realityAverage_phase, coefficientLeray_phase]

theorem phaseRetraction_comp_subtype (N : ℕ) :
    (phaseRetraction N).comp (phaseSubmodule N).subtype = LinearMap.id := by
  ext q
  exact phaseRetraction_subtype N q

theorem phaseLaplacian_trace_eq_ambient (N : ℕ) :
    LinearMap.trace ℝ (Phase N) (phaseLaplacian N) =
      LinearMap.trace ℝ (AmbientPhase N)
        ((phaseSubmodule N).subtype.comp ((phaseLaplacian N).comp (phaseRetraction N))) := by
  have hc := LinearMap.trace_comp_comm'
    (phaseSubmodule N).subtype ((phaseLaplacian N).comp (phaseRetraction N))
  have heq : ((phaseLaplacian N).comp (phaseRetraction N)).comp
      (phaseSubmodule N).subtype = phaseLaplacian N := by
    ext q
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, phaseRetraction_subtype]
  rw [heq] at hc
  exact hc

end
end QuantumAdapter.Obligations
