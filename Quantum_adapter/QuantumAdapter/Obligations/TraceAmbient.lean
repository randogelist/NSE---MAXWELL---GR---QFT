import QuantumAdapter.Obligations.TraceProjection

/-!
Real trace on finite complex coordinates by an explicit rank-one resolution
of the identity. No ambient-real-basis construction is required.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuantumAdapter.Obligations

noncomputable section

open SingularClosure

def ambientSingle (N : ℕ) (ki : PhaseIndex N) (z : ℂ) : AmbientPhase N :=
  WithLp.toLp 2 (Pi.single ki z)

@[simp] theorem ambientSingle_apply (N : ℕ) (ki li : PhaseIndex N) (z : ℂ) :
    ambientSingle N ki z li = if li = ki then z else 0 := by
  simp [ambientSingle, Pi.single_apply]

def ambientRealCoordinate (N : ℕ) (ki : PhaseIndex N) : AmbientPhase N →ₗ[ℝ] ℝ where
  toFun q := (q ki).re
  map_add' q r := by simp
  map_smul' a q := by simp

def ambientImagCoordinate (N : ℕ) (ki : PhaseIndex N) : AmbientPhase N →ₗ[ℝ] ℝ where
  toFun q := (q ki).im
  map_add' q r := by simp
  map_smul' a q := by simp

theorem ambientSingle_resolution (N : ℕ) (q : AmbientPhase N) :
    q = ∑ ki : PhaseIndex N,
      ((q ki).re • ambientSingle N ki 1 + (q ki).im • ambientSingle N ki Complex.I) := by
  ext li
  simp [ambientSingle_apply, Complex.re_add_im]

theorem ambientEndomorphism_resolution (N : ℕ)
    (f : AmbientPhase N →ₗ[ℝ] AmbientPhase N) :
    f = ∑ ki : PhaseIndex N,
      ((ambientRealCoordinate N ki).smulRight (f (ambientSingle N ki 1)) +
        (ambientImagCoordinate N ki).smulRight (f (ambientSingle N ki Complex.I))) := by
  apply LinearMap.ext
  intro q
  simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smulRight_apply]
  change f q = ∑ ki : PhaseIndex N,
    ((q ki).re • f (ambientSingle N ki 1) + (q ki).im • f (ambientSingle N ki Complex.I))
  calc
    f q = f (∑ ki : PhaseIndex N,
        ((q ki).re • ambientSingle N ki 1 +
          (q ki).im • ambientSingle N ki Complex.I)) := congrArg f (ambientSingle_resolution N q)
    _ = _ := by simp only [map_sum, map_add, map_smul]

theorem ambient_real_trace_formula (N : ℕ)
    (f : AmbientPhase N →ₗ[ℝ] AmbientPhase N) :
    LinearMap.trace ℝ (AmbientPhase N) f =
      ∑ ki : PhaseIndex N,
        ((f (ambientSingle N ki 1) ki).re + (f (ambientSingle N ki Complex.I) ki).im) := by
  conv_lhs => rw [ambientEndomorphism_resolution N f]
  simp only [map_sum, map_add, LinearMap.trace_smulRight,
    ambientRealCoordinate, ambientImagCoordinate]

end
end QuantumAdapter.Obligations
