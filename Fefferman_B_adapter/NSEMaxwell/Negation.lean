import NSEMaxwell.Constitutive

/-!
# Unconditional negation identities for the concrete operators

The totalized derivative, Bochner integral, and infinite sum all commute with
negation. Unlike additivity on arbitrary inputs, these statements require
neither differentiability, integrability, nor summability assumptions.

Consequently the concrete inverse Laplacian, Biot–Savart operator, and the
displayed constitutive differential commute with negation on all inputs.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

namespace NSEMaxwell.Classical

noncomputable section

@[simp] theorem coordinateDerivative_neg (a : Field) (i : Fin 3) :
    coordinateDerivative (-a) i = -coordinateDerivative a i := by
  funext x
  simp [coordinateDerivative, fderiv_neg]

@[simp] theorem spatialCurl_neg (a : Field) :
    spatialCurl (-a) = -spatialCurl a := by
  funext x
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [spatialCurl, coordinateDerivative_neg, PiLp.toLp_apply] <;> ring

@[simp] theorem vectorL_neg (a : Field) : vectorL (-a) = -vectorL a := by
  funext x
  simp only [vectorL, Pi.neg_apply, smul_neg, integral_neg, tsum_neg]

@[simp] theorem scalarL_neg (f : ScalarField) : scalarL (-f) = -scalarL f := by
  funext x
  simp only [scalarL, Pi.neg_apply, mul_neg, integral_neg, tsum_neg]

@[simp] theorem K_neg (a : Field) : K (-a) = -K a := by
  simp only [K, vectorL_neg, spatialCurl_neg]

/-- Actual DG negation, with no analytic premise. -/
@[simp] theorem DG_neg (ν : ℝ) (m : Vec) (B h : Field) :
    DG ν m B (-h) = -DG ν m B h :=
  NSEMaxwell.Constitutive.DG_neg_of_K_curl ν m B h (K_neg h) (spatialCurl_neg h)

/-- The former `DG_curl_neg` analytic obligation is an unconditional theorem. -/
theorem DG_curl_neg (ν : ℝ) (m : Vec) (B : Field) :
    DG ν m B (-spatialCurl (G ν m B)) =
      -DG ν m B (spatialCurl (G ν m B)) :=
  DG_neg ν m B (spatialCurl (G ν m B))

end

end NSEMaxwell.Classical
