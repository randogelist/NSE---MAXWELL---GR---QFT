import SingularClosure.FourierSobolevProduct
import SingularClosure.StrongCoefficientContracts
import SingularClosure.SobolevTrajectoryCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual smooth Fourier NSE vector field on every Sobolev scale

The unrestricted infinite divergence product is bundled as a continuous
bilinear map using its proved norm estimate. The actual vector field is the
linear viscous multiplier minus the Leray projection of its diagonal. All
coefficients agree with the full Fourier equation from the strong contract.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped ContDiff

namespace SingularClosure

noncomputable section

theorem sobolevDivergenceProduct_add_left (r : ℕ)
    (c e d : TorusSobolev (r + 2)) :
    sobolevDivergenceProduct r (c + e) d =
      sobolevDivergenceProduct r c d + sobolevDivergenceProduct r e d := by
  apply Subtype.ext
  funext k i
  change divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) (c + e))
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d) =
    divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d) +
    divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) e)
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d)
  simp only [map_add, ContinuousLinearMap.add_apply]

theorem sobolevDivergenceProduct_add_right (r : ℕ)
    (c d e : TorusSobolev (r + 2)) :
    sobolevDivergenceProduct r c (d + e) =
      sobolevDivergenceProduct r c d + sobolevDivergenceProduct r c e := by
  apply Subtype.ext
  funext k i
  change divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) (d + e)) =
    divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d) +
    divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) e)
  simp only [map_add]

theorem sobolevDivergenceProduct_smul_left (r : ℕ) (z : ℂ)
    (c d : TorusSobolev (r + 2)) :
    sobolevDivergenceProduct r (z • c) d = z • sobolevDivergenceProduct r c d := by
  apply Subtype.ext
  funext k i
  change divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) (z • c))
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d) =
    z * divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d)
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem sobolevDivergenceProduct_smul_right (r : ℕ) (z : ℂ)
    (c d : TorusSobolev (r + 2)) :
    sobolevDivergenceProduct r c (z • d) = z • sobolevDivergenceProduct r c d := by
  apply Subtype.ext
  funext k i
  change divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) (z • d)) =
    z * divergenceTransportCoefficient k i
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
      (torusSobolevLower 0 (r + 2) (Nat.zero_le _) d)
  simp only [map_smul, smul_eq_mul]

def sobolevDivergenceProductLinear (r : ℕ) :
    TorusSobolev (r + 2) →ₗ[ℂ] TorusSobolev (r + 2) →ₗ[ℂ] TorusSobolev r where
  toFun c :=
    { toFun := sobolevDivergenceProduct r c
      map_add' := fun d e => sobolevDivergenceProduct_add_right r c d e
      map_smul' := fun z d => sobolevDivergenceProduct_smul_right r z c d }
  map_add' c e := by
    ext d
    exact sobolevDivergenceProduct_add_left r c e d
  map_smul' z c := by
    ext d
    exact sobolevDivergenceProduct_smul_left r z c d

def sobolevDivergenceProductBilinear (r : ℕ) :
    TorusSobolev (r + 2) →L[ℂ] TorusSobolev (r + 2) →L[ℂ] TorusSobolev r :=
  (sobolevDivergenceProductLinear r).mkContinuous₂
    (SOBOLEV_DIVERGENCE_PRODUCT_NORM_BOUND r).choose
    (SOBOLEV_DIVERGENCE_PRODUCT_NORM_BOUND r).choose_spec.2

@[simp]
theorem sobolevDivergenceProductBilinear_apply (r : ℕ)
    (c d : TorusSobolev (r + 2)) :
    sobolevDivergenceProductBilinear r c d = sobolevDivergenceProduct r c d := rfl

theorem sobolevDivergenceProduct_diagonal_contDiff (r : ℕ) :
    ContDiff ℝ ∞ (fun c : TorusSobolev (r + 2) => sobolevDivergenceProduct r c c) := by
  have h : ContDiff ℂ ∞
      (fun c : TorusSobolev (r + 2) => sobolevDivergenceProductBilinear r c c) :=
    (sobolevDivergenceProductBilinear r).contDiff.clm_apply
      (contDiff_id : ContDiff ℂ ∞ (fun c : TorusSobolev (r + 2) => c))
  simpa only [sobolevDivergenceProductBilinear_apply] using h.restrict_scalars ℝ

/-- The literal infinite Fourier vector field, defined on every H(r+2) input. -/
def fourierSobolevRhs (ν : ℝ) (r : ℕ) (c : TorusSobolev (r + 2)) : TorusSobolev r :=
  torusSobolevViscous ν r c - torusSobolevLeray r (sobolevDivergenceProduct r c c)

theorem fourierSobolevRhs_contDiff (ν : ℝ) (r : ℕ) :
    ContDiff ℝ ∞ (fourierSobolevRhs ν r) := by
  have hv : ContDiff ℝ ∞ (torusSobolevViscous ν r) :=
    (torusSobolevViscous ν r).contDiff.restrict_scalars ℝ
  have hp : ContDiff ℝ ∞ (fun c : TorusSobolev (r + 2) =>
      torusSobolevLeray r (sobolevDivergenceProduct r c c)) :=
    ((torusSobolevLeray r).contDiff.restrict_scalars ℝ).comp
      (sobolevDivergenceProduct_diagonal_contDiff r)
  exact hv.sub hp

theorem fourierSobolevRhs_coefficient_eq_fullRhs (ν : ℝ) (r : ℕ)
    (c : TorusSobolev (r + 2)) :
    (fourierSobolevRhs ν r c).val =
      fullFourierRhs ν (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c) := by
  funext k i
  change (torusSobolevViscous ν r c).val k i -
    (torusSobolevLeray r (sobolevDivergenceProduct r c c)).val k i = _
  have htransport : sobolevDivergenceProductCoeff r c c k =
      (fun j => divergenceTransportCoefficient k j
        (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)
        (torusSobolevLower 0 (r + 2) (Nat.zero_le _) c)) := rfl
  rw [torusSobolevViscous_coeff, torusSobolevLeray_coeff,
    sobolevDivergenceProduct_coeff]
  simp only [fullFourierRhs, torusSobolevLower_coeff, lerayFourierCoeff]
  rw [htransport]

end

end SingularClosure
