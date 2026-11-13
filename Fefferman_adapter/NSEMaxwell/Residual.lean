import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Abel

/-!
# Explicit residual algebra for the NSE--Maxwell correspondence

This module proves algebraic implications from explicitly named identities.
It does not instantiate the actual periodic differential operators and does
not assert Fefferman B. The analytic realization must discharge the hypotheses
used below before any theorem is identified with the concrete PDE equivalence.

No compiler run is performed in the authoring environment.
-/

namespace NSEMaxwell.Residual

variable {V : Type*} [AddCommGroup V]

/-- The momentum residual, with viscosity already included in viscousLap. -/
def momentumResidual (uTime convection gradPressure viscousLap : V) : V :=
  uTime + convection + gradPressure - viscousLap

/-- The Faraday residual. -/
def faradayResidual (bTime curlElectric : V) : V :=
  bTime + curlElectric

/-- The Ampere residual, with cSquaredCurlB = c^2 curl B. -/
def ampereResidual (eTime cSquaredCurlB current : V) : V :=
  eTime - cSquaredCurlB + current

/-- The prescribed spatial current once the nonlinear evolution vector is fixed. -/
def inducedCurrent (DG : V →+ V) (cSquaredCurlB evolution : V) : V :=
  cSquaredCurlB - DG evolution

/-- The Hodge identity suffices for the normalized residual factorization. -/
theorem hodge_momentum_factorization
    (K : V →+ V)
    (bTime electric gradHead curlElectric : V)
    (hHodge : electric + gradHead = K curlElectric) :
    K bTime + electric + gradHead =
      K (faradayResidual bTime curlElectric) := by
  calc
    K bTime + electric + gradHead =
        K bTime + (electric + gradHead) := by abel
    _ = K bTime + K curlElectric := by rw [hHodge]
    _ = K (faradayResidual bTime curlElectric) := by
      simp only [faradayResidual, map_add]

/-- Derive the momentum factorization from the explicit kinematic identities.

hConvection is the Lamb identity, hPressure is the normalized Bernoulli
pressure split, hViscosity is the curl--Laplacian identity, and hHodge
is the mean-zero periodic Hodge identity for the electric field.
-/
theorem momentum_factorization
    (K : V →+ V)
    (uTime bTime convection gradPressure viscousLap : V)
    (lamb kineticGradient gradHead diffusionCurl curlElectric : V)
    (hTime : uTime = K bTime)
    (hConvection : convection = lamb + kineticGradient)
    (hPressure : gradPressure = gradHead - kineticGradient)
    (hViscosity : viscousLap = -diffusionCurl)
    (hHodge : (lamb + diffusionCurl) + gradHead = K curlElectric) :
    momentumResidual uTime convection gradPressure viscousLap =
      K (faradayResidual bTime curlElectric) := by
  calc
    momentumResidual uTime convection gradPressure viscousLap =
        K bTime + (lamb + diffusionCurl) + gradHead := by
      unfold momentumResidual
      rw [hTime, hConvection, hPressure, hViscosity]
      abel
    _ = K (faradayResidual bTime curlElectric) :=
      hodge_momentum_factorization K bTime
        (lamb + diffusionCurl) gradHead curlElectric hHodge

/-- Reconstruction is injective at zero whenever curl is its left inverse
at the particular admissible residual. -/
theorem reconstructed_zero_iff
    (K curl : V →+ V) (r : V)
    (hReconstruct : curl (K r) = r) :
    K r = 0 ↔ r = 0 := by
  constructor
  · intro h
    calc
      r = curl (K r) := hReconstruct.symm
      _ = curl 0 := congrArg curl h
      _ = 0 := map_zero curl
  · intro h
    rw [h, map_zero]

/-- A factored momentum residual vanishes exactly when Faraday's does. -/
theorem factored_zero_iff
    (K curl : V →+ V) (momentum faraday : V)
    (hFactor : momentum = K faraday)
    (hReconstruct : curl (K faraday) = faraday) :
    momentum = 0 ↔ faraday = 0 := by
  rw [hFactor]
  exact reconstructed_zero_iff K curl faraday hReconstruct

/-- Changing the pressure gradient adds precisely that gradient difference. -/
theorem momentum_pressure_change
    (uTime convection gradPressure canonicalGradPressure viscousLap difference : V)
    (hPressure : gradPressure = canonicalGradPressure + difference) :
    momentumResidual uTime convection gradPressure viscousLap =
      momentumResidual uTime convection canonicalGradPressure viscousLap + difference := by
  unfold momentumResidual
  rw [hPressure]
  abel

/-- Separate the solenoidal residual and a curl-free pressure correction.

The conclusion is an equality of gradient fields. The separate analytic
fact that a smooth periodic scalar with zero gradient is spatially constant
is not asserted by this algebraic lemma.
-/
theorem gradient_split_zero_iff
    (K curl : V →+ V) (faraday pressureGradient : V)
    (hReconstruct : curl (K faraday) = faraday)
    (hCurlGradient : curl pressureGradient = 0) :
    K faraday + pressureGradient = 0 ↔
      faraday = 0 ∧ pressureGradient = 0 := by
  constructor
  · intro h
    have hFaraday : faraday = 0 := by
      have hCurl := congrArg curl h
      simpa only [map_add, hReconstruct, hCurlGradient, add_zero, map_zero] using hCurl
    have hGradient : pressureGradient = 0 := by
      simpa only [hFaraday, map_zero, zero_add] using h
    exact ⟨hFaraday, hGradient⟩
  · intro h
    simp only [h.1, h.2, map_zero, zero_add]

/-- Ampere factorization follows from the chain rule and fixed spatial current.

No Faraday equation is assumed. The derivative DG is additive because it
is the derivative of the constitutive map at a fixed field.
-/
theorem ampere_factorization
    (DG : V →+ V)
    (eTime bTime cSquaredCurlB evolution curlElectric : V)
    (hChainRule : eTime = DG bTime)
    (hEvolution : evolution = -curlElectric) :
    ampereResidual eTime cSquaredCurlB
        (inducedCurrent DG cSquaredCurlB evolution) =
      DG (faradayResidual bTime curlElectric) := by
  unfold ampereResidual inducedCurrent faradayResidual
  rw [hChainRule, hEvolution, map_add, map_neg]
  abel

/-- The four Maxwell equations written as vanishing residuals. -/
def MaxwellResiduals {S : Type*} [Zero S]
    (gaussMagnetic : S) (faraday : V)
    (gaussElectric : S) (ampere : V) : Prop :=
  gaussMagnetic = 0 ∧ faraday = 0 ∧ gaussElectric = 0 ∧ ampere = 0

/-- On the explicitly prescribed constitutive graph, the full Maxwell
system is equivalent to its Faraday equation. -/
theorem full_maxwell_iff_faraday
    {S : Type*} [Zero S]
    (DG : V →+ V)
    (gaussMagnetic gaussElectric : S)
    (faraday ampere : V)
    (hGaussMagnetic : gaussMagnetic = 0)
    (hGaussElectric : gaussElectric = 0)
    (hAmpere : ampere = DG faraday) :
    MaxwellResiduals gaussMagnetic faraday gaussElectric ampere ↔
      faraday = 0 := by
  constructor
  · intro h
    exact h.2.1
  · intro hFaraday
    refine ⟨hGaussMagnetic, hFaraday, hGaussElectric, ?_⟩
    calc
      ampere = DG faraday := hAmpere
      _ = DG 0 := congrArg DG hFaraday
      _ = 0 := map_zero DG

/-- Algebraic residual equivalence, with every analytic input explicit.

This is not the concrete Fefferman-B theorem. It is the residual theorem
to be instantiated after the actual periodic analytic identities are proved.
-/
theorem momentum_zero_iff_full_maxwell
    {S : Type*} [Zero S]
    (K curl DG : V →+ V)
    (gaussMagnetic gaussElectric : S)
    (momentum faraday ampere : V)
    (hFactor : momentum = K faraday)
    (hReconstruct : curl (K faraday) = faraday)
    (hGaussMagnetic : gaussMagnetic = 0)
    (hGaussElectric : gaussElectric = 0)
    (hAmpere : ampere = DG faraday) :
    momentum = 0 ↔
      MaxwellResiduals gaussMagnetic faraday gaussElectric ampere := by
  exact
    (factored_zero_iff K curl momentum faraday hFactor hReconstruct).trans
      (full_maxwell_iff_faraday DG gaussMagnetic gaussElectric faraday ampere
        hGaussMagnetic hGaussElectric hAmpere).symm

end NSEMaxwell.Residual

