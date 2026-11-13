import QuantumAdapter.Assembly.Flow
import QuantumAdapter.Assembly.Fourier

/-! The actual full-mode convolution as a continuous real bilinear phase map. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

def fullBilinearTransport (N : ℕ) (a b : FourierCoeff) (k : Frequency)
    (i : Fin 3) : ℂ :=
  ∑ p ∈ fullModes N,
    (∑ j : Fin 3, a p j * derivativeSymbol j (k - p)) * b (k - p) i

theorem fullBilinearTransport_self (N : ℕ) (a : FourierCoeff) :
    fullBilinearTransport N a a = fullTransport N a := by
  funext k i
  simp only [fullBilinearTransport, fullTransport, derivativeSymbol, Pi.sub_apply]

theorem fullBilinearTransport_add_left (N : ℕ) (a b c : FourierCoeff) :
    fullBilinearTransport N (a + b) c =
      fullBilinearTransport N a c + fullBilinearTransport N b c := by
  funext k i
  simp only [fullBilinearTransport, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem fullBilinearTransport_add_right (N : ℕ) (a b c : FourierCoeff) :
    fullBilinearTransport N a (b + c) =
      fullBilinearTransport N a b + fullBilinearTransport N a c := by
  funext k i
  simp only [fullBilinearTransport, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem fullBilinearTransport_smul_left (N : ℕ) (s : ℝ) (a b : FourierCoeff) :
    fullBilinearTransport N (s • a) b = s • fullBilinearTransport N a b := by
  funext k i
  simp only [fullBilinearTransport, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum]

theorem fullBilinearTransport_smul_right (N : ℕ) (s : ℝ) (a b : FourierCoeff) :
    fullBilinearTransport N a (s • b) = s • fullBilinearTransport N a b := by
  funext k i
  simp only [fullBilinearTransport, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum]

theorem coefficientLeray_add_native (k : Frequency) (a b : Fin 3 → ℂ) :
    coefficientLeray k (a + b) = coefficientLeray k a + coefficientLeray k b := by
  classical
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, hk, if_false, Pi.add_apply, mul_add,
      Finset.sum_add_distrib, add_div]
    ring

theorem coefficientLeray_real_smul_native (k : Frequency) (s : ℝ) (a : Fin 3 → ℂ) :
    coefficientLeray k (s • a) = s • coefficientLeray k a := by
  classical
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, hk, if_false, Pi.smul_apply, Complex.real_smul,
      ← Finset.mul_sum]
    ring

/-- Signed nonlinear ambient vector field; the zero mode is fixed. -/
def bilinearAmbient (N : ℕ) (q r : Phase N) : AmbientPhase N :=
  WithLp.toLp 2 (fun ki => if ki.1.val = 0 then 0 else
    -coefficientLeray ki.1.val
      (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) ki.1.val) ki.2)

theorem bilinearAmbient_add_left (N : ℕ) (q r s : Phase N) :
    bilinearAmbient N (q + r) s = bilinearAmbient N q s + bilinearAmbient N r s := by
  ext ki
  simp only [bilinearAmbient, Assembly.phaseCoeff_add, fullBilinearTransport_add_left,
    Pi.add_apply]
  by_cases hk : ki.1.val = 0
  · simp [hk]
  · simp only [hk, if_false, coefficientLeray_add_native, Pi.add_apply, neg_add_rev]
    ring

theorem bilinearAmbient_add_right (N : ℕ) (q r s : Phase N) :
    bilinearAmbient N q (r + s) = bilinearAmbient N q r + bilinearAmbient N q s := by
  ext ki
  simp only [bilinearAmbient, Assembly.phaseCoeff_add, fullBilinearTransport_add_right,
    Pi.add_apply]
  by_cases hk : ki.1.val = 0
  · simp [hk]
  · simp only [hk, if_false, coefficientLeray_add_native, Pi.add_apply, neg_add_rev]
    ring

theorem bilinearAmbient_smul_left (N : ℕ) (s : ℝ) (q r : Phase N) :
    bilinearAmbient N (s • q) r = s • bilinearAmbient N q r := by
  ext ki
  simp only [bilinearAmbient, Assembly.phaseCoeff_smul, fullBilinearTransport_smul_left,
    Pi.smul_apply]
  by_cases hk : ki.1.val = 0
  · simp [hk]
  · simp [hk, coefficientLeray_real_smul_native, smul_neg]

theorem bilinearAmbient_smul_right (N : ℕ) (s : ℝ) (q r : Phase N) :
    bilinearAmbient N q (s • r) = s • bilinearAmbient N q r := by
  ext ki
  simp only [bilinearAmbient, Assembly.phaseCoeff_smul, fullBilinearTransport_smul_right,
    Pi.smul_apply]
  by_cases hk : ki.1.val = 0
  · simp [hk]
  · simp [hk, coefficientLeray_real_smul_native, smul_neg]

/-- Actual projected signed convection. No tangency premise is introduced. -/
def bilinearConvection (N : ℕ) (q r : Phase N) : Phase N :=
  (phaseSubmodule N).orthogonalProjectionOnto (bilinearAmbient N q r)

theorem bilinearConvection_add_left (N : ℕ) (q r s : Phase N) :
    bilinearConvection N (q + r) s = bilinearConvection N q s + bilinearConvection N r s := by
  simp [bilinearConvection, bilinearAmbient_add_left]

theorem bilinearConvection_add_right (N : ℕ) (q r s : Phase N) :
    bilinearConvection N q (r + s) = bilinearConvection N q r + bilinearConvection N q s := by
  simp [bilinearConvection, bilinearAmbient_add_right]

theorem bilinearConvection_smul_left (N : ℕ) (s : ℝ) (q r : Phase N) :
    bilinearConvection N (s • q) r = s • bilinearConvection N q r := by
  simp [bilinearConvection, bilinearAmbient_smul_left]

theorem bilinearConvection_smul_right (N : ℕ) (s : ℝ) (q r : Phase N) :
    bilinearConvection N q (s • r) = s • bilinearConvection N q r := by
  simp [bilinearConvection, bilinearAmbient_smul_right]

def bilinearConvectionRight (N : ℕ) (q : Phase N) : Phase N →ₗ[ℝ] Phase N where
  toFun := bilinearConvection N q
  map_add' := bilinearConvection_add_right N q
  map_smul' := by intro s r; exact bilinearConvection_smul_right N s q r

def bilinearConvectionRightCLM (N : ℕ) (q : Phase N) : Phase N →L[ℝ] Phase N :=
  { toLinearMap := bilinearConvectionRight N q
    cont := (bilinearConvectionRight N q).continuous_of_finiteDimensional }

def bilinearConvectionLinear (N : ℕ) : Phase N →ₗ[ℝ] Phase N →L[ℝ] Phase N where
  toFun := bilinearConvectionRightCLM N
  map_add' := by intro q r; ext s; exact bilinearConvection_add_left N q r s
  map_smul' := by intro a q; ext r; exact bilinearConvection_smul_left N a q r

def bilinearConvectionCLM (N : ℕ) : Phase N →L[ℝ] Phase N →L[ℝ] Phase N :=
  { toLinearMap := bilinearConvectionLinear N
    cont := (bilinearConvectionLinear N).continuous_of_finiteDimensional }

@[simp] theorem bilinearConvectionCLM_apply (N : ℕ) (q r : Phase N) :
    bilinearConvectionCLM N q r = bilinearConvection N q r := rfl

theorem bilinearAmbient_self (N : ℕ) (q : Phase N) :
    bilinearAmbient N q q = rawRhs 0 N q := by
  ext ki
  simp [bilinearAmbient, fullBilinearTransport_self, rawRhs]

theorem bilinearConvection_self (N : ℕ) (q : Phase N) :
    bilinearConvection N q q = drift 0 N q := by
  simp only [bilinearConvection, bilinearAmbient_self, drift]

end
end QuantumAdapter.Obligations
