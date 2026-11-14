import SingularClosure.FourierTransport

/-!
# Actual infinite Fourier NSE coefficient right hand side

Exact definition extracted from `StrongCoefficientContracts.lean` at Methlib
commit 4813604a46179c745b82f51bee51a186e9f4cc2d. No trajectory contract is imported;
the coefficient formula has unrestricted zero mode.
-/

set_option autoImplicit false
namespace SingularClosure
noncomputable section

def fullFourierRhs (ν : ℝ) (c : TorusSobolev 0)
    (k : Frequency) (i : Fin 3) : ℂ :=
  -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c.val k i -
    coefficientLeray k (fun j => divergenceTransportCoefficient k j c c) i

end
end SingularClosure
