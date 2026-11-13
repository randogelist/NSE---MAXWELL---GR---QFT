import GRAssembly.NativeCK
import GRAssembly.NativeGaussianInput
import GRAssembly.NativeFourier
import GRAssembly.NSE_GR_THREE_OBLIGATION_CLOSURE

/-!
Native discharge of the three literal literature signatures, followed by the
previously assembled exact local analytic NSE / marked five-dimensional
Gaussian vacuum-sector equivalence. The root has no literature-input parameter.
-/
set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.NativeLiterature

theorem literatureInputs_native : LiteratureInputs :=
  ⟨literatureAnalyticCKInput_native, literatureGaussianJetInput_native,
    literatureSmoothFourierInput_native⟩

theorem NSE_GR_NATIVE_LITERATURE_CLOSURE
    (ν ρ t0 : ℝ) (hν : 0 < ν) (hρ : ρ ≠ 0) :
    ExactSectorEquivalence ν ρ t0 :=
  NSEGR.Assembly.NSE_GR_THREE_OBLIGATION_CLOSURE ν ρ t0 hν hρ literatureInputs_native

end NSEGR.NativeLiterature
