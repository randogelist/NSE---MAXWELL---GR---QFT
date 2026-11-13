import GRAssembly.NativeGaussianJet
import GRAssembly.NativeCK

/-! Native instantiation of the exact Gaussian literature endpoint. -/
set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.NativeLiterature

theorem literatureGaussianJetInput_native : NSEGR.LiteratureGaussianJetInput :=
  literatureGaussianJetInput_of_analyticCK literatureAnalyticCKInput_native

end NSEGR.NativeLiterature
