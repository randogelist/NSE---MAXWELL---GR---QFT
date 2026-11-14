import GRAssembly.Strengthening.AnalyticalFrontier.WienerCarrier

/-!
The elementary scalar/numerical foundation together with the complete fixed
`ℓ¹` Fourier carrier. The remaining premise is now the nonlinear Wiener
construction itself.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

def ANALYTICAL_WIENER_CARRIER_FOUNDATION : Prop :=
  ANALYTICAL_WIENER_ELEMENTARY_FOUNDATION ∧
  ANALYTICAL_WIENER_CARRIER_CHECKPOINT

theorem ANALYTICAL_WIENER_CARRIER_FOUNDATION_NATIVE :
    ANALYTICAL_WIENER_CARRIER_FOUNDATION :=
  ⟨ANALYTICAL_WIENER_ELEMENTARY_FOUNDATION_NATIVE,
    ANALYTICAL_WIENER_CARRIER_CHECKPOINT_NATIVE⟩

/--
The remaining nonlinear/analytic block:

* weighted convolution and Leray-divergence estimates;
* the projected mild equation in `A₀`;
* fixed-path Duhamel contraction and weighted Picard invariant;
* coefficient/fixed-margin holomorphy;
* identification with the supplied trajectory;
* mixed factorial estimates.
-/
def ANALYTICAL_WIENER_NONLINEAR_FRONTIER : Prop :=
  ANALYTICAL_WIENER_CARRIER_FOUNDATION →
    ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT

theorem ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_wienerNonlinearFrontier
    (frontier : ANALYTICAL_WIENER_NONLINEAR_FRONTIER) :
    ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT :=
  frontier ANALYTICAL_WIENER_CARRIER_FOUNDATION_NATIVE

theorem ANALYTICAL_OBLIGATION_FRONTIER_of_wienerNonlinearFrontier
    (frontier : ANALYTICAL_WIENER_NONLINEAR_FRONTIER) :
    ANALYTICAL_OBLIGATION_FRONTIER :=
  ANALYTICAL_OBLIGATION_FRONTIER_of_quantitative
    (ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_wienerNonlinearFrontier frontier)

theorem NSE_GR_FINAL_B_EQUIVALENCE_of_wienerNonlinearFrontier
    (frontier : ANALYTICAL_WIENER_NONLINEAR_FRONTIER) :
    NSE_GR_FINAL_B_EQUIVALENCE :=
  NSE_GR_FINAL_B_EQUIVALENCE_of_quantitative
    (ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_wienerNonlinearFrontier frontier)

end
end NSEGR.Strengthening
