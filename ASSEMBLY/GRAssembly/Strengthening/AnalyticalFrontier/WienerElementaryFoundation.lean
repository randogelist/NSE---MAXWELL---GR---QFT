import GRAssembly.Strengthening.AnalyticalFrontier.WienerScalarWeights

/-!
The fully native elementary foundation and the remaining functional Wiener
frontier.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

def ANALYTICAL_WIENER_ELEMENTARY_FOUNDATION : Prop :=
  ANALYTICAL_WIENER_NUMERICAL_FOUNDATION ∧
  ANALYTICAL_WIENER_SCALAR_WEIGHT_CHECKPOINT

theorem ANALYTICAL_WIENER_ELEMENTARY_FOUNDATION_NATIVE :
    ANALYTICAL_WIENER_ELEMENTARY_FOUNDATION :=
  ⟨ANALYTICAL_WIENER_NUMERICAL_FOUNDATION_NATIVE,
    ANALYTICAL_WIENER_SCALAR_WEIGHT_CHECKPOINT_NATIVE⟩

/--
The remaining functional block after all scalar and numerical estimates:

* fixed weighted Fourier-Wiener carriers and convolution;
* projected mild equation and Duhamel contraction;
* weighted Picard invariant;
* coefficient/fixed-margin holomorphy;
* real mild-solution identification;
* mixed factorial estimate.
-/
def ANALYTICAL_WIENER_REFINED_FUNCTIONAL_FRONTIER : Prop :=
  ANALYTICAL_WIENER_ELEMENTARY_FOUNDATION →
    ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT

theorem ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_refinedWienerFrontier
    (frontier : ANALYTICAL_WIENER_REFINED_FUNCTIONAL_FRONTIER) :
    ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT :=
  frontier ANALYTICAL_WIENER_ELEMENTARY_FOUNDATION_NATIVE

theorem ANALYTICAL_OBLIGATION_FRONTIER_of_refinedWienerFrontier
    (frontier : ANALYTICAL_WIENER_REFINED_FUNCTIONAL_FRONTIER) :
    ANALYTICAL_OBLIGATION_FRONTIER :=
  ANALYTICAL_OBLIGATION_FRONTIER_of_quantitative
    (ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_refinedWienerFrontier frontier)

theorem NSE_GR_FINAL_B_EQUIVALENCE_of_refinedWienerFrontier
    (frontier : ANALYTICAL_WIENER_REFINED_FUNCTIONAL_FRONTIER) :
    NSE_GR_FINAL_B_EQUIVALENCE :=
  NSE_GR_FINAL_B_EQUIVALENCE_of_quantitative
    (ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_refinedWienerFrontier frontier)

end
end NSEGR.Strengthening
