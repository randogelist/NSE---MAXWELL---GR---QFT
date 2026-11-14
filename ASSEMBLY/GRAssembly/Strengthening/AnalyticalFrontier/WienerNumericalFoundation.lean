import GRAssembly.Strengthening.AnalyticalFrontier.ContractionBudget

/-!
Resolved numerical/sector foundation and the remaining functional Wiener
frontier. The latter contains precisely the Fourier-Wiener construction that
must produce the quantitative local factorial estimate.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

/-- The elementary sector, heat-exponent, and contraction-budget package. -/
def ANALYTICAL_WIENER_NUMERICAL_FOUNDATION : Prop :=
  ANALYTICAL_FIXED_SECTOR_GEOMETRY_CHECKPOINT ∧
  ANALYTICAL_SCALAR_HEAT_CHECKPOINT ∧
  ANALYTICAL_CONTRACTION_BUDGET_CHECKPOINT

/-- All elementary numerical components are supplied natively. -/
theorem ANALYTICAL_WIENER_NUMERICAL_FOUNDATION_NATIVE :
    ANALYTICAL_WIENER_NUMERICAL_FOUNDATION :=
  ⟨ANALYTICAL_FIXED_SECTOR_GEOMETRY_CHECKPOINT_NATIVE,
    ANALYTICAL_SCALAR_HEAT_CHECKPOINT_NATIVE,
    ANALYTICAL_CONTRACTION_BUDGET_CHECKPOINT_NATIVE⟩

/--
The remaining functional-analytic frontier:

* weighted periodic Wiener carriers and convolution;
* projected Duhamel map in the fixed `A₀` path space;
* contraction fixed point and weighted Picard invariant;
* coefficient and fixed-margin Banach holomorphy;
* real mild-solution identification;
* mixed Cauchy/Gevrey factorial bounds.
-/
def ANALYTICAL_WIENER_FUNCTIONAL_FRONTIER : Prop :=
  ANALYTICAL_WIENER_NUMERICAL_FOUNDATION →
    ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT

theorem ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_wienerFunctionalFrontier
    (frontier : ANALYTICAL_WIENER_FUNCTIONAL_FRONTIER) :
    ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT :=
  frontier ANALYTICAL_WIENER_NUMERICAL_FOUNDATION_NATIVE

theorem ANALYTICAL_OBLIGATION_FRONTIER_of_wienerFunctionalFrontier
    (frontier : ANALYTICAL_WIENER_FUNCTIONAL_FRONTIER) :
    ANALYTICAL_OBLIGATION_FRONTIER :=
  ANALYTICAL_OBLIGATION_FRONTIER_of_quantitative
    (ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_wienerFunctionalFrontier frontier)

theorem NSE_GR_FINAL_B_EQUIVALENCE_of_wienerFunctionalFrontier
    (frontier : ANALYTICAL_WIENER_FUNCTIONAL_FRONTIER) :
    NSE_GR_FINAL_B_EQUIVALENCE :=
  NSE_GR_FINAL_B_EQUIVALENCE_of_quantitative
    (ANALYTICAL_QUANTITATIVE_FACTORIAL_CHECKPOINT_of_wienerFunctionalFrontier frontier)

end
end NSEGR.Strengthening
