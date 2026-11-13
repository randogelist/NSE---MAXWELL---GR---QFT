import NSEMaxwellForward
import NSEMaxwellReverse

/-!
# Compatibility assembly of the two concrete implications

Declaration namespaces and the original equivalence statements are preserved.
The analytic-law premise remains explicit.
-/

set_option autoImplicit false

namespace NSEMaxwell.Bridge

open NSEMaxwell.Classical NSEMaxwell.Constitutive
open scoped ContDiff

noncomputable section

/-- Conditional equivalence assembled from the two independent direction modules. -/
theorem feffermanB_iff_maxwellB_of_periodicAnalyticLaws
    (laws : PeriodicAnalyticLaws) (ν c : ℝ) :
    FeffermanB ν ↔ MaxwellB ν c :=
  ⟨feffermanB_implies_maxwellB_of_periodicAnalyticLaws laws ν c,
    maxwellB_implies_feffermanB_of_periodicAnalyticLaws laws ν c⟩

/-- Exact quantifier prefix; the analytic-law premise remains explicit. -/
theorem exact_equivalence_of_periodicAnalyticLaws
    (laws : PeriodicAnalyticLaws) : ExactEquivalence := by
  intro ν hν c hc
  exact feffermanB_iff_maxwellB_of_periodicAnalyticLaws laws ν c

end

end NSEMaxwell.Bridge
