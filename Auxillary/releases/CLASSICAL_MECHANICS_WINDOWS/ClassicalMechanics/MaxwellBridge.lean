import ClassicalMechanics.Equivalence
import NSEMaxwell.AnalyticReduction

/-!
Sequential composition with the existing constrained Maxwell endpoint.
The Newtonian/NSE adapter has no analytic-law premise. The Maxwell composition
retains the exact existing `FourierHodgeLaws` premise in every theorem type.
-/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical NSEMaxwell.Bridge

noncomputable section

theorem newtonianB_implies_maxwellB_of_fourierHodgeLaws
    (laws : FourierHodgeLaws) (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (h : NewtonianB ν) : MaxwellB ν c := by
  exact (exact_equivalence_of_fourierHodgeLaws laws ν hν c hc).mp
    (newtonianB_implies_feffermanB ν h)

theorem maxwellB_implies_newtonianB_of_fourierHodgeLaws
    (laws : FourierHodgeLaws) (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (h : MaxwellB ν c) : NewtonianB ν := by
  exact feffermanB_implies_newtonianB ν
    ((exact_equivalence_of_fourierHodgeLaws laws ν hν c hc).mpr h)

theorem newtonianB_iff_maxwellB_of_fourierHodgeLaws
    (laws : FourierHodgeLaws) (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) :
    NewtonianB ν ↔ MaxwellB ν c :=
  ⟨newtonianB_implies_maxwellB_of_fourierHodgeLaws laws ν c hν hc,
    maxwellB_implies_newtonianB_of_fourierHodgeLaws laws ν c hν hc⟩

end

end ClassicalMechanics
