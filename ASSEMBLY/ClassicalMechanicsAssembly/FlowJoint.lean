import ClassicalMechanicsAssembly.FlowJointJets
import ClassicalMechanicsAssembly.FlowJetIntegral

/-!
# Joint regularity of the constructed ODE flow

The concrete jet integral equations discharge the last input of the
closed-slab joint-regularity theorem.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical
open scoped Topology ContDiff Interval NNReal

noncomputable section

/-- Joint C-infinity regularity of the actual selected periodic ODE flow.
All Banach-path, jet-continuity, forcing and time-integral obligations are derived. -/
theorem constructed_flow_smooth {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, SpatialPeriodic (u t))
    {B K : ℝ≥0} (h : Flow.SlabODEData T u B K) :
    SmoothVelocityOn T (Flow.flow h hT.le) := by
  apply smoothVelocityOn_of_path_jet_integrals hT hu
    (selectedFlowPath_contDiff hT hu hp h)
  · intro t ht a
    rfl
  · intro r s hs a
    exact selectedFlow_labelJet_integral hT hu hp h r s hs a

end

end ClassicalMechanicsAssembly
