import QuantumAdapter.Obligations.GalerkinResidualConvergence

/-! P6: an actual native smooth solution gives all finite-horizon Galerkin H3 bounds. -/
set_option autoImplicit false
set_option Elab.async true
namespace QuantumAdapter.Obligations
noncomputable section
open QuantumAdapter.Assembly NSEMaxwell.Classical

/-- P6 with exactly the native solution premise, including pressure, initial trace, and arbitrary mean. -/
theorem phaseFlow_smooth_stability {ν : ℝ} (hν : 0 < ν) (F : PhaseFlow ν)
    (a : Field) (ha : Data a) (u : Velocity) (p : Pressure)
    (h : NSSolution ν a u p) (T : ℝ) (hT : 0 < T) :
    GalerkinBoundAt F a ha T := by
  obtain ⟨δ, hδ, hres⟩ := h.referenceResidual_vanishes_uniformly T
  exact galerkinBoundAt_of_reference_residual_bound hν F h ha T hT δ hδ hres

end
end QuantumAdapter.Obligations
