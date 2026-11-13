import GRAssembly.NativeGaussianEvolution
import GRAssembly.NativeCKFiniteDimensional

/-! Exact analytic CK existence in the native Gaussian state coordinates. -/
set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false
namespace NSEGR.NativeLiterature
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
noncomputable section

theorem gaussianEvolutionState_exists_unique (input : LiteratureAnalyticCKInput)
    (K : BoundaryTensor) (t0 : ℝ) (x0 : Vec)
    (hK : AnalyticAt ℝ (fun y : GaussianBase => K y.1 y.2) (t0, x0)) :
    ∃ U : ℝ × GaussianBase → GaussianState,
      GaussianEvolutionStateSolution K t0 x0 U ∧
        ∀ V : ℝ × GaussianBase → GaussianState,
          GaussianEvolutionStateSolution K t0 x0 V → U =ᶠ[𝓝 (0, (t0, x0))] V := by
  apply ckLocal_exists_unique_of_literatureCK input gaussianCKRHS
    (gaussianInitialState K) 0 (t0, x0) (gaussianInitialState_analyticAt hK)
  apply gaussianCKRHS_analyticAt
  exact gaussianEta_isUnit

end
end NSEGR.NativeLiterature
