import GRAssembly.NativeReconstructionCore
import GRAssembly.BoundaryConstraints

/-! Gaussian boundary reconstruction and the canonical full-tensor identity. -/
set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

namespace NSEGR.Assembly
noncomputable section

theorem canonical_boundary_exact_completion {ν ρ t0 : ℝ}
    (g : CanonicalRepresentative ν ρ t0) :
    ∀ t ∈ timeInterval t0 g.timeRadius,
      boundaryK g.metric t = completedBoundary ν ρ (boundaryVelocity (boundaryK g.metric))
        (boundaryPressure ρ (boundaryK g.metric)) (boundaryPotential (boundaryK g.metric)) t := by
  intro t ht
  have hK := gaussianVacuum_boundaryAdmissible g.geometry
  exact boundary_slice_eq_completedBoundary_of_zero_stress ν ρ (boundaryK g.metric) t
    (hK.symmetric t ht) (boundaryAdmissible_solenoidal hK ht)
    (boundaryAdmissible_potential_laplacian hK ht)
    (boundaryAdmissible_raw_recovery hK ht) (g.stress_zero t ht)

theorem geometricReconstructionLaws_native (ν ρ t0 : ℝ) :
    GeometricReconstructionLaws ν ρ t0 where
  regularity := fun δ ε g hg => boundaryAdmissible_decoded_pair
    (gaussianVacuum_boundaryAdmissible hg)
  solenoidal := fun δ ε g hg t ht x => boundaryAdmissible_solenoidal
    (gaussianVacuum_boundaryAdmissible hg) ht x
  residual := fun δ ε g hg t ht x => boundaryAdmissible_residual
    (gaussianVacuum_boundaryAdmissible hg) ht x


end
end NSEGR.Assembly
