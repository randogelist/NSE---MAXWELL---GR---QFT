import GRAssembly.ScalarJet

/-!
GC05--GC06 assembled native endpoint, with the local GC10 Hamiltonian output.
Scope: one normalized analytic scalar germ at the specified spatial point.
The conclusion does not assert a common periodic cylinder or an inhabitant of
ScalarBoundaryCompletionLaws. LI01 is the only literature input used here.
-/

set_option autoImplicit false
set_option Elab.async true

open Filter
open scoped Topology

namespace NSEGR.Assembly
noncomputable section

/-- The concrete scalar CK chain, normalized uniqueness, and Hamiltonian
constraint assembled into one local witness. -/
theorem scalar_local_assembly
    (input : LiteratureAnalyticCKInput)
    {ν ρ t0 δ : ℝ} {u : Velocity} {p : Pressure}
    (hρ : ρ ≠ 0) (hpair : AnalyticPeriodicPair t0 δ u p) (x0 : Vec) :
    ∃ ψ : Pressure,
      ScalarNormalGerm ν ρ u p t0 x0 ψ ∧
      (∀ᶠ z in 𝓝 (t0, x0), ρ + scalarLaplacian (ψ z.1) z.2 ≠ 0) ∧
      (∀ᶠ z in 𝓝 (t0, x0),
        boundaryHamiltonian (completedBoundary ν ρ u p ψ) z.1 z.2 = 0) ∧
      ∀ φ : Pressure, ScalarNormalGerm ν ρ u p t0 x0 φ →
        (fun z : ℝ × Vec => ψ z.1 z.2) =ᶠ[𝓝 (t0, x0)]
          (fun z : ℝ × Vec => φ z.1 z.2) := by
  obtain ⟨ψ, hψ⟩ := scalarNormalGerm_exists input hρ hpair x0
  have hbase : (t0, x0) ∈ spacetimeSlab t0 δ := by
    constructor <;> linarith [hpair.radius_pos]
  refine ⟨ψ, hψ, hψ.noncharacteristic hρ, hψ.hamiltonian hρ, ?_⟩
  intro φ hφ
  exact scalar_normalized_germ_unique input hρ
    (hpair.velocity_analytic (t0, x0) hbase)
    (hpair.pressure_analytic (t0, x0) hbase) hψ hφ

end
end NSEGR.Assembly
