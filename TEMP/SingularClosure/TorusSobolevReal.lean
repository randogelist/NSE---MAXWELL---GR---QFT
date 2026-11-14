import SingularClosure.TorusSobolev

/-!
Generic real-scalar instances from Methlib 4813604a46179c745b82f51bee51a186e9f4cc2d,
SingularClosure/SobolevTrajectoryCalculus.lean. Exact instance bodies retained;
Galerkin-specific trajectory imports are not needed for these instances.
-/

set_option autoImplicit false

namespace SingularClosure
noncomputable section

instance torusSobolevNormedSpaceReal (s : ℕ) : NormedSpace ℝ (TorusSobolev s) :=
  NormedSpace.restrictScalars ℝ ℂ (TorusSobolev s)

instance torusSobolevRealScalarTower (s : ℕ) : IsScalarTower ℝ ℂ (TorusSobolev s) :=
  Real.isScalarTower

end
end SingularClosure
