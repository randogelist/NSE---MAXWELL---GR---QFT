import ClassicalMechanics.MaterialBridge
import NSEMaxwell.CurlCurl

/-!
# Source-preserving assembly of 25 registered native endpoints

N01--N17 and NX01--NX08 refer to existing theorems in the frozen B-tier
source register. `export` provides names in `ClassicalMechanicsAssembly.Native`;
it preserves the canonical theorem and every premise. No theorem body is copied.

The `export` commands establish the alias provenance. The examples below
check that each reference elaborates with the original full implicit argument
telescope. Because Lean has proof irrelevance, these equality examples are
not independent certificates of proof-body identity. The external runner
separately audits the 25 canonical declarations listed in
`Auxillary/assembly-native-targets.txt`.

The exports are aliases, not 25 newly proved mathematical results. In
particular they do not construct the pending flow or diffusion realization.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly.Native

export NSEMaxwell.CurlCurl (
  coordinateDerivative_smooth
  coordinate_component_smooth
  fderiv_component_apply
  secondCoordinate_symm
  second_coordinate_component
  laplacian_coordinate
)

export ClassicalMechanics (
  cofactorGradient_eq_adjugate_transpose
  piola_identity
  tensorDivergence_adjugate_gradient
  cofactorGradient_eq_inverse_transpose_of_det_one
  tensorDivergence_inverse_transpose_of_det_one
  scalar_fderiv_coordinate_expansion
  gradient_comp_coordinate
  finite_velocity_slice_smooth
  materialPullbackIdentities_of_flow
  material_pressure_gradient_pullback_on
  coordinateMinor_derivative
  uniqueDiffOn_finiteSpacetime
  finite_spatial_restriction_fderiv
  finite_time_hasDerivWithinAt
  finite_time_restriction_fderiv
  finite_flow_acceleration
  material_inverse_transpose_divergence_zero
  material_path_surjective
  CLASSICAL_MECHANICS_MATERIAL_OF_FLOW_AND_DIFFUSION
)

end ClassicalMechanicsAssembly.Native

-- N01: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.coordinateDerivative_smooth
example : @ClassicalMechanicsAssembly.Native.coordinateDerivative_smooth =
    @NSEMaxwell.CurlCurl.coordinateDerivative_smooth := rfl

-- N02: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.coordinate_component_smooth
example : @ClassicalMechanicsAssembly.Native.coordinate_component_smooth =
    @NSEMaxwell.CurlCurl.coordinate_component_smooth := rfl

-- N03: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.fderiv_component_apply
example : @ClassicalMechanicsAssembly.Native.fderiv_component_apply =
    @NSEMaxwell.CurlCurl.fderiv_component_apply := rfl

-- N04: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.secondCoordinate_symm
example : @ClassicalMechanicsAssembly.Native.secondCoordinate_symm =
    @NSEMaxwell.CurlCurl.secondCoordinate_symm := rfl

-- N05: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.second_coordinate_component
example : @ClassicalMechanicsAssembly.Native.second_coordinate_component =
    @NSEMaxwell.CurlCurl.second_coordinate_component := rfl

-- N06: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.laplacian_coordinate
example : @ClassicalMechanicsAssembly.Native.laplacian_coordinate =
    @NSEMaxwell.CurlCurl.laplacian_coordinate := rfl

-- N07: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.cofactorGradient_eq_adjugate_transpose
example : @ClassicalMechanicsAssembly.Native.cofactorGradient_eq_adjugate_transpose =
    @ClassicalMechanics.cofactorGradient_eq_adjugate_transpose := rfl

-- N08: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.piola_identity
example : @ClassicalMechanicsAssembly.Native.piola_identity =
    @ClassicalMechanics.piola_identity := rfl

-- N09: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.tensorDivergence_adjugate_gradient
example : @ClassicalMechanicsAssembly.Native.tensorDivergence_adjugate_gradient =
    @ClassicalMechanics.tensorDivergence_adjugate_gradient := rfl

-- N10: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.cofactorGradient_eq_inverse_transpose_of_det_one
example : @ClassicalMechanicsAssembly.Native.cofactorGradient_eq_inverse_transpose_of_det_one =
    @ClassicalMechanics.cofactorGradient_eq_inverse_transpose_of_det_one := rfl

-- N11: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.tensorDivergence_inverse_transpose_of_det_one
example : @ClassicalMechanicsAssembly.Native.tensorDivergence_inverse_transpose_of_det_one =
    @ClassicalMechanics.tensorDivergence_inverse_transpose_of_det_one := rfl

-- N12: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.scalar_fderiv_coordinate_expansion
example : @ClassicalMechanicsAssembly.Native.scalar_fderiv_coordinate_expansion =
    @ClassicalMechanics.scalar_fderiv_coordinate_expansion := rfl

-- N13: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.gradient_comp_coordinate
example : @ClassicalMechanicsAssembly.Native.gradient_comp_coordinate =
    @ClassicalMechanics.gradient_comp_coordinate := rfl

-- N14: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.finite_velocity_slice_smooth
example : @ClassicalMechanicsAssembly.Native.finite_velocity_slice_smooth =
    @ClassicalMechanics.finite_velocity_slice_smooth := rfl

-- N15: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.materialPullbackIdentities_of_flow
example : @ClassicalMechanicsAssembly.Native.materialPullbackIdentities_of_flow =
    @ClassicalMechanics.materialPullbackIdentities_of_flow := rfl

-- N16: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.material_pressure_gradient_pullback_on
example : @ClassicalMechanicsAssembly.Native.material_pressure_gradient_pullback_on =
    @ClassicalMechanics.material_pressure_gradient_pullback_on := rfl

-- N17: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.coordinateMinor_derivative
example : @ClassicalMechanicsAssembly.Native.coordinateMinor_derivative =
    @ClassicalMechanics.coordinateMinor_derivative := rfl

-- NX01: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.uniqueDiffOn_finiteSpacetime
example : @ClassicalMechanicsAssembly.Native.uniqueDiffOn_finiteSpacetime =
    @ClassicalMechanics.uniqueDiffOn_finiteSpacetime := rfl

-- NX02: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.finite_spatial_restriction_fderiv
example : @ClassicalMechanicsAssembly.Native.finite_spatial_restriction_fderiv =
    @ClassicalMechanics.finite_spatial_restriction_fderiv := rfl

-- NX03: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.finite_time_hasDerivWithinAt
example : @ClassicalMechanicsAssembly.Native.finite_time_hasDerivWithinAt =
    @ClassicalMechanics.finite_time_hasDerivWithinAt := rfl

-- NX04: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.finite_time_restriction_fderiv
example : @ClassicalMechanicsAssembly.Native.finite_time_restriction_fderiv =
    @ClassicalMechanics.finite_time_restriction_fderiv := rfl

-- NX05: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.finite_flow_acceleration
example : @ClassicalMechanicsAssembly.Native.finite_flow_acceleration =
    @ClassicalMechanics.finite_flow_acceleration := rfl

-- NX06: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.material_inverse_transpose_divergence_zero
example : @ClassicalMechanicsAssembly.Native.material_inverse_transpose_divergence_zero =
    @ClassicalMechanics.material_inverse_transpose_divergence_zero := rfl

-- NX07: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.material_path_surjective
example : @ClassicalMechanicsAssembly.Native.material_path_surjective =
    @ClassicalMechanics.material_path_surjective := rfl

-- NX08: exported reference/type compatibility; original premises retained.
#check @ClassicalMechanicsAssembly.Native.CLASSICAL_MECHANICS_MATERIAL_OF_FLOW_AND_DIFFUSION
example : @ClassicalMechanicsAssembly.Native.CLASSICAL_MECHANICS_MATERIAL_OF_FLOW_AND_DIFFUSION =
    @ClassicalMechanics.CLASSICAL_MECHANICS_MATERIAL_OF_FLOW_AND_DIFFUSION := rfl
