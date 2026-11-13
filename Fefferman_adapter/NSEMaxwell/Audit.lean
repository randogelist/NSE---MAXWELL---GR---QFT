import NSEMaxwell
import MethlibEndpoints
import FourierHodgeLaws_inhabitant

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

#print NSEMaxwell.Classical.Data
#print NSEMaxwell.Classical.MagneticData
#print NSEMaxwell.Classical.NSSolution
#print NSEMaxwell.Classical.MaxwellSolution
#print NSEMaxwell.Classical.FeffermanB
#print NSEMaxwell.Classical.MaxwellB
#print NSEMaxwell.Classical.ExactEquivalence
#print NSEMaxwell.Bridge.MagneticPath
#print NSEMaxwell.Bridge.CanonicalRegularity
#print NSEMaxwell.Bridge.PeriodicAnalyticLaws

#check @NSEMaxwell.Classical.velocity_slice_smooth
#print axioms NSEMaxwell.Classical.velocity_slice_smooth

#check @NSEMaxwell.Classical.pressure_slice_smooth
#print axioms NSEMaxwell.Classical.pressure_slice_smooth

#check @NSEMaxwell.Classical.timeDerivative_congr_field
#print axioms NSEMaxwell.Classical.timeDerivative_congr_field

#check @NSEMaxwell.Classical.scalarTimeDerivative_congr_field
#print axioms NSEMaxwell.Classical.scalarTimeDerivative_congr_field

#check @NSEMaxwell.Classical.vectorL_zero
#print axioms NSEMaxwell.Classical.vectorL_zero

#check @NSEMaxwell.Classical.scalarL_zero
#print axioms NSEMaxwell.Classical.scalarL_zero

#check @NSEMaxwell.Classical.K_zero
#print axioms NSEMaxwell.Classical.K_zero

#check @NSEMaxwell.Classical.DG_zero_direction
#print axioms NSEMaxwell.Classical.DG_zero_direction

#check @NSEMaxwell.Classical.NSSolution.slice_data
#print axioms NSEMaxwell.Classical.NSSolution.slice_data

#check @NSEMaxwell.Classical.MaxwellSolution.slice_magnetic_data
#print axioms NSEMaxwell.Classical.MaxwellSolution.slice_magnetic_data

#check @NSEMaxwell.Constitutive.cross_add_left
#print axioms NSEMaxwell.Constitutive.cross_add_left

#check @NSEMaxwell.Constitutive.cross_add_right
#print axioms NSEMaxwell.Constitutive.cross_add_right

#check @NSEMaxwell.Constitutive.DG_add_of_K_curl
#print axioms NSEMaxwell.Constitutive.DG_add_of_K_curl

#check @NSEMaxwell.Constitutive.DG_neg_of_K_curl
#print axioms NSEMaxwell.Constitutive.DG_neg_of_K_curl

#check @NSEMaxwell.Constitutive.ampere_factorization
#print axioms NSEMaxwell.Constitutive.ampere_factorization

#check @NSEMaxwell.Constitutive.ampere_zero_of_faraday
#print axioms NSEMaxwell.Constitutive.ampere_zero_of_faraday

#check @NSEMaxwell.Constitutive.canonical_faraday_of_maxwell
#print axioms NSEMaxwell.Constitutive.canonical_faraday_of_maxwell

#check @NSEMaxwell.Residual.hodge_momentum_factorization
#print axioms NSEMaxwell.Residual.hodge_momentum_factorization

#check @NSEMaxwell.Residual.momentum_factorization
#print axioms NSEMaxwell.Residual.momentum_factorization

#check @NSEMaxwell.Residual.reconstructed_zero_iff
#print axioms NSEMaxwell.Residual.reconstructed_zero_iff

#check @NSEMaxwell.Residual.factored_zero_iff
#print axioms NSEMaxwell.Residual.factored_zero_iff

#check @NSEMaxwell.Residual.momentum_pressure_change
#print axioms NSEMaxwell.Residual.momentum_pressure_change

#check @NSEMaxwell.Residual.gradient_split_zero_iff
#print axioms NSEMaxwell.Residual.gradient_split_zero_iff

#check @NSEMaxwell.Residual.ampere_factorization
#print axioms NSEMaxwell.Residual.ampere_factorization

#check @NSEMaxwell.Residual.full_maxwell_iff_faraday
#print axioms NSEMaxwell.Residual.full_maxwell_iff_faraday

#check @NSEMaxwell.Residual.momentum_zero_iff_full_maxwell
#print axioms NSEMaxwell.Residual.momentum_zero_iff_full_maxwell

#check @NSEMaxwell.ExistenceTransport.forall_iff_of_data_equiv
#print axioms NSEMaxwell.ExistenceTransport.forall_iff_of_data_equiv

#check @NSEMaxwell.ExistenceTransport.forall_exists_iff_of_data_equiv
#print axioms NSEMaxwell.ExistenceTransport.forall_exists_iff_of_data_equiv

#check @NSEMaxwell.ExistenceTransport.forall_nonempty_iff_of_solution_equiv
#print axioms NSEMaxwell.ExistenceTransport.forall_nonempty_iff_of_solution_equiv

#check @NSEMaxwell.Bridge.MagneticPath.slice
#print axioms NSEMaxwell.Bridge.MagneticPath.slice

#check @NSEMaxwell.Bridge.momentum_zero_of_ns
#print axioms NSEMaxwell.Bridge.momentum_zero_of_ns

#check @NSEMaxwell.Bridge.canonical_momentum_factorization
#print axioms NSEMaxwell.Bridge.canonical_momentum_factorization

#check @NSEMaxwell.Bridge.maxwell_of_faraday
#print axioms NSEMaxwell.Bridge.maxwell_of_faraday

#check @NSEMaxwell.Bridge.faraday_of_ns
#print axioms NSEMaxwell.Bridge.faraday_of_ns

#check @NSEMaxwell.Bridge.maxwell_of_ns
#print axioms NSEMaxwell.Bridge.maxwell_of_ns

#check @NSEMaxwell.Bridge.ns_of_maxwell
#print axioms NSEMaxwell.Bridge.ns_of_maxwell

#check @NSEMaxwell.Bridge.feffermanB_iff_maxwellB_of_periodicAnalyticLaws
#print axioms NSEMaxwell.Bridge.feffermanB_iff_maxwellB_of_periodicAnalyticLaws

#check @NSEMaxwell.Bridge.exact_equivalence_of_periodicAnalyticLaws
#print axioms NSEMaxwell.Bridge.exact_equivalence_of_periodicAnalyticLaws

#check @NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE
#print axioms NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE

#check @NSEMaxwell.Classical.coordinateDerivative_neg
#print axioms NSEMaxwell.Classical.coordinateDerivative_neg

#check @NSEMaxwell.Classical.spatialCurl_neg
#print axioms NSEMaxwell.Classical.spatialCurl_neg

#check @NSEMaxwell.Classical.vectorL_neg
#print axioms NSEMaxwell.Classical.vectorL_neg

#check @NSEMaxwell.Classical.scalarL_neg
#print axioms NSEMaxwell.Classical.scalarL_neg

#check @NSEMaxwell.Classical.K_neg
#print axioms NSEMaxwell.Classical.K_neg

#check @NSEMaxwell.Classical.DG_neg
#print axioms NSEMaxwell.Classical.DG_neg

#check @NSEMaxwell.Classical.DG_curl_neg
#print axioms NSEMaxwell.Classical.DG_curl_neg

#check @NSEMaxwell.Lamb.vector_coordinate_decomposition
#print axioms NSEMaxwell.Lamb.vector_coordinate_decomposition

#check @NSEMaxwell.Lamb.convection_coordinate
#print axioms NSEMaxwell.Lamb.convection_coordinate

#check @NSEMaxwell.Lamb.kinetic_gradient_coordinate
#print axioms NSEMaxwell.Lamb.kinetic_gradient_coordinate

#check @NSEMaxwell.Lamb.lamb_identity_at
#print axioms NSEMaxwell.Lamb.lamb_identity_at

#check @NSEMaxwell.Lamb.lamb_identity
#print axioms NSEMaxwell.Lamb.lamb_identity

#check @NSEMaxwell.Lamb.lamb_identity_of_data
#print axioms NSEMaxwell.Lamb.lamb_identity_of_data

#check @NSEMaxwell.Lamb.reconstructed_lamb_identity
#print axioms NSEMaxwell.Lamb.reconstructed_lamb_identity

#check @NSEMaxwell.Classical.gradient_pressure_decomposition
#print axioms NSEMaxwell.Classical.gradient_pressure_decomposition

#check @NSEMaxwell.Classical.canonicalPressure_gradient
#print axioms NSEMaxwell.Classical.canonicalPressure_gradient

#check @NSEMaxwell.Classical.smooth_constant_velocity
#print axioms NSEMaxwell.Classical.smooth_constant_velocity

#check @NSEMaxwell.Classical.smooth_constant_pressure
#print axioms NSEMaxwell.Classical.smooth_constant_pressure

#check @NSEMaxwell.Classical.periodic_constant_velocity
#print axioms NSEMaxwell.Classical.periodic_constant_velocity

#check @NSEMaxwell.Classical.periodic_constant_pressure
#print axioms NSEMaxwell.Classical.periodic_constant_pressure

#check @NSEMaxwell.Constitutive.timeDerivative_eq_evolution_of_faraday
#print axioms NSEMaxwell.Constitutive.timeDerivative_eq_evolution_of_faraday

#check @NSEMaxwell.Constitutive.ampere_zero_of_faraday_chain
#print axioms NSEMaxwell.Constitutive.ampere_zero_of_faraday_chain

#check @NSEMaxwell.Bridge.MagneticPath.constant
#print axioms NSEMaxwell.Bridge.MagneticPath.constant

#check @NSEMaxwell.Bridge.PeriodicAnalyticLaws.curl_data
#print axioms NSEMaxwell.Bridge.PeriodicAnalyticLaws.curl_data

#check @NSEMaxwell.Bridge.PeriodicAnalyticLaws.reconstruction_data
#print axioms NSEMaxwell.Bridge.PeriodicAnalyticLaws.reconstruction_data

#check @NSEMaxwell.Bridge.PeriodicAnalyticLaws.reconstruct_mean
#print axioms NSEMaxwell.Bridge.PeriodicAnalyticLaws.reconstruct_mean

#check @NSEMaxwell.Bridge.canonical_momentum_split
#print axioms NSEMaxwell.Bridge.canonical_momentum_split

#check @NSEMaxwell.Bridge.canonical_momentum_zero_of_faraday
#print axioms NSEMaxwell.Bridge.canonical_momentum_zero_of_faraday

#check @NSEMaxwell.CurlCurl.coordinateDerivative_smooth
#print axioms NSEMaxwell.CurlCurl.coordinateDerivative_smooth

#check @NSEMaxwell.CurlCurl.spatialCurl_smooth
#print axioms NSEMaxwell.CurlCurl.spatialCurl_smooth

#check @NSEMaxwell.CurlCurl.secondCoordinate_symm
#print axioms NSEMaxwell.CurlCurl.secondCoordinate_symm

#check @NSEMaxwell.CurlCurl.curl_curl
#print axioms NSEMaxwell.CurlCurl.curl_curl

#check @NSEMaxwell.CurlCurl.divergence_curl
#print axioms NSEMaxwell.CurlCurl.divergence_curl

#check @NSEMaxwell.CurlCurl.viscosity_identity_of_data
#print axioms NSEMaxwell.CurlCurl.viscosity_identity_of_data

#check @NSEMaxwell.CurlCurl.reconstructed_viscosity_identity
#print axioms NSEMaxwell.CurlCurl.reconstructed_viscosity_identity

#check @NSEMaxwell.PeriodicIntegration.fderiv_periodic
#print axioms NSEMaxwell.PeriodicIntegration.fderiv_periodic

#check @NSEMaxwell.PeriodicIntegration.coordinateDerivative_periodic
#print axioms NSEMaxwell.PeriodicIntegration.coordinateDerivative_periodic

#check @NSEMaxwell.PeriodicIntegration.spatialCurl_periodic
#print axioms NSEMaxwell.PeriodicIntegration.spatialCurl_periodic

#check @NSEMaxwell.PeriodicIntegration.divergence_periodic
#print axioms NSEMaxwell.PeriodicIntegration.divergence_periodic

#check @NSEMaxwell.PeriodicIntegration.gradient_periodic
#print axioms NSEMaxwell.PeriodicIntegration.gradient_periodic

#check @NSEMaxwell.PeriodicIntegration.laplacian_periodic
#print axioms NSEMaxwell.PeriodicIntegration.laplacian_periodic

#check @NSEMaxwell.PeriodicIntegration.integrableOn_unitCube_of_continuous
#print axioms NSEMaxwell.PeriodicIntegration.integrableOn_unitCube_of_continuous

#check @NSEMaxwell.PeriodicIntegration.spatialMean_coordinateDerivative_zero
#print axioms NSEMaxwell.PeriodicIntegration.spatialMean_coordinateDerivative_zero

#check @NSEMaxwell.PeriodicIntegration.spatialMean_apply
#print axioms NSEMaxwell.PeriodicIntegration.spatialMean_apply

#check @NSEMaxwell.PeriodicIntegration.integral_coordinate_component_zero
#print axioms NSEMaxwell.PeriodicIntegration.integral_coordinate_component_zero

#check @NSEMaxwell.PeriodicIntegration.spatialMean_curl_zero
#print axioms NSEMaxwell.PeriodicIntegration.spatialMean_curl_zero

#check @NSEMaxwell.Spacetime.forwardSpacetime_eq_prod
#print axioms NSEMaxwell.Spacetime.forwardSpacetime_eq_prod

#check @NSEMaxwell.Spacetime.uniqueDiffOn_forwardSpacetime
#print axioms NSEMaxwell.Spacetime.uniqueDiffOn_forwardSpacetime

#check @NSEMaxwell.Spacetime.closure_interior_forwardSpacetime
#print axioms NSEMaxwell.Spacetime.closure_interior_forwardSpacetime

#check @NSEMaxwell.Spacetime.spatial_restriction_fderiv
#print axioms NSEMaxwell.Spacetime.spatial_restriction_fderiv

#check @NSEMaxwell.Spacetime.time_restriction_hasDerivWithinAt
#print axioms NSEMaxwell.Spacetime.time_restriction_hasDerivWithinAt

#check @NSEMaxwell.Spacetime.time_restriction_derivWithin
#print axioms NSEMaxwell.Spacetime.time_restriction_derivWithin

#check @NSEMaxwell.Spacetime.directional_smooth
#print axioms NSEMaxwell.Spacetime.directional_smooth

#check @NSEMaxwell.Spacetime.directional_fderivWithin_apply
#print axioms NSEMaxwell.Spacetime.directional_fderivWithin_apply

#check @NSEMaxwell.Spacetime.time_slice_hasDerivWithinAt
#print axioms NSEMaxwell.Spacetime.time_slice_hasDerivWithinAt

#check @NSEMaxwell.Spacetime.coordinateDerivative_eq_joint
#print axioms NSEMaxwell.Spacetime.coordinateDerivative_eq_joint

#check @NSEMaxwell.Spacetime.coordinateDerivative_trajectory_smooth
#print axioms NSEMaxwell.Spacetime.coordinateDerivative_trajectory_smooth

#check @NSEMaxwell.Spacetime.timeDerivative_smooth
#print axioms NSEMaxwell.Spacetime.timeDerivative_smooth

#check @NSEMaxwell.Spacetime.curl_trajectory_smooth
#print axioms NSEMaxwell.Spacetime.curl_trajectory_smooth

#check @NSEMaxwell.Spacetime.timeDerivative_coordinateDerivative
#print axioms NSEMaxwell.Spacetime.timeDerivative_coordinateDerivative

#check @NSEMaxwell.Spacetime.time_component_hasDerivWithinAt
#print axioms NSEMaxwell.Spacetime.time_component_hasDerivWithinAt

#check @NSEMaxwell.Spacetime.timeDerivative_component
#print axioms NSEMaxwell.Spacetime.timeDerivative_component

#check @NSEMaxwell.Spacetime.timeDerivative_curl_commute
#print axioms NSEMaxwell.Spacetime.timeDerivative_curl_commute

#check @NSEMaxwell.FourierPeriodic.cosineKernel_add_unit_left
#print axioms NSEMaxwell.FourierPeriodic.cosineKernel_add_unit_left

#check @NSEMaxwell.FourierPeriodic.cosineKernel_symm
#print axioms NSEMaxwell.FourierPeriodic.cosineKernel_symm

#check @NSEMaxwell.FourierPeriodic.cosineKernel_add_unit_right
#print axioms NSEMaxwell.FourierPeriodic.cosineKernel_add_unit_right

#check @NSEMaxwell.FourierPeriodic.vectorL_periodic
#print axioms NSEMaxwell.FourierPeriodic.vectorL_periodic

#check @NSEMaxwell.FourierPeriodic.scalarL_periodic
#print axioms NSEMaxwell.FourierPeriodic.scalarL_periodic

#check @NSEMaxwell.FourierPeriodic.K_periodic
#print axioms NSEMaxwell.FourierPeriodic.K_periodic

#check @NSEMaxwell.FourierPeriodic.U_periodic
#print axioms NSEMaxwell.FourierPeriodic.U_periodic

#check @NSEMaxwell.FourierPeriodic.G_periodic
#print axioms NSEMaxwell.FourierPeriodic.G_periodic

#check @NSEMaxwell.FourierPeriodic.V_periodic
#print axioms NSEMaxwell.FourierPeriodic.V_periodic

#check @NSEMaxwell.FourierPeriodic.Q_periodic
#print axioms NSEMaxwell.FourierPeriodic.Q_periodic

#check @NSEMaxwell.FourierPeriodic.DG_periodic
#print axioms NSEMaxwell.FourierPeriodic.DG_periodic

#check @NSEMaxwell.FourierPeriodic.current_periodic
#print axioms NSEMaxwell.FourierPeriodic.current_periodic

#check @NSEMaxwell.FourierPeriodic.canonicalPressure_periodic
#print axioms NSEMaxwell.FourierPeriodic.canonicalPressure_periodic

#check @NSEMaxwell.FourierPeriodic.canonicalVelocity_periodic
#print axioms NSEMaxwell.FourierPeriodic.canonicalVelocity_periodic

#check @NSEMaxwell.FourierPeriodic.canonicalElectric_periodic
#print axioms NSEMaxwell.FourierPeriodic.canonicalElectric_periodic

#check @NSEMaxwell.FourierPeriodic.canonicalCharge_periodic
#print axioms NSEMaxwell.FourierPeriodic.canonicalCharge_periodic

#check @NSEMaxwell.FourierPeriodic.canonicalCurrent_periodic
#print axioms NSEMaxwell.FourierPeriodic.canonicalCurrent_periodic

#check @NSEMaxwell.FourierPeriodic.canonicalPressureTrajectory_periodic
#print axioms NSEMaxwell.FourierPeriodic.canonicalPressureTrajectory_periodic

#print NSEMaxwell.Bridge.CanonicalSmoothness

#print NSEMaxwell.Bridge.FourierHodgeLaws

#check @NSEMaxwell.PeriodicIntegration.isCompact_unitCube
#print axioms NSEMaxwell.PeriodicIntegration.isCompact_unitCube

#check @NSEMaxwell.PeriodicIntegration.integral_fderiv_unitVector_zero
#print axioms NSEMaxwell.PeriodicIntegration.integral_fderiv_unitVector_zero

#check @NSEMaxwell.PeriodicIntegration.gradient_smooth
#print axioms NSEMaxwell.PeriodicIntegration.gradient_smooth

#check @NSEMaxwell.PeriodicIntegration.spatialMean_gradient_zero
#print axioms NSEMaxwell.PeriodicIntegration.spatialMean_gradient_zero

#check @NSEMaxwell.PeriodicIntegration.laplacian_smooth
#print axioms NSEMaxwell.PeriodicIntegration.laplacian_smooth

#check @NSEMaxwell.PeriodicIntegration.spatialMean_laplacian_zero
#print axioms NSEMaxwell.PeriodicIntegration.spatialMean_laplacian_zero

#check @NSEMaxwell.PeriodicIntegration.momentumFlux_smooth
#print axioms NSEMaxwell.PeriodicIntegration.momentumFlux_smooth

#check @NSEMaxwell.PeriodicIntegration.momentumFlux_periodic
#print axioms NSEMaxwell.PeriodicIntegration.momentumFlux_periodic

#check @NSEMaxwell.PeriodicIntegration.coordinateDerivative_momentumFlux
#print axioms NSEMaxwell.PeriodicIntegration.coordinateDerivative_momentumFlux

#check @NSEMaxwell.PeriodicIntegration.momentumFlux_divergence
#print axioms NSEMaxwell.PeriodicIntegration.momentumFlux_divergence

#check @NSEMaxwell.PeriodicIntegration.convection_smooth
#print axioms NSEMaxwell.PeriodicIntegration.convection_smooth

#check @NSEMaxwell.PeriodicIntegration.spatialMean_convection_zero
#print axioms NSEMaxwell.PeriodicIntegration.spatialMean_convection_zero

#check @NSEMaxwell.Spacetime.timeDerivative_periodic
#print axioms NSEMaxwell.Spacetime.timeDerivative_periodic

#check @NSEMaxwell.Spacetime.timeDerivative_divergence_zero
#print axioms NSEMaxwell.Spacetime.timeDerivative_divergence_zero

#check @NSEMaxwell.DominatedWithin.hasDerivWithinAt_integral_of_dominated
#print axioms NSEMaxwell.DominatedWithin.hasDerivWithinAt_integral_of_dominated

#check @NSEMaxwell.LocalEvolution.cross_smooth
#print axioms NSEMaxwell.LocalEvolution.cross_smooth

#check @NSEMaxwell.LocalEvolution.cross_trajectory_smooth
#print axioms NSEMaxwell.LocalEvolution.cross_trajectory_smooth

#check @NSEMaxwell.LocalEvolution.timeDerivative_cross
#print axioms NSEMaxwell.LocalEvolution.timeDerivative_cross

#check @NSEMaxwell.LocalEvolution.electric_time_chain_of_reconstruction
#print axioms NSEMaxwell.LocalEvolution.electric_time_chain_of_reconstruction

#check @NSEMaxwell.LocalEvolution.gradient_smooth
#print axioms NSEMaxwell.LocalEvolution.gradient_smooth

#check @NSEMaxwell.LocalEvolution.spatialCurl_add
#print axioms NSEMaxwell.LocalEvolution.spatialCurl_add

#check @NSEMaxwell.LocalEvolution.spatialCurl_gradient
#print axioms NSEMaxwell.LocalEvolution.spatialCurl_gradient

#check @NSEMaxwell.LocalEvolution.vorticity_residual
#print axioms NSEMaxwell.LocalEvolution.vorticity_residual

#check @NSEMaxwell.TemporalMean.local_uniform_time_bound
#print axioms NSEMaxwell.TemporalMean.local_uniform_time_bound

#check @NSEMaxwell.TemporalMean.mean_time_hasDerivWithinAt
#print axioms NSEMaxwell.TemporalMean.mean_time_hasDerivWithinAt

#check @NSEMaxwell.TemporalMean.mean_time_derivWithin
#print axioms NSEMaxwell.TemporalMean.mean_time_derivWithin

#check @NSEMaxwell.TemporalMean.timeDerivative_mean_zero_of_constant_mean
#print axioms NSEMaxwell.TemporalMean.timeDerivative_mean_zero_of_constant_mean

#check @NSEMaxwell.PeriodicIntegration.spatialMean_timeDerivative_zero_of_constant_mean
#print axioms NSEMaxwell.PeriodicIntegration.spatialMean_timeDerivative_zero_of_constant_mean

#check @NSEMaxwell.PeriodicIntegration.spatialMean_timeDerivative_zero_of_equation
#print axioms NSEMaxwell.PeriodicIntegration.spatialMean_timeDerivative_zero_of_equation

#check @NSEMaxwell.PeriodicIntegration.mean_conservation_of_equation
#print axioms NSEMaxwell.PeriodicIntegration.mean_conservation_of_equation

#check @NSEMaxwell.Bridge.vorticity_regularity_proved
#print axioms NSEMaxwell.Bridge.vorticity_regularity_proved

#check @NSEMaxwell.Bridge.FourierHodgeLaws.canonical_regularity
#print axioms NSEMaxwell.Bridge.FourierHodgeLaws.canonical_regularity

#check @NSEMaxwell.Bridge.FourierHodgeLaws.reconstruction_data
#print axioms NSEMaxwell.Bridge.FourierHodgeLaws.reconstruction_data

#check @NSEMaxwell.Bridge.FourierHodgeLaws.reconstruct_mean
#print axioms NSEMaxwell.Bridge.FourierHodgeLaws.reconstruct_mean

#check @NSEMaxwell.Bridge.FourierHodgeLaws.reconstruction_time
#print axioms NSEMaxwell.Bridge.FourierHodgeLaws.reconstruction_time

#check @NSEMaxwell.Bridge.mean_conservation_proved
#print axioms NSEMaxwell.Bridge.mean_conservation_proved

#check @NSEMaxwell.Bridge.FourierHodgeLaws.toPeriodicAnalyticLaws
#print axioms NSEMaxwell.Bridge.FourierHodgeLaws.toPeriodicAnalyticLaws

#check @NSEMaxwell.Bridge.exact_equivalence_of_fourierHodgeLaws
#print axioms NSEMaxwell.Bridge.exact_equivalence_of_fourierHodgeLaws

#check @NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED
#print axioms NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_REDUCED

#check @NSEMaxwell.CanonicalSmoothness.divergence_trajectory_smooth
#print axioms NSEMaxwell.CanonicalSmoothness.divergence_trajectory_smooth

#check @NSEMaxwell.CanonicalSmoothness.canonical_electric_smooth
#print axioms NSEMaxwell.CanonicalSmoothness.canonical_electric_smooth

#check @NSEMaxwell.CanonicalSmoothness.canonical_charge_smooth
#print axioms NSEMaxwell.CanonicalSmoothness.canonical_charge_smooth

#check @NSEMaxwell.CanonicalSmoothness.magnetic_curl_path
#print axioms NSEMaxwell.CanonicalSmoothness.magnetic_curl_path

#check @NSEMaxwell.CanonicalSmoothness.magnetic_neg_path
#print axioms NSEMaxwell.CanonicalSmoothness.magnetic_neg_path

#check @NSEMaxwell.CanonicalSmoothness.evolution_magnetic_path
#print axioms NSEMaxwell.CanonicalSmoothness.evolution_magnetic_path

#check @NSEMaxwell.CanonicalSmoothness.canonical_current_smooth_of_velocity_smoothing
#print axioms NSEMaxwell.CanonicalSmoothness.canonical_current_smooth_of_velocity_smoothing

-- Pinned upstream endpoints registered for the remaining Fourier/Hodge bridge.
#check @UnitAddTorus.mFourierCoeff_eq_integral
#print axioms UnitAddTorus.mFourierCoeff_eq_integral

#check @UnitAddTorus.hasSum_mFourier_series_apply_of_summable
#print axioms UnitAddTorus.hasSum_mFourier_series_apply_of_summable

#check @contDiff_tsum
#print axioms contDiff_tsum

#check @ZLattice.summable_norm_pow_inv
#print axioms ZLattice.summable_norm_pow_inv

-- Directional endpoints, with all original analytic premises retained.

#check @NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_periodicAnalyticLaws
#print axioms NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_periodicAnalyticLaws

#check @NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_periodicAnalyticLaws
#print axioms NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_periodicAnalyticLaws

#check @NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_fourierHodgeLaws
#print axioms NSEMaxwell.Bridge.feffermanB_implies_maxwellB_of_fourierHodgeLaws

#check @NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_fourierHodgeLaws
#print axioms NSEMaxwell.Bridge.maxwellB_implies_feffermanB_of_fourierHodgeLaws

-- Independently native Maxwell endpoint: exact concrete declarations and proofs.

#check @NSEMaxwell.Classical.Vec
#print axioms NSEMaxwell.Classical.Vec

#check @NSEMaxwell.Classical.Field
#print axioms NSEMaxwell.Classical.Field

#check @NSEMaxwell.Classical.Velocity
#print axioms NSEMaxwell.Classical.Velocity

#check @NSEMaxwell.Classical.Pressure
#print axioms NSEMaxwell.Classical.Pressure

#check @NSEMaxwell.Classical.unitCube
#print axioms NSEMaxwell.Classical.unitCube

#check @NSEMaxwell.Classical.SpatialPeriodic
#print axioms NSEMaxwell.Classical.SpatialPeriodic

#check @NSEMaxwell.Classical.spatialMean
#print axioms NSEMaxwell.Classical.spatialMean

#check @NSEMaxwell.Classical.coordinateDerivative
#print axioms NSEMaxwell.Classical.coordinateDerivative

#check @NSEMaxwell.Classical.divergence
#print axioms NSEMaxwell.Classical.divergence

#check @NSEMaxwell.Classical.spatialCurl
#print axioms NSEMaxwell.Classical.spatialCurl

#check @NSEMaxwell.Classical.timeDerivative
#print axioms NSEMaxwell.Classical.timeDerivative

#check @NSEMaxwell.Classical.SmoothVelocity
#print axioms NSEMaxwell.Classical.SmoothVelocity

#check @NSEMaxwell.Classical.SmoothPressure
#print axioms NSEMaxwell.Classical.SmoothPressure

#check @NSEMaxwell.Classical.Data
#print axioms NSEMaxwell.Classical.Data

#check @NSEMaxwell.Classical.MagneticData
#print axioms NSEMaxwell.Classical.MagneticData

#check @NSEMaxwell.Classical.inverseLaplacianSymbol
#print axioms NSEMaxwell.Classical.inverseLaplacianSymbol

#check @NSEMaxwell.Classical.cosineKernel
#print axioms NSEMaxwell.Classical.cosineKernel

#check @NSEMaxwell.Classical.vectorL
#print axioms NSEMaxwell.Classical.vectorL

#check @NSEMaxwell.Classical.scalarL
#print axioms NSEMaxwell.Classical.scalarL

#check @NSEMaxwell.Classical.K
#print axioms NSEMaxwell.Classical.K

#check @NSEMaxwell.Classical.U
#print axioms NSEMaxwell.Classical.U

#check @NSEMaxwell.Classical.G
#print axioms NSEMaxwell.Classical.G

#check @NSEMaxwell.Classical.V
#print axioms NSEMaxwell.Classical.V

#check @NSEMaxwell.Classical.Q
#print axioms NSEMaxwell.Classical.Q

#check @NSEMaxwell.Classical.DG
#print axioms NSEMaxwell.Classical.DG

#check @NSEMaxwell.Classical.current
#print axioms NSEMaxwell.Classical.current

#check @NSEMaxwell.Classical.MaxwellSolution
#print axioms NSEMaxwell.Classical.MaxwellSolution

#check @NSEMaxwell.Classical.MaxwellB
#print axioms NSEMaxwell.Classical.MaxwellB

#check @MaxwellEndpoint.MaxwellEquations
#print axioms MaxwellEndpoint.MaxwellEquations

#check @MaxwellEndpoint.equations_of_solution
#print axioms MaxwellEndpoint.equations_of_solution

#check @MaxwellEndpoint.constitutive_fields_of_solution
#print axioms MaxwellEndpoint.constitutive_fields_of_solution

#check @MaxwellEndpoint.magnetic_evolution_of_solution
#print axioms MaxwellEndpoint.magnetic_evolution_of_solution

#check @MaxwellEndpoint.electric_evolution_of_solution
#print axioms MaxwellEndpoint.electric_evolution_of_solution

#check @MaxwellEndpoint.maxwellB_iff_native
#print axioms MaxwellEndpoint.maxwellB_iff_native

#check @MaxwellEndpoint.coordinateDerivative_zero
#print axioms MaxwellEndpoint.coordinateDerivative_zero

#check @MaxwellEndpoint.divergence_zero
#print axioms MaxwellEndpoint.divergence_zero

#check @MaxwellEndpoint.spatialCurl_zero
#print axioms MaxwellEndpoint.spatialCurl_zero

#check @MaxwellEndpoint.cross_zero_left
#print axioms MaxwellEndpoint.cross_zero_left

#check @MaxwellEndpoint.cross_zero_right
#print axioms MaxwellEndpoint.cross_zero_right

#check @MaxwellEndpoint.vectorL_zero
#print axioms MaxwellEndpoint.vectorL_zero

#check @MaxwellEndpoint.scalarL_zero
#print axioms MaxwellEndpoint.scalarL_zero

#check @MaxwellEndpoint.K_zero
#print axioms MaxwellEndpoint.K_zero

#check @MaxwellEndpoint.U_zero
#print axioms MaxwellEndpoint.U_zero

#check @MaxwellEndpoint.G_zero
#print axioms MaxwellEndpoint.G_zero

#check @MaxwellEndpoint.V_zero
#print axioms MaxwellEndpoint.V_zero

#check @MaxwellEndpoint.Q_zero
#print axioms MaxwellEndpoint.Q_zero

#check @MaxwellEndpoint.DG_zero
#print axioms MaxwellEndpoint.DG_zero

#check @MaxwellEndpoint.current_zero
#print axioms MaxwellEndpoint.current_zero

#check @MaxwellEndpoint.timeDerivative_zero
#print axioms MaxwellEndpoint.timeDerivative_zero

#check @MaxwellEndpoint.magneticData_zero
#print axioms MaxwellEndpoint.magneticData_zero

#check @MaxwellEndpoint.zero_solution
#print axioms MaxwellEndpoint.zero_solution

#check @MaxwellEndpoint.zero_datum_global_instance
#print axioms MaxwellEndpoint.zero_datum_global_instance

-- Selected native Methlib endpoints; semantic hypotheses remain explicit.

#check @SingularClosure.torusDatumComponent_fourierCoeff
#print axioms SingularClosure.torusDatumComponent_fourierCoeff

#check @SingularClosure.datumFourierCoeff_coordinateDerivative
#print axioms SingularClosure.datumFourierCoeff_coordinateDerivative

#check @SingularClosure.FOURIER_POLYNOMIAL_DECAY
#print axioms SingularClosure.FOURIER_POLYNOMIAL_DECAY

#check @SingularClosure.scalarFourierSeries_contDiff
#print axioms SingularClosure.scalarFourierSeries_contDiff

#check @SingularClosure.scalarFourierSeries_coefficient
#print axioms SingularClosure.scalarFourierSeries_coefficient

#check @SingularClosure.datumFourierCoeff_injective_continuous_periodic
#print axioms SingularClosure.datumFourierCoeff_injective_continuous_periodic

#check @SingularClosure.infiniteTransportPressure_recovery
#print axioms SingularClosure.infiniteTransportPressure_recovery

#check @SingularClosure.datumFourierCoeff_smoothFourierSynthesis
#print axioms SingularClosure.datumFourierCoeff_smoothFourierSynthesis

#check @SingularClosure.smoothFourierSynthesis_coordinateDerivative
#print axioms SingularClosure.smoothFourierSynthesis_coordinateDerivative

#check @SingularClosure.summable_torusSobolevWeight_inv_four
#print axioms SingularClosure.summable_torusSobolevWeight_inv_four

-- Concrete Fourier-Hodge declarations and exact premise-free equivalence.

#check @NSEMaxwell.HodgeProof.spatialMean_contDiffOn_nat
#print axioms NSEMaxwell.HodgeProof.spatialMean_contDiffOn_nat

#check @NSEMaxwell.HodgeProof.spatialMean_contDiffOn
#print axioms NSEMaxwell.HodgeProof.spatialMean_contDiffOn

#check @NSEMaxwell.HodgeProof.spatialMean_scalar_embed
#print axioms NSEMaxwell.HodgeProof.spatialMean_scalar_embed

#check @NSEMaxwell.HodgeProof.scalarMean_contDiffOn
#print axioms NSEMaxwell.HodgeProof.scalarMean_contDiffOn

#check @NSEMaxwell.HodgeProof.spatialMean_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.spatialMean_trajectory_smooth

#check @NSEMaxwell.HodgeProof.scalarMean_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.scalarMean_trajectory_smooth

#check @NSEMaxwell.HodgeProof.kineticMean_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.kineticMean_trajectory_smooth

#check @NSEMaxwell.HodgeProof.canonicalVelocity_smooth_of_vectorL_smooth
#print axioms NSEMaxwell.HodgeProof.canonicalVelocity_smooth_of_vectorL_smooth

#check @NSEMaxwell.HodgeProof.canonicalVelocity_divergence_free_of_vectorL_smooth
#print axioms NSEMaxwell.HodgeProof.canonicalVelocity_divergence_free_of_vectorL_smooth

#check @NSEMaxwell.HodgeProof.canonicalPressure_smooth_of_scalarL_smooth
#print axioms NSEMaxwell.HodgeProof.canonicalPressure_smooth_of_scalarL_smooth

#check @NSEMaxwell.HodgeProof.canonical_smoothness_of_parameter_smoothing
#print axioms NSEMaxwell.HodgeProof.canonical_smoothness_of_parameter_smoothing

#check @NSEMaxwell.HodgeProof.H3_of_parameter_smoothing
#print axioms NSEMaxwell.HodgeProof.H3_of_parameter_smoothing

#check @NSEMaxwell.HodgeProof.native_unitVector
#print axioms NSEMaxwell.HodgeProof.native_unitVector

#check @NSEMaxwell.HodgeProof.native_unitCube
#print axioms NSEMaxwell.HodgeProof.native_unitCube

#check @NSEMaxwell.HodgeProof.native_spatialPeriodic_iff
#print axioms NSEMaxwell.HodgeProof.native_spatialPeriodic_iff

#check @NSEMaxwell.HodgeProof.native_spatialMean
#print axioms NSEMaxwell.HodgeProof.native_spatialMean

#check @NSEMaxwell.HodgeProof.native_coordinateDerivative
#print axioms NSEMaxwell.HodgeProof.native_coordinateDerivative

#check @NSEMaxwell.HodgeProof.native_divergence
#print axioms NSEMaxwell.HodgeProof.native_divergence

#check @NSEMaxwell.HodgeProof.native_gradient
#print axioms NSEMaxwell.HodgeProof.native_gradient

#check @NSEMaxwell.HodgeProof.native_laplacian
#print axioms NSEMaxwell.HodgeProof.native_laplacian

#check @NSEMaxwell.HodgeProof.scalarLift_component
#print axioms NSEMaxwell.HodgeProof.scalarLift_component

#check @NSEMaxwell.HodgeProof.scalarLift_contDiff
#print axioms NSEMaxwell.HodgeProof.scalarLift_contDiff

#check @NSEMaxwell.HodgeProof.scalarLift_periodic
#print axioms NSEMaxwell.HodgeProof.scalarLift_periodic

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_scalarLift
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_scalarLift

#check @NSEMaxwell.HodgeProof.inverseLaplacianSymbol_zero
#print axioms NSEMaxwell.HodgeProof.inverseLaplacianSymbol_zero

#check @NSEMaxwell.HodgeProof.inverseLaplacianSymbol_neg
#print axioms NSEMaxwell.HodgeProof.inverseLaplacianSymbol_neg

#check @NSEMaxwell.HodgeProof.inverseLaplacianSymbol_nonneg
#print axioms NSEMaxwell.HodgeProof.inverseLaplacianSymbol_nonneg

#check @NSEMaxwell.HodgeProof.inverseLaplacianSymbol_le_one
#print axioms NSEMaxwell.HodgeProof.inverseLaplacianSymbol_le_one

#check @NSEMaxwell.HodgeProof.inverseLaplacianSymbol_complex_norm_le_one
#print axioms NSEMaxwell.HodgeProof.inverseLaplacianSymbol_complex_norm_le_one

#check @NSEMaxwell.HodgeProof.inverseVectorCoeff_zero
#print axioms NSEMaxwell.HodgeProof.inverseVectorCoeff_zero

#check @NSEMaxwell.HodgeProof.inverseScalarCoeff_zero
#print axioms NSEMaxwell.HodgeProof.inverseScalarCoeff_zero

#check @NSEMaxwell.HodgeProof.scalarCoeff_neg
#print axioms NSEMaxwell.HodgeProof.scalarCoeff_neg

#check @NSEMaxwell.HodgeProof.inverseVectorCoeff_reality
#print axioms NSEMaxwell.HodgeProof.inverseVectorCoeff_reality

#check @NSEMaxwell.HodgeProof.inverseScalarCoeff_neg
#print axioms NSEMaxwell.HodgeProof.inverseScalarCoeff_neg

#check @NSEMaxwell.HodgeProof.scalarLift_coordinateDerivative
#print axioms NSEMaxwell.HodgeProof.scalarLift_coordinateDerivative

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_coordinateDerivative
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_coordinateDerivative

#check @NSEMaxwell.HodgeProof.scalarCoeff_coordinateDerivative
#print axioms NSEMaxwell.HodgeProof.scalarCoeff_coordinateDerivative

#check @NSEMaxwell.HodgeProof.rapid_datumFourierCoeff
#print axioms NSEMaxwell.HodgeProof.rapid_datumFourierCoeff

#check @NSEMaxwell.HodgeProof.rapid_scalarCoeff
#print axioms NSEMaxwell.HodgeProof.rapid_scalarCoeff

#check @NSEMaxwell.HodgeProof.rapid_mul_bounded
#print axioms NSEMaxwell.HodgeProof.rapid_mul_bounded

#check @NSEMaxwell.HodgeProof.rapid_inverseLaplacianCoeff
#print axioms NSEMaxwell.HodgeProof.rapid_inverseLaplacianCoeff

#check @NSEMaxwell.HodgeProof.rapid_inverseScalarCoeff
#print axioms NSEMaxwell.HodgeProof.rapid_inverseScalarCoeff

#check @NSEMaxwell.HodgeProof.inverseVectorCoeff_weighted_summable
#print axioms NSEMaxwell.HodgeProof.inverseVectorCoeff_weighted_summable

#check @NSEMaxwell.HodgeProof.inverseScalarCoeff_weighted_summable
#print axioms NSEMaxwell.HodgeProof.inverseScalarCoeff_weighted_summable

#check @NSEMaxwell.HodgeProof.fourierCharacter_mul_star
#print axioms NSEMaxwell.HodgeProof.fourierCharacter_mul_star

#check @NSEMaxwell.HodgeProof.cosineKernel_eq_character_re
#print axioms NSEMaxwell.HodgeProof.cosineKernel_eq_character_re

#check @NSEMaxwell.HodgeProof.scalar_cosine_integral
#print axioms NSEMaxwell.HodgeProof.scalar_cosine_integral

#check @NSEMaxwell.HodgeProof.scalar_cosine_summand
#print axioms NSEMaxwell.HodgeProof.scalar_cosine_summand

#check @NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries
#print axioms NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries

#check @NSEMaxwell.HodgeProof.vector_cosine_integral_component
#print axioms NSEMaxwell.HodgeProof.vector_cosine_integral_component

#check @NSEMaxwell.HodgeProof.vector_cosine_summand_component
#print axioms NSEMaxwell.HodgeProof.vector_cosine_summand_component

#check @NSEMaxwell.HodgeProof.vectorL_summable
#print axioms NSEMaxwell.HodgeProof.vectorL_summable

#check @NSEMaxwell.HodgeProof.vectorL_eq_smoothFourierSynthesis
#print axioms NSEMaxwell.HodgeProof.vectorL_eq_smoothFourierSynthesis

#check @NSEMaxwell.HodgeProof.vectorL_smooth
#print axioms NSEMaxwell.HodgeProof.vectorL_smooth

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_vectorL
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_vectorL

#check @NSEMaxwell.HodgeProof.scalarL_smooth
#print axioms NSEMaxwell.HodgeProof.scalarL_smooth

#check @NSEMaxwell.HodgeProof.vectorL_component
#print axioms NSEMaxwell.HodgeProof.vectorL_component

#check @NSEMaxwell.HodgeProof.scalarL_zero
#print axioms NSEMaxwell.HodgeProof.scalarL_zero

#check @NSEMaxwell.HodgeProof.vectorL_zero
#print axioms NSEMaxwell.HodgeProof.vectorL_zero

#check @NSEMaxwell.HodgeProof.vectorL_trajectory_smooth_of_scalar_parameter_smoothing
#print axioms NSEMaxwell.HodgeProof.vectorL_trajectory_smooth_of_scalar_parameter_smoothing

#check @NSEMaxwell.HodgeProof.canonical_smoothness_of_scalar_parameter_smoothing
#print axioms NSEMaxwell.HodgeProof.canonical_smoothness_of_scalar_parameter_smoothing

#check @NSEMaxwell.HodgeProof.H3_of_scalar_parameter_smoothing
#print axioms NSEMaxwell.HodgeProof.H3_of_scalar_parameter_smoothing

#check @NSEMaxwell.HodgeProof.hasFDerivWithinAt_closure_of_continuous_jets
#print axioms NSEMaxwell.HodgeProof.hasFDerivWithinAt_closure_of_continuous_jets

#check @NSEMaxwell.HodgeProof.contDiffOn_nat_of_compatible_jets
#print axioms NSEMaxwell.HodgeProof.contDiffOn_nat_of_compatible_jets

#check @NSEMaxwell.HodgeProof.contDiffOn_infty_of_compatible_jets
#print axioms NSEMaxwell.HodgeProof.contDiffOn_infty_of_compatible_jets

#check @NSEMaxwell.HodgeProof.contDiffOn_closure_of_continuous_jets
#print axioms NSEMaxwell.HodgeProof.contDiffOn_closure_of_continuous_jets

#check @NSEMaxwell.HodgeProof.isOpen_positiveSpacetime
#print axioms NSEMaxwell.HodgeProof.isOpen_positiveSpacetime

#check @NSEMaxwell.HodgeProof.convex_positiveSpacetime
#print axioms NSEMaxwell.HodgeProof.convex_positiveSpacetime

#check @NSEMaxwell.HodgeProof.closure_positiveSpacetime
#print axioms NSEMaxwell.HodgeProof.closure_positiveSpacetime

#check @NSEMaxwell.HodgeProof.contDiffOn_forwardSpacetime_of_continuous_jets
#print axioms NSEMaxwell.HodgeProof.contDiffOn_forwardSpacetime_of_continuous_jets

#check @NSEMaxwell.HodgeProof.cubeSlice_contDiff
#print axioms NSEMaxwell.HodgeProof.cubeSlice_contDiff

#check @NSEMaxwell.HodgeProof.cubeTimeDerivative_smooth
#print axioms NSEMaxwell.HodgeProof.cubeTimeDerivative_smooth

#check @NSEMaxwell.HodgeProof.cubeTime_hasDerivWithinAt
#print axioms NSEMaxwell.HodgeProof.cubeTime_hasDerivWithinAt

#check @NSEMaxwell.HodgeProof.cubeIntegral_local_uniform_time_bound
#print axioms NSEMaxwell.HodgeProof.cubeIntegral_local_uniform_time_bound

#check @NSEMaxwell.HodgeProof.cubeIntegral_hasDerivWithinAt
#print axioms NSEMaxwell.HodgeProof.cubeIntegral_hasDerivWithinAt

#check @NSEMaxwell.HodgeProof.cubeIntegral_derivWithin
#print axioms NSEMaxwell.HodgeProof.cubeIntegral_derivWithin

#check @NSEMaxwell.HodgeProof.cubeIntegral_contDiffOn_nat
#print axioms NSEMaxwell.HodgeProof.cubeIntegral_contDiffOn_nat

#check @NSEMaxwell.HodgeProof.cubeIntegral_contDiffOn
#print axioms NSEMaxwell.HodgeProof.cubeIntegral_contDiffOn

#check @NSEMaxwell.HodgeProof.scalarTimeDerivative_smooth
#print axioms NSEMaxwell.HodgeProof.scalarTimeDerivative_smooth

#check @NSEMaxwell.HodgeProof.scalarTimeDerivative_periodic
#print axioms NSEMaxwell.HodgeProof.scalarTimeDerivative_periodic

#check @NSEMaxwell.HodgeProof.scalarSpatialDerivative_smooth
#print axioms NSEMaxwell.HodgeProof.scalarSpatialDerivative_smooth

#check @NSEMaxwell.HodgeProof.scalarSpatialDerivative_periodic
#print axioms NSEMaxwell.HodgeProof.scalarSpatialDerivative_periodic

#check @NSEMaxwell.HodgeProof.scalarCoeff_integrand_smooth
#print axioms NSEMaxwell.HodgeProof.scalarCoeff_integrand_smooth

#check @NSEMaxwell.HodgeProof.scalarCoeff_contDiffOn
#print axioms NSEMaxwell.HodgeProof.scalarCoeff_contDiffOn

#check @NSEMaxwell.HodgeProof.scalarCoeff_hasDerivWithinAt
#print axioms NSEMaxwell.HodgeProof.scalarCoeff_hasDerivWithinAt

#check @NSEMaxwell.HodgeProof.scalarCoeff_derivWithin
#print axioms NSEMaxwell.HodgeProof.scalarCoeff_derivWithin

#check @NSEMaxwell.HodgeProof.scalarCoeff_hasDerivAt_pos
#print axioms NSEMaxwell.HodgeProof.scalarCoeff_hasDerivAt_pos

#check @NSEMaxwell.HodgeProof.scalarCoeff_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.scalarCoeff_trajectory_smooth

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_contDiffOn
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_contDiffOn

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_hasDerivWithinAt
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_hasDerivWithinAt

#check @NSEMaxwell.HodgeProof.compact_velocity_norm_bound
#print axioms NSEMaxwell.HodgeProof.compact_velocity_norm_bound

#check @NSEMaxwell.HodgeProof.compact_componentL1_bound
#print axioms NSEMaxwell.HodgeProof.compact_componentL1_bound

#check @NSEMaxwell.HodgeProof.iteratedCoordinateDerivative_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.iteratedCoordinateDerivative_trajectory_smooth

#check @NSEMaxwell.HodgeProof.uniform_fourierDecayConstant
#print axioms NSEMaxwell.HodgeProof.uniform_fourierDecayConstant

#check @NSEMaxwell.HodgeProof.uniform_datumFourierCoeff_moment_bound
#print axioms NSEMaxwell.HodgeProof.uniform_datumFourierCoeff_moment_bound

#check @NSEMaxwell.HodgeProof.scalarLift_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.scalarLift_trajectory_smooth

#check @NSEMaxwell.HodgeProof.scalarLift_trajectory_periodic
#print axioms NSEMaxwell.HodgeProof.scalarLift_trajectory_periodic

#check @NSEMaxwell.HodgeProof.uniform_scalarCoeff_moment_bound
#print axioms NSEMaxwell.HodgeProof.uniform_scalarCoeff_moment_bound

#check @NSEMaxwell.HodgeProof.uniform_inverseScalarCoeff_moment_bound
#print axioms NSEMaxwell.HodgeProof.uniform_inverseScalarCoeff_moment_bound

#check @NSEMaxwell.HodgeProof.inverseScalarCoeff_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.inverseScalarCoeff_trajectory_smooth

#check @NSEMaxwell.HodgeProof.inverseScalarSeriesTerm_continuousOn
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeriesTerm_continuousOn

#check @NSEMaxwell.HodgeProof.inverseScalarSeries_continuousOn
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeries_continuousOn

#check @NSEMaxwell.HodgeProof.inverseScalarSeriesTerm_hasFDerivAt
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeriesTerm_hasFDerivAt

#check @NSEMaxwell.HodgeProof.inverseScalarSeriesTermDerivative_bound
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeriesTermDerivative_bound

#check @NSEMaxwell.HodgeProof.phaseProjection_eq_sum
#print axioms NSEMaxwell.HodgeProof.phaseProjection_eq_sum

#check @NSEMaxwell.HodgeProof.inverseScalarSeriesTermDerivative_eq_partials
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeriesTermDerivative_eq_partials

#check @NSEMaxwell.HodgeProof.inverseScalarSeriesTerm_summable
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeriesTerm_summable

#check @NSEMaxwell.HodgeProof.inverseScalarSeriesTermDerivative_summable
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeriesTermDerivative_summable

#check @NSEMaxwell.HodgeProof.tsum_inverseScalarSeriesTermDerivative
#print axioms NSEMaxwell.HodgeProof.tsum_inverseScalarSeriesTermDerivative

#check @NSEMaxwell.HodgeProof.inverseScalarSeriesDerivative_continuousOn
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeriesDerivative_continuousOn

#check @NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivAt_pos
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivAt_pos

#check @NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivWithinAt
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivWithinAt

#check @NSEMaxwell.HodgeProof.inverseScalarSeries_contDiffOn_nat
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeries_contDiffOn_nat

#check @NSEMaxwell.HodgeProof.inverseScalarSeries_contDiffOn
#print axioms NSEMaxwell.HodgeProof.inverseScalarSeries_contDiffOn

#check @NSEMaxwell.HodgeProof.scalarL_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.scalarL_trajectory_smooth

#check @NSEMaxwell.HodgeProof.vectorL_trajectory_smooth
#print axioms NSEMaxwell.HodgeProof.vectorL_trajectory_smooth

#check @NSEMaxwell.HodgeProof.canonical_smoothness
#print axioms NSEMaxwell.HodgeProof.canonical_smoothness

#check @NSEMaxwell.HodgeProof.h3_canonical_smoothness
#print axioms NSEMaxwell.HodgeProof.h3_canonical_smoothness

#check @NSEMaxwell.HodgeProof.coordinateDerivative_const_add
#print axioms NSEMaxwell.HodgeProof.coordinateDerivative_const_add

#check @NSEMaxwell.HodgeProof.divergence_const_add
#print axioms NSEMaxwell.HodgeProof.divergence_const_add

#check @NSEMaxwell.HodgeProof.spatialCurl_const_add
#print axioms NSEMaxwell.HodgeProof.spatialCurl_const_add

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_smooth
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_smooth

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.U_smooth
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.U_smooth

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.divergence_K
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.divergence_K

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.spatialMean_K
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.spatialMean_K

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.curl_K
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.curl_K

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_curl
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_curl

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.reconstruct_velocity
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.reconstruct_velocity

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.reconstruct_curl
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.reconstruct_curl

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.reconstruction_data
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.reconstruction_data

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.reconstruct_mean
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.reconstruct_mean

#check @NSEMaxwell.HodgeProof.spatialMean_lamb_zero
#print axioms NSEMaxwell.HodgeProof.spatialMean_lamb_zero

#check @NSEMaxwell.HodgeProof.G_smooth_of_velocity_smooth
#print axioms NSEMaxwell.HodgeProof.G_smooth_of_velocity_smooth

#check @NSEMaxwell.HodgeProof.spatialMean_G_of_reconstruction
#print axioms NSEMaxwell.HodgeProof.spatialMean_G_of_reconstruction

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.G_smooth
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.G_smooth

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.spatialMean_G
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.spatialMean_G

#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.electric_hodge
#print axioms NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.electric_hodge

#check @NSEMaxwell.HodgeProof.scalarL_summable
#print axioms NSEMaxwell.HodgeProof.scalarL_summable

#check @NSEMaxwell.HodgeProof.cosine_mul_integrable
#print axioms NSEMaxwell.HodgeProof.cosine_mul_integrable

#check @NSEMaxwell.HodgeProof.scalarL_add
#print axioms NSEMaxwell.HodgeProof.scalarL_add

#check @NSEMaxwell.HodgeProof.scalarL_sub
#print axioms NSEMaxwell.HodgeProof.scalarL_sub

#check @NSEMaxwell.HodgeProof.scalarL_finset_sum
#print axioms NSEMaxwell.HodgeProof.scalarL_finset_sum

#check @NSEMaxwell.HodgeProof.coordinateDerivative_vectorL_commute
#print axioms NSEMaxwell.HodgeProof.coordinateDerivative_vectorL_commute

#check @NSEMaxwell.HodgeProof.coordinate_component_periodic
#print axioms NSEMaxwell.HodgeProof.coordinate_component_periodic

#check @NSEMaxwell.HodgeProof.scalarL_coordinateComponent
#print axioms NSEMaxwell.HodgeProof.scalarL_coordinateComponent

#check @NSEMaxwell.HodgeProof.divergence_vectorL_commute
#print axioms NSEMaxwell.HodgeProof.divergence_vectorL_commute

#check @NSEMaxwell.HodgeProof.curl_vectorL_commute
#print axioms NSEMaxwell.HodgeProof.curl_vectorL_commute

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_add
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_add

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_sub
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_sub

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_neg
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_neg

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_const
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_const

#check @NSEMaxwell.HodgeProof.datumFourierCoeff_laplacian
#print axioms NSEMaxwell.HodgeProof.datumFourierCoeff_laplacian

#check @NSEMaxwell.HodgeProof.laplacianFrequency_mul_inverseLaplacianSymbol
#print axioms NSEMaxwell.HodgeProof.laplacianFrequency_mul_inverseLaplacianSymbol

#check @NSEMaxwell.HodgeProof.neg_laplacian_vectorL
#print axioms NSEMaxwell.HodgeProof.neg_laplacian_vectorL

#check @NSEMaxwell.HodgeProof.spatialInverseLaplacianLaws
#print axioms NSEMaxwell.HodgeProof.spatialInverseLaplacianLaws

#check @NSEMaxwell.HodgeProof.h1_reconstruct_velocity
#print axioms NSEMaxwell.HodgeProof.h1_reconstruct_velocity

#check @NSEMaxwell.HodgeProof.h2_reconstruct_curl
#print axioms NSEMaxwell.HodgeProof.h2_reconstruct_curl

#check @NSEMaxwell.HodgeProof.h4_electric_hodge
#print axioms NSEMaxwell.HodgeProof.h4_electric_hodge

#check @NSEMaxwell.HodgeProof.fourierHodgeLaws_of_parameter_smoothing
#print axioms NSEMaxwell.HodgeProof.fourierHodgeLaws_of_parameter_smoothing

#check @NSEMaxwell.HodgeProof.exact_equivalence_of_parameter_smoothing
#print axioms NSEMaxwell.HodgeProof.exact_equivalence_of_parameter_smoothing

#check @NSEMaxwell.HodgeProof.fourierHodgeLaws_inhabitant
#print axioms NSEMaxwell.HodgeProof.fourierHodgeLaws_inhabitant

#check @NSEMaxwell.HodgeProof.exact_equivalence_native
#print axioms NSEMaxwell.HodgeProof.exact_equivalence_native

#check @NSEMaxwell.HodgeProof.contDiffOn_tsum_closure_of_compatible_jets
#print axioms NSEMaxwell.HodgeProof.contDiffOn_tsum_closure_of_compatible_jets

#check @NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL
#print axioms NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE_UNCONDITIONAL
