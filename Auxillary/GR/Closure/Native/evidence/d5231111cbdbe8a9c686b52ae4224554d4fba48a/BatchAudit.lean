import GRAdapter
import NSEGRForward
import NSEGRReverse
import TempEndpoints
import GRAssembly.CertifiedBase
import GRAssembly.AnalyticHodgeCalculus
import GRAssembly.AnalyticHodgeSeries
import GRAssembly.AnalyticHodgeInput
import GRAssembly.AnalyticHodgeTaylor
import GRAssembly.HodgeBounds
import GRAssembly.HodgeCommutation
import GRAssembly.AnalyticHodge
import GRAssembly.BoundaryConstraintsJets
import GRAssembly.BoundaryConstraintsGeometry
import GRAssembly.BoundaryConstraints
import GRAssembly.NativeCalculus
import GRAssembly.NativeCompletionCalculus
import GRAssembly.NativeGluingAtlas
import GRAssembly.NativeGluingTranslation
import GRAssembly.NativeGluingScalar
import GRAssembly.NativeConservation
import GRAssembly.NativeReconstructionCore
import GRAssembly.NativeCompletion
import GRAssembly.NativeGluingGaussianCoordinates
import GRAssembly.NativeGluingGaussian
import GRAssembly.NativeInverse
import GRAssembly.NativeReconstruction
import GRAssembly.NativeInverseCanonical
import GRAssembly.RootClosure
import GRAssembly.NSE_GR_THREE_OBLIGATION_CLOSURE
import GRAssembly.NativeCKSeries
import GRAssembly.NativeCKLift
import GRAssembly.NativeCKPrimitive
import GRAssembly.NativeCKFixedPoint
import GRAssembly.NativeCKBilinear
import GRAssembly.NativeCKComposition
import GRAssembly.NativeCKMultilinear
import GRAssembly.NativeCKNormalization
import GRAssembly.NativeCKScaledMap
import GRAssembly.NativeCKAnalyticMap
import GRAssembly.NativeCKGerm
import GRAssembly.NativeCKSemantics
import GRAssembly.NativeCK
import GRAssembly.NativeFourierCalculus
import GRAssembly.NativeFourierDecay
import GRAssembly.NativeFourierTorus
import GRAssembly.NativeFourier
import GRAssembly.NativeCKFiniteDimensional
import GRAssembly.NativeGaussianBianchi
import GRAssembly.NativeGaussianMetricCurvature
import GRAssembly.NativeGaussianContraction
import GRAssembly.NativeGaussianConstraintsPropagation
import GRAssembly.NativeGaussianEvolution
import GRAssembly.NativeGaussianConstraintInitial
import GRAssembly.NativeGaussianEvolutionCompatibility
import GRAssembly.NativeGaussianConstraintZero
import GRAssembly.NativeGaussianEvolutionJet
import GRAssembly.NativeGaussianEvolutionCompatibilityJet
import GRAssembly.NativeGaussianEvolutionExistence
import GRAssembly.NativeGaussianEvolutionRicci
import GRAssembly.NativeGaussianEvolutionRecovery
import GRAssembly.NativeGaussianEvolutionAssembly
import GRAssembly.NativeGaussianJet
import GRAssembly.NativeGaussianInput
import GRAssembly.NSE_GR_NATIVE_LITERATURE_CLOSURE
set_option pp.universes false
#check @NSEGR.identity3_diag
#print axioms NSEGR.identity3_diag
#check @NSEGR.trace3_eq_matrix_trace
#print axioms NSEGR.trace3_eq_matrix_trace
#check @NSEGR.trace3_zero
#print axioms NSEGR.trace3_zero
#check @NSEGR.trace3_add
#print axioms NSEGR.trace3_add
#check @NSEGR.trace3_sub
#print axioms NSEGR.trace3_sub
#check @NSEGR.trace3_smul
#print axioms NSEGR.trace3_smul
#check @NSEGR.trace3_tf3
#print axioms NSEGR.trace3_tf3
#check @NSEGR.tf3_eq_self_of_trace_zero
#print axioms NSEGR.tf3_eq_self_of_trace_zero
#check @NSEGR.tf3_zero
#print axioms NSEGR.tf3_zero
#check @NSEGR.tf3_idempotent
#print axioms NSEGR.tf3_idempotent
#check @NSEGR.tf3_add
#print axioms NSEGR.tf3_add
#check @NSEGR.tf3_sub
#print axioms NSEGR.tf3_sub
#check @NSEGR.tf3_smul
#print axioms NSEGR.tf3_smul
#check @NSEGR.tf3_symmetric
#print axioms NSEGR.tf3_symmetric
#check @NSEGR.tf3_eq_zero_iff
#print axioms NSEGR.tf3_eq_zero_iff
#check @NSEGR.frobeniusSq3_nonneg
#print axioms NSEGR.frobeniusSq3_nonneg
#check @NSEGR.vectorSq3_nonneg
#print axioms NSEGR.vectorSq3_nonneg
#check @NSEGR.viscosityResidual_affine
#print axioms NSEGR.viscosityResidual_affine
#check @NSEGR.viscosityResidual_difference
#print axioms NSEGR.viscosityResidual_difference
#check @NSEGR.lorentzTrace4_traceReverse4
#print axioms NSEGR.lorentzTrace4_traceReverse4
#check @NSEGR.lorentzTrace4_traceRecover4
#print axioms NSEGR.lorentzTrace4_traceRecover4
#check @NSEGR.traceRecover4_traceReverse4
#print axioms NSEGR.traceRecover4_traceReverse4
#check @NSEGR.traceReverse4_traceRecover4
#print axioms NSEGR.traceReverse4_traceRecover4
#check @NSEGR.traceReverse4_hamiltonian
#print axioms NSEGR.traceReverse4_hamiltonian
#check @NSEGR.boundaryBlock_time_time
#print axioms NSEGR.boundaryBlock_time_time
#check @NSEGR.boundaryBlock_time_space
#print axioms NSEGR.boundaryBlock_time_space
#check @NSEGR.boundaryBlock_space_time
#print axioms NSEGR.boundaryBlock_space_time
#check @NSEGR.boundaryBlock_space_space
#print axioms NSEGR.boundaryBlock_space_space
#check @NSEGR.lorentzTrace4_boundaryBlock
#print axioms NSEGR.lorentzTrace4_boundaryBlock
#check @NSEGR.lorentzSquare4_boundaryBlock
#print axioms NSEGR.lorentzSquare4_boundaryBlock
#check @NSEGR.boundaryBlock_hamiltonian
#print axioms NSEGR.boundaryBlock_hamiltonian
#check @NSEGR.trace3_initialSpatial
#print axioms NSEGR.trace3_initialSpatial
#check @NSEGR.boundaryBlock_hamiltonian_zero_iff
#print axioms NSEGR.boundaryBlock_hamiltonian_zero_iff
#check @NSEGR.initialTimeTime_solves_hamiltonian
#print axioms NSEGR.initialTimeTime_solves_hamiltonian
#check @NSEGR.initial_boundary_hamiltonian
#print axioms NSEGR.initial_boundary_hamiltonian
#check @NSEGR.bulkPoint_radial
#print axioms NSEGR.bulkPoint_radial
#check @NSEGR.bulkPoint_time
#print axioms NSEGR.bulkPoint_time
#check @NSEGR.bulkPoint_spatial
#print axioms NSEGR.bulkPoint_spatial
#check @NSEGR.boundarySpatialTensor_congr_slice
#print axioms NSEGR.boundarySpatialTensor_congr_slice
#check @NSEGR.boundaryBeta_congr_slice
#print axioms NSEGR.boundaryBeta_congr_slice
#check @NSEGR.boundaryRawVelocity_congr_slice
#print axioms NSEGR.boundaryRawVelocity_congr_slice
#check @NSEGR.boundaryVelocity_congr_slice
#print axioms NSEGR.boundaryVelocity_congr_slice
#check @NSEGR.boundaryPotential_congr_slice
#print axioms NSEGR.boundaryPotential_congr_slice
#check @NSEGR.boundaryStress_congr_slice
#print axioms NSEGR.boundaryStress_congr_slice
#check @NSEGR.boundaryStress_trace_zero
#print axioms NSEGR.boundaryStress_trace_zero
#check @NSEGR.boundaryStress_viscosity_difference
#print axioms NSEGR.boundaryStress_viscosity_difference
#check @NSEGR.boundaryK_constant
#print axioms NSEGR.boundaryK_constant
#check @NSEGR.boundaryK_flat
#print axioms NSEGR.boundaryK_flat
#check @NSEGR.boundarySpatialTensor_zero
#print axioms NSEGR.boundarySpatialTensor_zero
#check @NSEGR.boundaryBeta_zero
#print axioms NSEGR.boundaryBeta_zero
#check @NSEGR.boundaryRawVelocity_zero
#print axioms NSEGR.boundaryRawVelocity_zero
#check @NSEGR.boundaryVelocity_zero
#print axioms NSEGR.boundaryVelocity_zero
#check @NSEGR.boundaryPotential_zero
#print axioms NSEGR.boundaryPotential_zero
#check @NSEGR.velocityOuter_zero
#print axioms NSEGR.velocityOuter_zero
#check @NSEGR.boundaryStress_zero
#print axioms NSEGR.boundaryStress_zero
#check @NSEGR.boundaryPartial_const
#print axioms NSEGR.boundaryPartial_const
#check @NSEGR.boundaryHessian_const
#print axioms NSEGR.boundaryHessian_const
#check @NSEGR.boundaryHamiltonian_zero
#print axioms NSEGR.boundaryHamiltonian_zero
#check @NSEGR.boundaryCodazzi_zero
#print axioms NSEGR.boundaryCodazzi_zero
#check @NSEGR.lorentzSign4_mul_self
#print axioms NSEGR.lorentzSign4_mul_self
#check @NSEGR.lowerTensor4_involutive
#print axioms NSEGR.lowerTensor4_involutive
#check @NSEGR.lowerTensor4_add
#print axioms NSEGR.lowerTensor4_add
#check @NSEGR.lowerTensor4_time_time
#print axioms NSEGR.lowerTensor4_time_time
#check @NSEGR.lowerTensor4_time_space
#print axioms NSEGR.lowerTensor4_time_space
#check @NSEGR.lowerTensor4_space_space
#print axioms NSEGR.lowerTensor4_space_space
#check @NSEGR.conservedSourceUpper_time_time
#print axioms NSEGR.conservedSourceUpper_time_time
#check @NSEGR.conservedSourceUpper_time_space
#print axioms NSEGR.conservedSourceUpper_time_space
#check @NSEGR.conservedSourceUpper_space_space
#print axioms NSEGR.conservedSourceUpper_space_space
#check @NSEGR.scalarCompletionUpper_time_time
#print axioms NSEGR.scalarCompletionUpper_time_time
#check @NSEGR.scalarCompletionUpper_time_space
#print axioms NSEGR.scalarCompletionUpper_time_space
#check @NSEGR.scalarCompletionUpper_space_space
#print axioms NSEGR.scalarCompletionUpper_space_space
#check @NSEGR.completedBoundary_trace_recovery
#print axioms NSEGR.completedBoundary_trace_recovery
#check @NSEGR.completedBoundary_hamiltonian_identity
#print axioms NSEGR.completedBoundary_hamiltonian_identity
#check @NSEGR.localNSE_of_reconstruction_and_zero_stress
#print axioms NSEGR.localNSE_of_reconstruction_and_zero_stress
#check @NSEGR.timeInterval_mono
#print axioms NSEGR.timeInterval_mono
#check @NSEGR.timeInterval_mem_nhds
#print axioms NSEGR.timeInterval_mem_nhds
#check @NSEGR.strain_symmetric
#print axioms NSEGR.strain_symmetric
#check @NSEGR.trace_strain
#print axioms NSEGR.trace_strain
#check @NSEGR.trace_strain_eq_zero
#print axioms NSEGR.trace_strain_eq_zero
#check @NSEGR.spatialMean_zero
#print axioms NSEGR.spatialMean_zero
#check @NSEGR.scalarMean_zero
#print axioms NSEGR.scalarMean_zero
#check @NSEGR.spatialPeriodic_const
#print axioms NSEGR.spatialPeriodic_const
#check @NSEGR.spatialPartial_const
#print axioms NSEGR.spatialPartial_const
#check @NSEGR.gradient_const
#print axioms NSEGR.gradient_const
#check @NSEGR.divergence_const
#print axioms NSEGR.divergence_const
#check @NSEGR.laplacian_const
#print axioms NSEGR.laplacian_const
#check @NSEGR.scalarLaplacian_const
#print axioms NSEGR.scalarLaplacian_const
#check @NSEGR.scalarHessian_const
#print axioms NSEGR.scalarHessian_const
#check @NSEGR.strain_const
#print axioms NSEGR.strain_const
#check @NSEGR.tensorDivergence_const
#print axioms NSEGR.tensorDivergence_const
#check @NSEGR.convection_const
#print axioms NSEGR.convection_const
#check @NSEGR.localTimeDerivative_const
#print axioms NSEGR.localTimeDerivative_const
#check @NSEGR.scalarLocalTimeDerivative_const
#print axioms NSEGR.scalarLocalTimeDerivative_const
#check @NSEGR.nseResidual_const
#print axioms NSEGR.nseResidual_const
#check @NSEGR.poissonSymbol_zero
#print axioms NSEGR.poissonSymbol_zero
#check @NSEGR.poissonInverse_zero
#print axioms NSEGR.poissonInverse_zero
#check @NSEGR.leray_const
#print axioms NSEGR.leray_const
#check @NSEGR.leray_zero
#print axioms NSEGR.leray_zero
#check @NSEGR.localNSE_const
#print axioms NSEGR.localNSE_const
#check @NSEGR.localNSE_zero
#print axioms NSEGR.localNSE_zero
#check @NSEGR.poissonInverse_definition
#print axioms NSEGR.poissonInverse_definition
#check @NSEGR.leray_definition
#print axioms NSEGR.leray_definition
#check @NSEGR.bulkPartial_const
#print axioms NSEGR.bulkPartial_const
#check @NSEGR.eta5_symmetric
#print axioms NSEGR.eta5_symmetric
#check @NSEGR.eta5_transpose
#print axioms NSEGR.eta5_transpose
#check @NSEGR.eta5_det
#print axioms NSEGR.eta5_det
#check @NSEGR.lorentzianAt_symmetric
#print axioms NSEGR.lorentzianAt_symmetric
#check @NSEGR.lorentzianAt_det_neg
#print axioms NSEGR.lorentzianAt_det_neg
#check @NSEGR.lorentzianAt_nondegenerate
#print axioms NSEGR.lorentzianAt_nondegenerate
#check @NSEGR.christoffel_constant
#print axioms NSEGR.christoffel_constant
#check @NSEGR.ricci_constant
#print axioms NSEGR.ricci_constant
#check @NSEGR.scalarCurvature_constant
#print axioms NSEGR.scalarCurvature_constant
#check @NSEGR.einstein_constant
#print axioms NSEGR.einstein_constant
#check @NSEGR.constant_vacuumOn
#print axioms NSEGR.constant_vacuumOn
#check @NSEGR.vacuumOn_mono
#print axioms NSEGR.vacuumOn_mono
#check @NSEGR.vacuumOn_implies_einsteinVacuumOn
#print axioms NSEGR.vacuumOn_implies_einsteinVacuumOn
#check @NSEGR.flatMetric_lorentzian
#print axioms NSEGR.flatMetric_lorentzian
#check @NSEGR.flatMetric_symmetric
#print axioms NSEGR.flatMetric_symmetric
#check @NSEGR.flatMetric_det
#print axioms NSEGR.flatMetric_det
#check @NSEGR.flatMetric_nondegenerate
#print axioms NSEGR.flatMetric_nondegenerate
#check @NSEGR.flatMetric_christoffel
#print axioms NSEGR.flatMetric_christoffel
#check @NSEGR.flatMetric_ricci
#print axioms NSEGR.flatMetric_ricci
#check @NSEGR.flatMetric_scalarCurvature
#print axioms NSEGR.flatMetric_scalarCurvature
#check @NSEGR.flatMetric_einstein
#print axioms NSEGR.flatMetric_einstein
#check @NSEGR.flatMetric_vacuumOn
#print axioms NSEGR.flatMetric_vacuumOn
#check @NSEGR.flatMetric_einsteinVacuumOn
#print axioms NSEGR.flatMetric_einsteinVacuumOn
#check @NSEGR.flatMetric_analyticOnNhd
#print axioms NSEGR.flatMetric_analyticOnNhd
#check @NSEGR.native_flat_vacuum
#print axioms NSEGR.native_flat_vacuum
#check @NSEGR.sameFlowAt_refl
#print axioms NSEGR.sameFlowAt_refl
#check @NSEGR.sameFlowAt_symm
#print axioms NSEGR.sameFlowAt_symm
#check @NSEGR.sameFlowAt_trans
#print axioms NSEGR.sameFlowAt_trans
#check @NSEGR.sameFlowAt_iff_origin_gauge
#print axioms NSEGR.sameFlowAt_iff_origin_gauge
#check @NSEGR.NSEgerm.sound
#print axioms NSEGR.NSEgerm.sound
#check @NSEGR.sameMetricAt_refl
#print axioms NSEGR.sameMetricAt_refl
#check @NSEGR.sameMetricAt_symm
#print axioms NSEGR.sameMetricAt_symm
#check @NSEGR.sameMetricAt_trans
#print axioms NSEGR.sameMetricAt_trans
#check @NSEGR.GRgerm.sound
#print axioms NSEGR.GRgerm.sound
#check @NSEGR.nonempty_NSEgerm
#print axioms NSEGR.nonempty_NSEgerm
#check @NSEGR.canonical_stress_trace_zero
#print axioms NSEGR.canonical_stress_trace_zero
#check @NSEGR.gaussianVacuum_nondegenerate
#print axioms NSEGR.gaussianVacuum_nondegenerate
#check @NSEGR.gaussianVacuum_einstein
#print axioms NSEGR.gaussianVacuum_einstein
#check @NSEGR.boundaryAdmissible_zero
#print axioms NSEGR.boundaryAdmissible_zero
#check @NSEGR.flatMetric_not_gaussianVacuum
#print axioms NSEGR.flatMetric_not_gaussianVacuum
#check @NSEGR.boundaryAdmissible_zero_parameter
#print axioms NSEGR.boundaryAdmissible_zero_parameter
#check @NSEGR.LorentzianAt
#print axioms NSEGR.LorentzianAt
#check @NSEGR.ricci
#print axioms NSEGR.ricci
#check @NSEGR.boundaryK
#print axioms NSEGR.boundaryK
#check @NSEGR.boundaryStress
#print axioms NSEGR.boundaryStress
#check @NSEGR.GaussianVacuum
#print axioms NSEGR.GaussianVacuum
#check @NSEGR.CanonicalRepresentative
#print axioms NSEGR.CanonicalRepresentative
#check @NSEGR.LocalNSE
#print axioms NSEGR.LocalNSE
#check @NSEGR.NSEgerm
#print axioms NSEGR.NSEgerm
#check @NSEGR.GRgerm
#print axioms NSEGR.GRgerm
#check @NSEGR.ExactSectorEquivalence
#print axioms NSEGR.ExactSectorEquivalence
#check @NSEGR.ScalarBoundaryCompletionLaws
#print axioms NSEGR.ScalarBoundaryCompletionLaws
#check @NSEGR.AnalyticRadialExtensionLaws
#print axioms NSEGR.AnalyticRadialExtensionLaws
#check @NSEGR.GeometricReconstructionLaws
#print axioms NSEGR.GeometricReconstructionLaws
#check @NSEGR.normalizedBoundaryMatrix_symmetric
#print axioms NSEGR.normalizedBoundaryMatrix_symmetric
#check @NSEGR.constantNormalizedBoundary_beta
#print axioms NSEGR.constantNormalizedBoundary_beta
#check @NSEGR.constantNormalizedBoundary_beta_time
#print axioms NSEGR.constantNormalizedBoundary_beta_time
#check @NSEGR.boundaryCodazzi_constant
#print axioms NSEGR.boundaryCodazzi_constant
#check @NSEGR.constantNormalizedBoundary_codazzi
#print axioms NSEGR.constantNormalizedBoundary_codazzi
#check @NSEGR.constantNormalizedBoundary_hamiltonian
#print axioms NSEGR.constantNormalizedBoundary_hamiltonian
#check @NSEGR.boundaryAdmissible_constantNormalized
#print axioms NSEGR.boundaryAdmissible_constantNormalized
#check @NSEGR.constantNormalizedBoundary_ne_zero
#print axioms NSEGR.constantNormalizedBoundary_ne_zero
#check @NSEGR.exists_boundaryAdmissible
#print axioms NSEGR.exists_boundaryAdmissible
#check @NSEGR.normalizedBoundaryMatrix
#print axioms NSEGR.normalizedBoundaryMatrix
#check @NSEGR.constantNormalizedBoundary
#print axioms NSEGR.constantNormalizedBoundary
#check @NSEGR.gradient_zero
#print axioms NSEGR.gradient_zero
#check @NSEGR.spatialPartial_zero
#print axioms NSEGR.spatialPartial_zero
#check @NSEGR.divergence_zero
#print axioms NSEGR.divergence_zero
#check @NSEGR.laplacian_zero
#print axioms NSEGR.laplacian_zero
#check @NSEGR.scalarLaplacian_zero
#print axioms NSEGR.scalarLaplacian_zero
#check @NSEGR.scalarHessian_zero
#print axioms NSEGR.scalarHessian_zero
#check @NSEGR.strain_zero
#print axioms NSEGR.strain_zero
#check @NSEGR.tensorDivergence_zero
#print axioms NSEGR.tensorDivergence_zero
#check @NSEGR.convection_zero
#print axioms NSEGR.convection_zero
#check @NSEGR.localTimeDerivative_zero
#print axioms NSEGR.localTimeDerivative_zero
#check @NSEGR.scalarLocalTimeDerivative_zero
#print axioms NSEGR.scalarLocalTimeDerivative_zero
#check @NSEGR.nseResidual_zero
#print axioms NSEGR.nseResidual_zero
#check @NSEGR.boundaryVelocity_congr_eventually
#print axioms NSEGR.boundaryVelocity_congr_eventually
#check @NSEGR.boundaryPressure_congr_eventually
#print axioms NSEGR.boundaryPressure_congr_eventually
#check @NSEGR.boundaryFields_sameFlow_of_eventually_eq
#print axioms NSEGR.boundaryFields_sameFlow_of_eventually_eq
#check @NSEGR.origin_pressure_gauge_analytic
#print axioms NSEGR.origin_pressure_gauge_analytic
#check @NSEGR.sameFlowAt_iff_analytic_pressure_gauge
#print axioms NSEGR.sameFlowAt_iff_analytic_pressure_gauge
#check @NSEGR.bulkSpatialCoordinates
#print axioms NSEGR.bulkSpatialCoordinates
#check @NSEGR.bulkPoint_coordinates
#print axioms NSEGR.bulkPoint_coordinates
#check @NSEGR.metric_eventuallyEq_of_fullSlices
#print axioms NSEGR.metric_eventuallyEq_of_fullSlices
#check @NSEGR.sameMetricAt_boundaryK
#print axioms NSEGR.sameMetricAt_boundaryK
#check @NSEGR.sameMetricAt_boundaryFields
#print axioms NSEGR.sameMetricAt_boundaryFields
#check @NSEGR.LiteratureInputs_ck
#print axioms NSEGR.LiteratureInputs_ck
#check @NSEGR.LiteratureInputs_gaussianJet
#print axioms NSEGR.LiteratureInputs_gaussianJet
#check @NSEGR.LiteratureInputs_smoothFourier
#print axioms NSEGR.LiteratureInputs_smoothFourier
#check @NSEGR.fderiv_periodic
#print axioms NSEGR.fderiv_periodic
#check @NSEGR.spatialPartial_periodic
#print axioms NSEGR.spatialPartial_periodic
#check @NSEGR.divergence_periodic
#print axioms NSEGR.divergence_periodic
#check @NSEGR.gradient_periodic
#print axioms NSEGR.gradient_periodic
#check @NSEGR.laplacian_periodic
#print axioms NSEGR.laplacian_periodic
#check @NSEGR.isCompact_unitCube
#print axioms NSEGR.isCompact_unitCube
#check @NSEGR.integrableOn_unitCube_of_continuous
#print axioms NSEGR.integrableOn_unitCube_of_continuous
#check @NSEGR.volume_unitCube
#print axioms NSEGR.volume_unitCube
#check @NSEGR.scalarMean_const
#print axioms NSEGR.scalarMean_const
#check @NSEGR.spatialMean_const
#print axioms NSEGR.spatialMean_const
#check @NSEGR.integral_fderiv_unitVector_zero
#print axioms NSEGR.integral_fderiv_unitVector_zero
#check @NSEGR.spatialMean_spatialPartial_zero
#print axioms NSEGR.spatialMean_spatialPartial_zero
#check @NSEGR.spatialMean_apply
#print axioms NSEGR.spatialMean_apply
#check @NSEGR.gradient_smooth
#print axioms NSEGR.gradient_smooth
#check @NSEGR.spatialMean_gradient_zero
#print axioms NSEGR.spatialMean_gradient_zero
#check @NSEGR.cosineKernel_add_unit_left
#print axioms NSEGR.cosineKernel_add_unit_left
#check @NSEGR.cosineKernel_symm
#print axioms NSEGR.cosineKernel_symm
#check @NSEGR.cosineKernel_add_unit_right
#print axioms NSEGR.cosineKernel_add_unit_right
#check @NSEGR.poissonInverse_periodic
#print axioms NSEGR.poissonInverse_periodic
#check @NSEGR.leray_periodic
#print axioms NSEGR.leray_periodic
#check @NSEGR.spatialPartial_smooth
#print axioms NSEGR.spatialPartial_smooth
#check @NSEGR.integral_spatial_component_zero
#print axioms NSEGR.integral_spatial_component_zero
#check @NSEGR.scalarMean_divergence_zero
#print axioms NSEGR.scalarMean_divergence_zero
#check @NSEGR.lorentzTrace4_lowerTensor4
#print axioms NSEGR.lorentzTrace4_lowerTensor4
#check @NSEGR.lorentzSquare4_lowerTensor4
#print axioms NSEGR.lorentzSquare4_lowerTensor4
#check @NSEGR.sourceHamiltonian4_lowerTensor4
#print axioms NSEGR.sourceHamiltonian4_lowerTensor4
#check @NSEGR.sourceHamiltonian4_boundaryBlock
#print axioms NSEGR.sourceHamiltonian4_boundaryBlock
#check @NSEGR.vectorSq3_sub
#print axioms NSEGR.vectorSq3_sub
#check @NSEGR.trace3_scalarSpatialJet
#print axioms NSEGR.trace3_scalarSpatialJet
#check @NSEGR.frobeniusSq3_scalarSpatialJet
#print axioms NSEGR.frobeniusSq3_scalarSpatialJet
#check @NSEGR.scalarCompletedUpper_eq_block
#print axioms NSEGR.scalarCompletedUpper_eq_block
#check @NSEGR.scalar_hamiltonian_expansion
#print axioms NSEGR.scalar_hamiltonian_expansion
#check @NSEGR.scalar_hamiltonian_expansion_lowered
#print axioms NSEGR.scalar_hamiltonian_expansion_lowered
#check @NSEGR.scalar_hamiltonian_zero_iff
#print axioms NSEGR.scalar_hamiltonian_zero_iff
#check @NSEGR.scalarJetRHS_solves_hamiltonian
#print axioms NSEGR.scalarJetRHS_solves_hamiltonian
#check @NSEGR.scalar_hamiltonian_secondJet_difference
#print axioms NSEGR.scalar_hamiltonian_secondJet_difference
#check @NSEGR.scalar_hamiltonian_initial_jet
#print axioms NSEGR.scalar_hamiltonian_initial_jet
#check @NSEGR.scalar_hamiltonian_initial_noncharacteristic
#print axioms NSEGR.scalar_hamiltonian_initial_noncharacteristic
#check @NSEGR.trace3_scalarHessian
#print axioms NSEGR.trace3_scalarHessian
#check @NSEGR.scalarCompletionUpper_eq_scalarJet
#print axioms NSEGR.scalarCompletionUpper_eq_scalarJet
#check @NSEGR.completedBoundary_hamiltonian_eq_scalarJet
#print axioms NSEGR.completedBoundary_hamiltonian_eq_scalarJet
#check @NSEGR.completedBoundary_hamiltonian_zero_iff_scalar_normal
#print axioms NSEGR.completedBoundary_hamiltonian_zero_iff_scalar_normal
#check @NSEGR.gaussianMatrix_rr
#print axioms NSEGR.gaussianMatrix_rr
#check @NSEGR.gaussianMatrix_rb
#print axioms NSEGR.gaussianMatrix_rb
#check @NSEGR.gaussianMatrix_ar
#print axioms NSEGR.gaussianMatrix_ar
#check @NSEGR.gaussianMatrix_ab
#print axioms NSEGR.gaussianMatrix_ab
#check @NSEGR.gaussianMatrix_one
#print axioms NSEGR.gaussianMatrix_one
#check @NSEGR.gaussianMatrix_mul
#print axioms NSEGR.gaussianMatrix_mul
#check @NSEGR.gaussianMatrix_transpose
#print axioms NSEGR.gaussianMatrix_transpose
#check @NSEGR.gaussianMatrix_isUnit_det
#print axioms NSEGR.gaussianMatrix_isUnit_det
#check @NSEGR.gaussianMatrix_inverse
#print axioms NSEGR.gaussianMatrix_inverse
#check @NSEGR.gaussianMatrix_eta4
#print axioms NSEGR.gaussianMatrix_eta4
#check @NSEGR.gaussianMetric_rr
#print axioms NSEGR.gaussianMetric_rr
#check @NSEGR.gaussianMetric_rb
#print axioms NSEGR.gaussianMetric_rb
#check @NSEGR.gaussianMetric_ar
#print axioms NSEGR.gaussianMetric_ar
#check @NSEGR.gaussianMetric_ab
#print axioms NSEGR.gaussianMetric_ab
#check @NSEGR.inverseMetric_gaussian
#print axioms NSEGR.inverseMetric_gaussian
#check @NSEGR.gaussianMetric_lorentzian_of_congruence
#print axioms NSEGR.gaussianMetric_lorentzian_of_congruence
#check @NSEGR.bulkPartial_gaussian_rr
#print axioms NSEGR.bulkPartial_gaussian_rr
#check @NSEGR.bulkPartial_gaussian_rb
#print axioms NSEGR.bulkPartial_gaussian_rb
#check @NSEGR.bulkPartial_gaussian_ar
#print axioms NSEGR.bulkPartial_gaussian_ar
#check @NSEGR.bulkPartial_gaussian_ab
#print axioms NSEGR.bulkPartial_gaussian_ab
#check @NSEGR.boundaryK_gaussian
#print axioms NSEGR.boundaryK_gaussian
#check @NSEGR.christoffel_gaussian_rr
#print axioms NSEGR.christoffel_gaussian_rr
#check @NSEGR.christoffel_gaussian_rab
#print axioms NSEGR.christoffel_gaussian_rab
#check @NSEGR.christoffel_gaussian_rrb
#print axioms NSEGR.christoffel_gaussian_rrb
#check @NSEGR.christoffel_gaussian_arb
#print axioms NSEGR.christoffel_gaussian_arb
#check @NSEGR.christoffel_gaussian_abc
#print axioms NSEGR.christoffel_gaussian_abc
#check @NSEGR.reconstruction_trace_scalarHessian
#print axioms NSEGR.reconstruction_trace_scalarHessian
#check @NSEGR.reconstruction_trace_velocityOuter
#print axioms NSEGR.reconstruction_trace_velocityOuter
#check @NSEGR.reconstruction_trace_boundarySpatial
#print axioms NSEGR.reconstruction_trace_boundarySpatial
#check @NSEGR.reconstruction_lorentzTrace_boundary
#print axioms NSEGR.reconstruction_lorentzTrace_boundary
#check @NSEGR.reconstruction_eta4_spatial
#print axioms NSEGR.reconstruction_eta4_spatial
#check @NSEGR.boundaryPreStress_trace
#print axioms NSEGR.boundaryPreStress_trace
#check @NSEGR.boundarySpatial_eq_of_stress_zero
#print axioms NSEGR.boundarySpatial_eq_of_stress_zero
#check @NSEGR.boundary_eq_completedBoundary_of_zero_stress
#print axioms NSEGR.boundary_eq_completedBoundary_of_zero_stress
#check @NSEGR.boundary_slice_eq_completedBoundary_of_zero_stress
#print axioms NSEGR.boundary_slice_eq_completedBoundary_of_zero_stress
#check @NSEGR.reconstruction_residual_of_differential_identities
#print axioms NSEGR.reconstruction_residual_of_differential_identities
#check @NSEGR.literatureCharacter_eq_exp_phase
#print axioms NSEGR.literatureCharacter_eq_exp_phase
#check @NSEGR.fourierPhase_neg
#print axioms NSEGR.fourierPhase_neg
#check @NSEGR.fourierPhase_sub
#print axioms NSEGR.fourierPhase_sub
#check @NSEGR.literatureCharacter_mul_negative
#print axioms NSEGR.literatureCharacter_mul_negative
#check @NSEGR.cosineKernel_eq_re_character
#print axioms NSEGR.cosineKernel_eq_re_character
#check @NSEGR.literatureCharacter_continuous
#print axioms NSEGR.literatureCharacter_continuous
#check @NSEGR.cosineKernel_integral_eq_re_fourier
#print axioms NSEGR.cosineKernel_integral_eq_re_fourier
#check @NSEGR.poissonInverse_eq_tsum_fourier_re
#print axioms NSEGR.poissonInverse_eq_tsum_fourier_re
#check @NSEGR.poissonInverse_eq_re_tsum_fourier
#print axioms NSEGR.poissonInverse_eq_re_tsum_fourier
#check @NSEGR.frequency_square_sum_ge_one
#print axioms NSEGR.frequency_square_sum_ge_one
#check @NSEGR.poissonSymbol_abs_le_one
#print axioms NSEGR.poissonSymbol_abs_le_one
#check @NSEGR.literatureCharacter_norm
#print axioms NSEGR.literatureCharacter_norm
#check @NSEGR.literatureFourierCoefficient_summable_norm
#print axioms NSEGR.literatureFourierCoefficient_summable_norm
#check @NSEGR.poisson_fourier_summable_of_literature
#print axioms NSEGR.poisson_fourier_summable_of_literature
#check @NSEGR.poissonInverse_series_summable_of_literature
#print axioms NSEGR.poissonInverse_series_summable_of_literature
#check @NSEGR.poissonInverse_eq_re_tsum_fourier_of_literature
#print axioms NSEGR.poissonInverse_eq_re_tsum_fourier_of_literature
#check @NSEGR.analyticAt_fin3_sum
#print axioms NSEGR.analyticAt_fin3_sum
#check @NSEGR.analyticAt_trace3_components
#print axioms NSEGR.analyticAt_trace3_components
#check @NSEGR.analyticAt_vectorDot3_components
#print axioms NSEGR.analyticAt_vectorDot3_components
#check @NSEGR.analyticAt_vectorSq3_components
#print axioms NSEGR.analyticAt_vectorSq3_components
#check @NSEGR.analyticAt_frobeniusInner3_components
#print axioms NSEGR.analyticAt_frobeniusInner3_components
#check @NSEGR.analyticAt_frobeniusSq3_components
#print axioms NSEGR.analyticAt_frobeniusSq3_components
#check @NSEGR.analyticAt_sourceHamiltonian4_boundaryBlock
#print axioms NSEGR.analyticAt_sourceHamiltonian4_boundaryBlock
#check @NSEGR.analyticAt_scalarJetRHS_components
#print axioms NSEGR.analyticAt_scalarJetRHS_components
#check @NSEGR.analyticOnNhd_scalarJetRHS_components
#print axioms NSEGR.analyticOnNhd_scalarJetRHS_components
#check @NSEGR.compact_slice_eventually_eq
#print axioms NSEGR.compact_slice_eventually_eq
#check @NSEGR.integerSpatialShift_apply
#print axioms NSEGR.integerSpatialShift_apply
#check @NSEGR.spatialCellRepresentative_mem_unitCube
#print axioms NSEGR.spatialCellRepresentative_mem_unitCube
#check @NSEGR.spatialCellRepresentative_add_shift
#print axioms NSEGR.spatialCellRepresentative_add_shift
#check @NSEGR.spatialPeriodic_integerSpatialShift
#print axioms NSEGR.spatialPeriodic_integerSpatialShift
#check @NSEGR.spatialPeriodic_eq_cellRepresentative
#print axioms NSEGR.spatialPeriodic_eq_cellRepresentative
#check @NSEGR.spatialPeriodic_eq_of_eqOn_unitCube
#print axioms NSEGR.spatialPeriodic_eq_of_eqOn_unitCube
#check @NSEGR.periodic_slice_germs_uniform
#print axioms NSEGR.periodic_slice_germs_uniform
#check @NSEGR.continuous_bulkPoint_product
#print axioms NSEGR.continuous_bulkPoint_product
#check @NSEGR.sameMetricAt_of_boundary_germs
#print axioms NSEGR.sameMetricAt_of_boundary_germs
#check @NSEGR.gaussianVacuum_eventually_periodic
#print axioms NSEGR.gaussianVacuum_eventually_periodic
#check @NSEGR.gaussianVacuum_sameMetricAt_of_boundary_germs
#print axioms NSEGR.gaussianVacuum_sameMetricAt_of_boundary_germs
#check @NSEGR.boundaryPressure_hasFDerivAt
#print axioms NSEGR.boundaryPressure_hasFDerivAt
#check @NSEGR.boundaryPressure_gradient
#print axioms NSEGR.boundaryPressure_gradient
#check @NSEGR.reconstruction_residual_of_three_differential_identities
#print axioms NSEGR.reconstruction_residual_of_three_differential_identities
#check @NSEGR.bulkCollar_eventually_boundary
#print axioms NSEGR.bulkCollar_eventually_boundary
#check @NSEGR.boundaryAdmissible_literatureFlatBoundaryGerm
#print axioms NSEGR.boundaryAdmissible_literatureFlatBoundaryGerm
#check @NSEGR.gaussianVacuum_literatureFlatGaussianGerm
#print axioms NSEGR.gaussianVacuum_literatureFlatGaussianGerm
#check @NSEGR.literatureGaussianJet_unique
#print axioms NSEGR.literatureGaussianJet_unique
#check @NSEGR.gaussianVacuum_sameMetricAt_of_literatureJet
#print axioms NSEGR.gaussianVacuum_sameMetricAt_of_literatureJet
#check @NSEGR.analyticAt_spatialPartial_joint
#print axioms NSEGR.analyticAt_spatialPartial_joint
#check @NSEGR.analyticAt_nseSpatialSource3_components
#print axioms NSEGR.analyticAt_nseSpatialSource3_components
#check @NSEGR.scalarCKRHS_potential
#print axioms NSEGR.scalarCKRHS_potential
#check @NSEGR.scalarCKRHS_time
#print axioms NSEGR.scalarCKRHS_time
#check @NSEGR.scalarCKRHS_gradient
#print axioms NSEGR.scalarCKRHS_gradient
#check @NSEGR.analyticAt_scalarCKJet_entry
#print axioms NSEGR.analyticAt_scalarCKJet_entry
#check @NSEGR.analyticAt_scalarCKRHS
#print axioms NSEGR.analyticAt_scalarCKRHS
#check @NSEGR.scalarCK_zero_initial_noncharacteristic
#print axioms NSEGR.scalarCK_zero_initial_noncharacteristic
#check @NSEGR.scalarCK_exists_unique_firstOrder
#print axioms NSEGR.scalarCK_exists_unique_firstOrder
#check @NSEGR.StressCalc.component_fderiv
#print axioms NSEGR.StressCalc.component_fderiv
#check @NSEGR.StressCalc.partial_component_smooth
#print axioms NSEGR.StressCalc.partial_component_smooth
#check @NSEGR.StressCalc.partial_partial
#print axioms NSEGR.StressCalc.partial_partial
#check @NSEGR.StressCalc.secondSpatial_symm
#print axioms NSEGR.StressCalc.secondSpatial_symm
#check @NSEGR.StressCalc.partial_component_fderiv
#print axioms NSEGR.StressCalc.partial_component_fderiv
#check @NSEGR.StressCalc.gradient_divergence_component
#print axioms NSEGR.StressCalc.gradient_divergence_component
#check @NSEGR.StressCalc.laplacian_component
#print axioms NSEGR.StressCalc.laplacian_component
#check @NSEGR.StressCalc.vector_decomposition
#print axioms NSEGR.StressCalc.vector_decomposition
#check @NSEGR.StressCalc.convection_component
#print axioms NSEGR.StressCalc.convection_component
#check @NSEGR.tensorDivergence_strain
#print axioms NSEGR.tensorDivergence_strain
#check @NSEGR.tensorDivergence_strain_of_divergence_zero
#print axioms NSEGR.tensorDivergence_strain_of_divergence_zero
#check @NSEGR.tensorDivergence_tf3_strain_of_divergence_zero
#print axioms NSEGR.tensorDivergence_tf3_strain_of_divergence_zero
#check @NSEGR.tensorDivergence_velocityOuter
#print axioms NSEGR.tensorDivergence_velocityOuter
#check @NSEGR.tensorDivergence_velocityOuter_of_divergence_zero
#print axioms NSEGR.tensorDivergence_velocityOuter_of_divergence_zero
#check @NSEGR.divergence_gradient
#print axioms NSEGR.divergence_gradient
#check @NSEGR.tensorDivergence_scalarHessian
#print axioms NSEGR.tensorDivergence_scalarHessian
#check @NSEGR.tensorDivergence_add
#print axioms NSEGR.tensorDivergence_add
#check @NSEGR.tensorDivergence_sub
#print axioms NSEGR.tensorDivergence_sub
#check @NSEGR.tensorDivergence_smul
#print axioms NSEGR.tensorDivergence_smul
#check @NSEGR.tensorDivergence_isotropic
#print axioms NSEGR.tensorDivergence_isotropic
#check @NSEGR.scalarHessian_component_smooth
#print axioms NSEGR.scalarHessian_component_smooth
#check @NSEGR.strain_component_smooth
#print axioms NSEGR.strain_component_smooth
#check @NSEGR.velocityOuter_component_smooth
#print axioms NSEGR.velocityOuter_component_smooth
#check @NSEGR.vectorSq3_smooth
#print axioms NSEGR.vectorSq3_smooth
#check @NSEGR.boundaryStress_tensorDivergence
#print axioms NSEGR.boundaryStress_tensorDivergence
#check @NSEGR.reconstruction_residual_of_codazzi_hodge
#print axioms NSEGR.reconstruction_residual_of_codazzi_hodge
#check @NSEGR.literatureCharacter_zero
#print axioms NSEGR.literatureCharacter_zero
#check @NSEGR.literatureFourierCoefficient_zero
#print axioms NSEGR.literatureFourierCoefficient_zero
#check @NSEGR.literatureFourier_hasSum_real
#print axioms NSEGR.literatureFourier_hasSum_real
#check @NSEGR.literatureFourier_nonzero_hasSum
#print axioms NSEGR.literatureFourier_nonzero_hasSum
#check @NSEGR.cosine_nonzero_hasSum_of_literature
#print axioms NSEGR.cosine_nonzero_hasSum_of_literature
#check @NSEGR.fourierScalarPartial_smooth
#print axioms NSEGR.fourierScalarPartial_smooth
#check @NSEGR.fourierScalarPartial_periodic
#print axioms NSEGR.fourierScalarPartial_periodic
#check @NSEGR.scalarLaplacian_smooth
#print axioms NSEGR.scalarLaplacian_smooth
#check @NSEGR.scalarLaplacian_periodic
#print axioms NSEGR.scalarLaplacian_periodic
#check @NSEGR.fourierScalarPartial_ofReal
#print axioms NSEGR.fourierScalarPartial_ofReal
#check @NSEGR.literaturePartialWord_pair_ofReal
#print axioms NSEGR.literaturePartialWord_pair_ofReal
#check @NSEGR.literatureFourierCoefficient_secondPartial
#print axioms NSEGR.literatureFourierCoefficient_secondPartial
#check @NSEGR.literatureFourierCoefficient_scalarLaplacian
#print axioms NSEGR.literatureFourierCoefficient_scalarLaplacian
#check @NSEGR.poissonSymbol_mul_scalarLaplacianSymbol
#print axioms NSEGR.poissonSymbol_mul_scalarLaplacianSymbol
#check @NSEGR.poissonInverse_scalarLaplacian_of_literature
#print axioms NSEGR.poissonInverse_scalarLaplacian_of_literature
#check @NSEGR.gradient_sub_constant
#print axioms NSEGR.gradient_sub_constant
#check @NSEGR.leray_gradient_of_literature
#print axioms NSEGR.leray_gradient_of_literature
#check @NSEGR.gaussianMatrix_det
#print axioms NSEGR.gaussianMatrix_det
#check @NSEGR.inverseMetric_gaussian_singular
#print axioms NSEGR.inverseMetric_gaussian_singular
#check @NSEGR.christoffel_gaussian_singular
#print axioms NSEGR.christoffel_gaussian_singular
#check @NSEGR.gaussianShapeOperator_singular
#print axioms NSEGR.gaussianShapeOperator_singular
#check @NSEGR.gaussianTangentialChristoffel_singular
#print axioms NSEGR.gaussianTangentialChristoffel_singular
#check @NSEGR.christoffel_gaussian_rrb_total
#print axioms NSEGR.christoffel_gaussian_rrb_total
#check @NSEGR.christoffel_gaussian_shape
#print axioms NSEGR.christoffel_gaussian_shape
#check @NSEGR.christoffel_gaussian_abc_total
#print axioms NSEGR.christoffel_gaussian_abc_total
#check @NSEGR.ricci_gaussian_mixed
#print axioms NSEGR.ricci_gaussian_mixed
#check @NSEGR.ricci_gaussian_normal
#print axioms NSEGR.ricci_gaussian_normal
#check @NSEGR.gaussianCodazziComponent_zero_of_vacuum
#print axioms NSEGR.gaussianCodazziComponent_zero_of_vacuum
#check @NSEGR.gaussianNormalRicciComponent_zero_of_vacuum
#print axioms NSEGR.gaussianNormalRicciComponent_zero_of_vacuum
#check @NSEGR.analyticAt_scalarJointPartial
#print axioms NSEGR.analyticAt_scalarJointPartial
#check @NSEGR.scalarJointPartial_commute
#print axioms NSEGR.scalarJointPartial_commute
#check @NSEGR.scalar_timeDerivative_eq_joint
#print axioms NSEGR.scalar_timeDerivative_eq_joint
#check @NSEGR.scalar_spatialDerivative_eq_joint
#print axioms NSEGR.scalar_spatialDerivative_eq_joint
#check @NSEGR.analytic_zero_transport_germ
#print axioms NSEGR.analytic_zero_transport_germ
#check @NSEGR.scalarCK_coordinate_jointDerivative
#print axioms NSEGR.scalarCK_coordinate_jointDerivative
#check @NSEGR.scalarCK_spatial_coordinate_derivative
#print axioms NSEGR.scalarCK_spatial_coordinate_derivative
#check @NSEGR.scalarCK_solution_transport
#print axioms NSEGR.scalarCK_solution_transport
#check @NSEGR.scalarCK_gradient_compatibility
#print axioms NSEGR.scalarCK_gradient_compatibility
#check @NSEGR.forward_velocity_recovery
#print axioms NSEGR.forward_velocity_recovery
#check @NSEGR.NSE_TO_GR_OF_SCALAR_AND_RADIAL_COMPLETION
#print axioms NSEGR.NSE_TO_GR_OF_SCALAR_AND_RADIAL_COMPLETION
#check @NSEGR.nonempty_GRgerm_of_completion
#print axioms NSEGR.nonempty_GRgerm_of_completion
#check @NSEGR.forwardRepresentative
#print axioms NSEGR.forwardRepresentative
#check @NSEGR.forward_boundary_match_eventually
#print axioms NSEGR.forward_boundary_match_eventually
#check @NSEGR.forward_pressure_gauge_recovery
#print axioms NSEGR.forward_pressure_gauge_recovery
#check @NSEGR.GR_TO_NSE_OF_GEOMETRIC_RECONSTRUCTION
#print axioms NSEGR.GR_TO_NSE_OF_GEOMETRIC_RECONSTRUCTION
#check @NSEGR.reverseGerm_forwardGerm
#print axioms NSEGR.reverseGerm_forwardGerm
#check @NSEGR.forwardGerm_reverseGerm
#print axioms NSEGR.forwardGerm_reverseGerm
#check @NSEGR.NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_NAMED_CONTRACTS
#print axioms NSEGR.NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_NAMED_CONTRACTS
#check @NSEGR.GermInverseLaws
#print axioms NSEGR.GermInverseLaws
#check @NSEGR.exactSectorEquivOfContracts
#print axioms NSEGR.exactSectorEquivOfContracts
#check @GRTemp.ML001.endpoint
#print axioms GRTemp.ML001.endpoint
#check @GRTemp.ML002.endpoint
#print axioms GRTemp.ML002.endpoint
#check @GRTemp.ML003.endpoint
#print axioms GRTemp.ML003.endpoint
#check @GRTemp.ML004.endpoint
#print axioms GRTemp.ML004.endpoint
#check @GRTemp.ML005.endpoint
#print axioms GRTemp.ML005.endpoint
#check @GRTemp.ML006.endpoint
#print axioms GRTemp.ML006.endpoint
#check @GRTemp.ML007.endpoint
#print axioms GRTemp.ML007.endpoint
#check @GRTemp.ML008.endpoint
#print axioms GRTemp.ML008.endpoint
#check @GRTemp.ML009.endpoint
#print axioms GRTemp.ML009.endpoint
#check @GRTemp.ML010.endpoint
#print axioms GRTemp.ML010.endpoint
#check @GRTemp.ML011.endpoint
#print axioms GRTemp.ML011.endpoint
#check @GRTemp.ML012.endpoint
#print axioms GRTemp.ML012.endpoint
#check @GRTemp.ML013.endpoint
#print axioms GRTemp.ML013.endpoint
#check @GRTemp.ML014.endpoint
#print axioms GRTemp.ML014.endpoint
#check @GRTemp.ML015.endpoint
#print axioms GRTemp.ML015.endpoint
#check @GRTemp.ML016.endpoint
#print axioms GRTemp.ML016.endpoint
#check @GRTemp.ML017.endpoint
#print axioms GRTemp.ML017.endpoint
#check @GRTemp.ML018.endpoint
#print axioms GRTemp.ML018.endpoint
#check @GRTemp.ML019.endpoint
#print axioms GRTemp.ML019.endpoint
#check @GRTemp.ML020.endpoint
#print axioms GRTemp.ML020.endpoint
#check @GRTemp.ML021.endpoint
#print axioms GRTemp.ML021.endpoint
#check @GRTemp.ML022.endpoint
#print axioms GRTemp.ML022.endpoint
#check @GRTemp.ML023.endpoint
#print axioms GRTemp.ML023.endpoint
#check @GRTemp.ML024.endpoint
#print axioms GRTemp.ML024.endpoint
#check @GRTemp.ML025.endpoint
#print axioms GRTemp.ML025.endpoint
#check @GRTemp.ML026.endpoint
#print axioms GRTemp.ML026.endpoint
#check @GRTemp.ML027.endpoint
#print axioms GRTemp.ML027.endpoint
#check @GRTemp.ML028.endpoint
#print axioms GRTemp.ML028.endpoint
#check @GRTemp.ML029.endpoint
#print axioms GRTemp.ML029.endpoint
#check @GRTemp.ML030.endpoint
#print axioms GRTemp.ML030.endpoint
#check @GRTemp.ML031.endpoint
#print axioms GRTemp.ML031.endpoint
#check @GRTemp.ML032.endpoint
#print axioms GRTemp.ML032.endpoint
#check @GRTemp.ML033.endpoint
#print axioms GRTemp.ML033.endpoint
#check @GRTemp.ML034.endpoint
#print axioms GRTemp.ML034.endpoint
#check @GRTemp.ML035.endpoint
#print axioms GRTemp.ML035.endpoint
#check @GRTemp.ML036.endpoint
#print axioms GRTemp.ML036.endpoint
#check @GRTemp.ML037.endpoint
#print axioms GRTemp.ML037.endpoint
#check @GRTemp.ML038.endpoint
#print axioms GRTemp.ML038.endpoint
#check @GRTemp.ML039.endpoint
#print axioms GRTemp.ML039.endpoint
#check @GRTemp.ML040.endpoint
#print axioms GRTemp.ML040.endpoint
#check @GRTemp.ML041.endpoint
#print axioms GRTemp.ML041.endpoint
#check @GRTemp.ML042.endpoint
#print axioms GRTemp.ML042.endpoint
#check @GRTemp.ML043.endpoint
#print axioms GRTemp.ML043.endpoint
#check @GRTemp.ML044.endpoint
#print axioms GRTemp.ML044.endpoint
#check @GRTemp.ML045.endpoint
#print axioms GRTemp.ML045.endpoint
#check @GRTemp.ML046.endpoint
#print axioms GRTemp.ML046.endpoint
#check @GRTemp.ML047.endpoint
#print axioms GRTemp.ML047.endpoint
#check @GRTemp.ML048.endpoint
#print axioms GRTemp.ML048.endpoint
#check @GRTemp.ML049.endpoint
#print axioms GRTemp.ML049.endpoint
#check @GRTemp.ML050.endpoint
#print axioms GRTemp.ML050.endpoint
#check @GRTemp.ML051.endpoint
#print axioms GRTemp.ML051.endpoint
#check @GRTemp.ML052.endpoint
#print axioms GRTemp.ML052.endpoint
#check @GRTemp.ML053.endpoint
#print axioms GRTemp.ML053.endpoint
#check @GRTemp.ML054.endpoint
#print axioms GRTemp.ML054.endpoint
#check @GRTemp.ML055.endpoint
#print axioms GRTemp.ML055.endpoint
#check @GRTemp.ML056.endpoint
#print axioms GRTemp.ML056.endpoint
#check @GRTemp.ML057.endpoint
#print axioms GRTemp.ML057.endpoint
#check @GRTemp.ML058.endpoint
#print axioms GRTemp.ML058.endpoint
#check @GRTemp.ML059.endpoint
#print axioms GRTemp.ML059.endpoint
#check @GRTemp.ML060.endpoint
#print axioms GRTemp.ML060.endpoint
#check @GRTemp.ML061.endpoint
#print axioms GRTemp.ML061.endpoint
#check @GRTemp.ML062.endpoint
#print axioms GRTemp.ML062.endpoint
#check @GRTemp.ML063.endpoint
#print axioms GRTemp.ML063.endpoint
#check @GRTemp.ML064.endpoint
#print axioms GRTemp.ML064.endpoint
#check @GRTemp.ML065.endpoint
#print axioms GRTemp.ML065.endpoint
#check @GRTemp.ME01.endpoint
#print axioms GRTemp.ME01.endpoint
#check @GRTemp.ME02.endpoint
#print axioms GRTemp.ME02.endpoint
#check @GRTemp.ME03.endpoint
#print axioms GRTemp.ME03.endpoint
#check @GRTemp.ME04.endpoint
#print axioms GRTemp.ME04.endpoint
#check @GRTemp.ME05.endpoint
#print axioms GRTemp.ME05.endpoint
#check @GRTemp.ME06.endpoint
#print axioms GRTemp.ME06.endpoint
#check @GRTemp.ME07.endpoint
#print axioms GRTemp.ME07.endpoint
#check @GRTemp.ME08.endpoint
#print axioms GRTemp.ME08.endpoint
#check @GRTemp.ME09.endpoint
#print axioms GRTemp.ME09.endpoint
#check @GRTemp.ME10.endpoint
#print axioms GRTemp.ME10.endpoint
#check @GRTemp.ME11.endpoint
#print axioms GRTemp.ME11.endpoint
#check @GRTemp.ME12.endpoint
#print axioms GRTemp.ME12.endpoint
#check @GRTemp.ME13.endpoint
#print axioms GRTemp.ME13.endpoint
#check @GRTemp.ME14.endpoint
#print axioms GRTemp.ME14.endpoint
#check @GRTemp.ME15.endpoint
#print axioms GRTemp.ME15.endpoint
#check @GRTemp.ME16.E01.endpoint
#print axioms GRTemp.ME16.E01.endpoint
#check @GRTemp.ME16.E02.endpoint
#print axioms GRTemp.ME16.E02.endpoint
#check @GRTemp.ME16.E03.endpoint
#print axioms GRTemp.ME16.E03.endpoint
#check @GRTemp.ME17.E01.endpoint
#print axioms GRTemp.ME17.E01.endpoint
#check @GRTemp.ME17.E02.endpoint
#print axioms GRTemp.ME17.E02.endpoint
#check @NSEGR.Assembly.coordinateExpWeight
#print axioms NSEGR.Assembly.coordinateExpWeight
#check @NSEGR.Assembly.coordinateExpWeight_nonneg
#print axioms NSEGR.Assembly.coordinateExpWeight_nonneg
#check @NSEGR.Assembly.summable_coordinateExpWeight
#print axioms NSEGR.Assembly.summable_coordinateExpWeight
#check @NSEGR.Assembly.frequencyTriple
#print axioms NSEGR.Assembly.frequencyTriple
#check @NSEGR.Assembly.frequencyTriple_injective
#print axioms NSEGR.Assembly.frequencyTriple_injective
#check @NSEGR.Assembly.latticeExpMajorant
#print axioms NSEGR.Assembly.latticeExpMajorant
#check @NSEGR.Assembly.latticeExpMajorant_nonneg
#print axioms NSEGR.Assembly.latticeExpMajorant_nonneg
#check @NSEGR.Assembly.summable_latticeExpMajorant
#print axioms NSEGR.Assembly.summable_latticeExpMajorant
#check @NSEGR.Assembly.frequencyL1
#print axioms NSEGR.Assembly.frequencyL1
#check @NSEGR.Assembly.frequencyExpWeight
#print axioms NSEGR.Assembly.frequencyExpWeight
#check @NSEGR.Assembly.frequencyExpWeight_eq_lattice
#print axioms NSEGR.Assembly.frequencyExpWeight_eq_lattice
#check @NSEGR.Assembly.summable_frequencyExpWeight
#print axioms NSEGR.Assembly.summable_frequencyExpWeight
#check @NSEGR.Assembly.summable_scaled_frequencyExpWeight
#print axioms NSEGR.Assembly.summable_scaled_frequencyExpWeight
#check @NSEGR.Assembly.complexPoissonMode
#print axioms NSEGR.Assembly.complexPoissonMode
#check @NSEGR.Assembly.realPoissonMode
#print axioms NSEGR.Assembly.realPoissonMode
#check @NSEGR.Assembly.complexPoissonMode_norm_le
#print axioms NSEGR.Assembly.complexPoissonMode_norm_le
#check @NSEGR.Assembly.realPoissonMode_eq_re
#print axioms NSEGR.Assembly.realPoissonMode_eq_re
#check @NSEGR.Assembly.realPoissonMode_norm_le
#print axioms NSEGR.Assembly.realPoissonMode_norm_le
#check @NSEGR.Assembly.realPoissonMode_continuous
#print axioms NSEGR.Assembly.realPoissonMode_continuous
#check @NSEGR.Assembly.poissonInverse_uniform_of_summable_coefficients
#print axioms NSEGR.Assembly.poissonInverse_uniform_of_summable_coefficients
#check @NSEGR.Assembly.poissonInverse_continuous_of_summable_coefficients
#print axioms NSEGR.Assembly.poissonInverse_continuous_of_summable_coefficients
#check @NSEGR.Assembly.poissonInverse_uniform_of_literature
#print axioms NSEGR.Assembly.poissonInverse_uniform_of_literature
#check @NSEGR.Assembly.poissonInverse_continuous_of_literature
#print axioms NSEGR.Assembly.poissonInverse_continuous_of_literature
#check @NSEGR.Assembly.poissonInverse_parameter_uniform
#print axioms NSEGR.Assembly.poissonInverse_parameter_uniform
#check @NSEGR.Assembly.realPoissonMode_parameter_continuousOn
#print axioms NSEGR.Assembly.realPoissonMode_parameter_continuousOn
#check @NSEGR.Assembly.poissonInverse_parameter_continuousOn
#print axioms NSEGR.Assembly.poissonInverse_parameter_continuousOn
#check @NSEGR.Assembly.poissonInverse_parameter_continuousOn_of_exponential_bound
#print axioms NSEGR.Assembly.poissonInverse_parameter_continuousOn_of_exponential_bound
#check @NSEGR.Assembly.gaugeCKRHS
#print axioms NSEGR.Assembly.gaugeCKRHS
#check @NSEGR.Assembly.gaugeCKRHS_potential
#print axioms NSEGR.Assembly.gaugeCKRHS_potential
#check @NSEGR.Assembly.gaugeCKRHS_velocity
#print axioms NSEGR.Assembly.gaugeCKRHS_velocity
#check @NSEGR.Assembly.analyticAt_gaugeCKRHS
#print axioms NSEGR.Assembly.analyticAt_gaugeCKRHS
#check @NSEGR.Assembly.gaugeCK_exists_unique_firstOrder
#print axioms NSEGR.Assembly.gaugeCK_exists_unique_firstOrder
#check @NSEGR.Assembly.gaugeCK_coordinate_timeDerivative
#print axioms NSEGR.Assembly.gaugeCK_coordinate_timeDerivative
#check @NSEGR.Assembly.gaugeCK_solution_transport
#print axioms NSEGR.Assembly.gaugeCK_solution_transport
#check @NSEGR.Assembly.analytic_double_primitive_of_literatureCK
#print axioms NSEGR.Assembly.analytic_double_primitive_of_literatureCK
#check @NSEGR.Assembly.bulkPartial_congr_of_eventuallyEq
#print axioms NSEGR.Assembly.bulkPartial_congr_of_eventuallyEq
#check @NSEGR.Assembly.bulkPartial_neg
#print axioms NSEGR.Assembly.bulkPartial_neg
#check @NSEGR.Assembly.christoffel_gaussian_rbr_total
#print axioms NSEGR.Assembly.christoffel_gaussian_rbr_total
#check @NSEGR.Assembly.christoffel_gaussian_abr_total
#print axioms NSEGR.Assembly.christoffel_gaussian_abr_total
#check @NSEGR.Assembly.radial_christoffel_derivative
#print axioms NSEGR.Assembly.radial_christoffel_derivative
#check @NSEGR.Assembly.gaussianTangentialRicciComponent
#print axioms NSEGR.Assembly.gaussianTangentialRicciComponent
#check @NSEGR.Assembly.ricci_gaussian_tangential
#print axioms NSEGR.Assembly.ricci_gaussian_tangential
#check @NSEGR.Assembly.gaussianTangentialRicciComponent_zero_of_vacuum
#print axioms NSEGR.Assembly.gaussianTangentialRicciComponent_zero_of_vacuum
#check @NSEGR.Assembly.gaussian_vacuum_iff_components
#print axioms NSEGR.Assembly.gaussian_vacuum_iff_components
#check @NSEGR.Assembly.poissonInverse_hasDerivAt_global
#print axioms NSEGR.Assembly.poissonInverse_hasDerivAt_global
#check @NSEGR.Assembly.scalarMean_hasDerivAt_global
#print axioms NSEGR.Assembly.scalarMean_hasDerivAt_global
#check @NSEGR.Assembly.cutoff_mul_contDiff
#print axioms NSEGR.Assembly.cutoff_mul_contDiff
#check @NSEGR.Assembly.exists_smooth_periodic_extension
#print axioms NSEGR.Assembly.exists_smooth_periodic_extension
#check @NSEGR.Assembly.poissonInverse_hasDerivAt_local
#print axioms NSEGR.Assembly.poissonInverse_hasDerivAt_local
#check @NSEGR.Assembly.poissonInverse_localTimeDerivative
#print axioms NSEGR.Assembly.poissonInverse_localTimeDerivative
#check @NSEGR.Assembly.scalarMean_hasDerivAt_local
#print axioms NSEGR.Assembly.scalarMean_hasDerivAt_local
#check @NSEGR.Assembly.scalarTimeDerivative_eq_local
#print axioms NSEGR.Assembly.scalarTimeDerivative_eq_local
#check @NSEGR.Assembly.poissonInverse_halfspace_smooth
#print axioms NSEGR.Assembly.poissonInverse_halfspace_smooth
#check @NSEGR.Assembly.scalarL_hasDerivAt_pos
#print axioms NSEGR.Assembly.scalarL_hasDerivAt_pos
#check @NSEGR.Assembly.poissonInverse_hasDerivAt_pos
#print axioms NSEGR.Assembly.poissonInverse_hasDerivAt_pos
#check @NSEGR.Assembly.poissonInverse_localTimeDerivative_pos
#print axioms NSEGR.Assembly.poissonInverse_localTimeDerivative_pos
#check @NSEGR.Assembly.scalarMean_hasDerivAt_pos
#print axioms NSEGR.Assembly.scalarMean_hasDerivAt_pos
#check @NSEGR.Assembly.poissonSymbol_eq_neg_methlib
#print axioms NSEGR.Assembly.poissonSymbol_eq_neg_methlib
#check @NSEGR.Assembly.poissonInverse_eq_neg_scalarL
#print axioms NSEGR.Assembly.poissonInverse_eq_neg_scalarL
#check @NSEGR.Assembly.poissonInverse_smooth
#print axioms NSEGR.Assembly.poissonInverse_smooth
#check @NSEGR.Assembly.scalarLaplacian_component
#print axioms NSEGR.Assembly.scalarLaplacian_component
#check @NSEGR.Assembly.scalarLaplacian_neg
#print axioms NSEGR.Assembly.scalarLaplacian_neg
#check @NSEGR.Assembly.scalarLaplacian_poissonInverse
#print axioms NSEGR.Assembly.scalarLaplacian_poissonInverse
#check @NSEGR.Assembly.scalarMean_poissonInverse_zero
#print axioms NSEGR.Assembly.scalarMean_poissonInverse_zero
#check @NSEGR.Assembly.scalarPartial_scalarL_commute
#print axioms NSEGR.Assembly.scalarPartial_scalarL_commute
#check @NSEGR.Assembly.scalarPartial_poissonInverse_commute
#print axioms NSEGR.Assembly.scalarPartial_poissonInverse_commute
#check @NSEGR.Assembly.poissonInverse_finset_sum
#print axioms NSEGR.Assembly.poissonInverse_finset_sum
#check @NSEGR.Assembly.scalarLaplacian_poissonInverse_commute
#print axioms NSEGR.Assembly.scalarLaplacian_poissonInverse_commute
#check @NSEGR.Assembly.poissonInverse_scalarLaplacian
#print axioms NSEGR.Assembly.poissonInverse_scalarLaplacian
#check @NSEGR.Assembly.leray_gradient_zero
#print axioms NSEGR.Assembly.leray_gradient_zero
#check @NSEGR.Assembly.divergence_smooth
#print axioms NSEGR.Assembly.divergence_smooth
#check @NSEGR.Assembly.divergence_sub
#print axioms NSEGR.Assembly.divergence_sub
#check @NSEGR.Assembly.leray_smooth
#print axioms NSEGR.Assembly.leray_smooth
#check @NSEGR.Assembly.divergence_leray_zero
#print axioms NSEGR.Assembly.divergence_leray_zero
#check @NSEGR.Assembly.leray_eq_self_of_divergence_zero
#print axioms NSEGR.Assembly.leray_eq_self_of_divergence_zero
#check @NSEGR.Assembly.leray_idempotent
#print axioms NSEGR.Assembly.leray_idempotent
#check @NSEGR.Assembly.spatialMean_leray
#print axioms NSEGR.Assembly.spatialMean_leray
#check @NSEGR.Assembly.positive_matrix_gram_factor
#print axioms NSEGR.Assembly.positive_matrix_gram_factor
#check @NSEGR.Assembly.lorentzSchur
#print axioms NSEGR.Assembly.lorentzSchur
#check @NSEGR.Assembly.lorentzSchur_posDef
#print axioms NSEGR.Assembly.lorentzSchur_posDef
#check @NSEGR.Assembly.lorentzTriangular
#print axioms NSEGR.Assembly.lorentzTriangular
#check @NSEGR.Assembly.lorentzTriangular_00
#print axioms NSEGR.Assembly.lorentzTriangular_00
#check @NSEGR.Assembly.lorentzTriangular_0j
#print axioms NSEGR.Assembly.lorentzTriangular_0j
#check @NSEGR.Assembly.lorentzTriangular_i0
#print axioms NSEGR.Assembly.lorentzTriangular_i0
#check @NSEGR.Assembly.lorentzTriangular_ij
#print axioms NSEGR.Assembly.lorentzTriangular_ij
#check @NSEGR.Assembly.lorentzTriangular_det
#print axioms NSEGR.Assembly.lorentzTriangular_det
#check @NSEGR.Assembly.eta4_congruence_apply
#print axioms NSEGR.Assembly.eta4_congruence_apply
#check @NSEGR.Assembly.lorentzTriangular_congruence
#print axioms NSEGR.Assembly.lorentzTriangular_congruence
#check @NSEGR.Assembly.lorentz_factor_of_spatial_posDef
#print axioms NSEGR.Assembly.lorentz_factor_of_spatial_posDef
#check @NSEGR.Assembly.gaussian_lorentzian_of_spatial_posDef
#print axioms NSEGR.Assembly.gaussian_lorentzian_of_spatial_posDef
#check @NSEGR.Assembly.small_entry_quadratic_bound
#print axioms NSEGR.Assembly.small_entry_quadratic_bound
#check @NSEGR.Assembly.spatial_quadratic_error_bound
#print axioms NSEGR.Assembly.spatial_quadratic_error_bound
#check @NSEGR.Assembly.spatial_posDef_of_near_identity
#print axioms NSEGR.Assembly.spatial_posDef_of_near_identity
#check @NSEGR.Assembly.lorentz_factor_of_near_eta4
#print axioms NSEGR.Assembly.lorentz_factor_of_near_eta4
#check @NSEGR.Assembly.gaussian_lorentzian_of_near_eta4
#print axioms NSEGR.Assembly.gaussian_lorentzian_of_near_eta4
#check @NSEGR.Assembly.finite_precompact_refinement
#print axioms NSEGR.Assembly.finite_precompact_refinement
#check @NSEGR.Assembly.finite_compact_overlap_uniform
#print axioms NSEGR.Assembly.finite_compact_overlap_uniform
#check @NSEGR.Assembly.overlapGlue
#print axioms NSEGR.Assembly.overlapGlue
#check @NSEGR.Assembly.overlapGlue_eq
#print axioms NSEGR.Assembly.overlapGlue_eq
#check @NSEGR.Assembly.overlapGlue_eventuallyEq
#print axioms NSEGR.Assembly.overlapGlue_eventuallyEq
#check @NSEGR.Assembly.overlapGlue_analyticAt
#print axioms NSEGR.Assembly.overlapGlue_analyticAt
#check @NSEGR.Assembly.overlapGlue_fderiv
#print axioms NSEGR.Assembly.overlapGlue_fderiv
#check @NSEGR.Assembly.overlapGlue_fderiv_eventuallyEq
#print axioms NSEGR.Assembly.overlapGlue_fderiv_eventuallyEq
#check @NSEGR.Assembly.integerSpatialShift_add
#print axioms NSEGR.Assembly.integerSpatialShift_add
#check @NSEGR.Assembly.integerSpatialShift_sub
#print axioms NSEGR.Assembly.integerSpatialShift_sub
#check @NSEGR.Assembly.integerSpatialShift_single
#print axioms NSEGR.Assembly.integerSpatialShift_single
#check @NSEGR.Assembly.latticePatch
#print axioms NSEGR.Assembly.latticePatch
#check @NSEGR.Assembly.latticeLocal
#print axioms NSEGR.Assembly.latticeLocal
#check @NSEGR.Assembly.latticePatch_isOpen
#print axioms NSEGR.Assembly.latticePatch_isOpen
#check @NSEGR.Assembly.latticePatch_cover
#print axioms NSEGR.Assembly.latticePatch_cover
#check @NSEGR.Assembly.boundedShiftVector
#print axioms NSEGR.Assembly.boundedShiftVector
#check @NSEGR.Assembly.lattice_relative_shift_bound
#print axioms NSEGR.Assembly.lattice_relative_shift_bound
#check @NSEGR.Assembly.compactLatticeOverlap
#print axioms NSEGR.Assembly.compactLatticeOverlap
#check @NSEGR.Assembly.compactLatticeOverlap_isCompact
#print axioms NSEGR.Assembly.compactLatticeOverlap_isCompact
#check @NSEGR.Assembly.lattice_overlap_germs_uniform
#print axioms NSEGR.Assembly.lattice_overlap_germs_uniform
#check @NSEGR.Assembly.periodic_witness_of_compatible_atlas
#print axioms NSEGR.Assembly.periodic_witness_of_compatible_atlas
#check @NSEGR.Assembly.periodic_witness_of_compact_overlap_germs
#print axioms NSEGR.Assembly.periodic_witness_of_compact_overlap_germs
#check @NSEGR.Assembly.analyticAt_of_lattice_local_germ
#print axioms NSEGR.Assembly.analyticAt_of_lattice_local_germ
#check @NSEGR.Assembly.germ_local_law_of_lattice_local_germ
#print axioms NSEGR.Assembly.germ_local_law_of_lattice_local_germ
#check @NSEGR.Assembly.periodic_analytic_witness_of_compact_overlap_germs
#print axioms NSEGR.Assembly.periodic_analytic_witness_of_compact_overlap_germs
#check @NSEGR.Assembly.scalarHessian_sub_constant
#print axioms NSEGR.Assembly.scalarHessian_sub_constant
#check @NSEGR.Assembly.scalarLaplacian_sub_constant
#print axioms NSEGR.Assembly.scalarLaplacian_sub_constant
#check @NSEGR.Assembly.analytic_second_deriv_sub
#print axioms NSEGR.Assembly.analytic_second_deriv_sub
#check @NSEGR.Assembly.scalarLocalTimeDerivative_gauge_germ
#print axioms NSEGR.Assembly.scalarLocalTimeDerivative_gauge_germ
#check @NSEGR.Assembly.gradient_scalarLocalTimeDerivative_gauge
#print axioms NSEGR.Assembly.gradient_scalarLocalTimeDerivative_gauge
#check @NSEGR.Assembly.scalarSecondTimeDerivative_gauge
#print axioms NSEGR.Assembly.scalarSecondTimeDerivative_gauge
#check @NSEGR.Assembly.source_plus_completion_pressure_gauge
#print axioms NSEGR.Assembly.source_plus_completion_pressure_gauge
#check @NSEGR.Assembly.completedBoundary_pressure_gauge
#print axioms NSEGR.Assembly.completedBoundary_pressure_gauge
#check @NSEGR.Assembly.normalized_pressure_gauge_completion
#print axioms NSEGR.Assembly.normalized_pressure_gauge_completion
#check @NSEGR.Assembly.nseSpatialSource3_trace
#print axioms NSEGR.Assembly.nseSpatialSource3_trace
#check @NSEGR.Assembly.completedBoundary_lower_trace
#print axioms NSEGR.Assembly.completedBoundary_lower_trace
#check @NSEGR.Assembly.completedBoundary_time_time
#print axioms NSEGR.Assembly.completedBoundary_time_time
#check @NSEGR.Assembly.completedBoundary_time_space
#print axioms NSEGR.Assembly.completedBoundary_time_space
#check @NSEGR.Assembly.completedBoundary_space_space
#print axioms NSEGR.Assembly.completedBoundary_space_space
#check @NSEGR.Assembly.completedBoundary_rawVelocity
#print axioms NSEGR.Assembly.completedBoundary_rawVelocity
#check @NSEGR.Assembly.completedBoundary_beta
#print axioms NSEGR.Assembly.completedBoundary_beta
#check @NSEGR.Assembly.nseSpatialSource3_divergence
#print axioms NSEGR.Assembly.nseSpatialSource3_divergence
#check @NSEGR.Assembly.upperDivergence
#print axioms NSEGR.Assembly.upperDivergence
#check @NSEGR.Assembly.velocity_coordinate_timeDerivative
#print axioms NSEGR.Assembly.velocity_coordinate_timeDerivative
#check @NSEGR.Assembly.nseSpatialSource3_symmetric
#print axioms NSEGR.Assembly.nseSpatialSource3_symmetric
#check @NSEGR.Assembly.conservedSourceUpper_divergence_time
#print axioms NSEGR.Assembly.conservedSourceUpper_divergence_time
#check @NSEGR.Assembly.conservedSourceUpper_divergence_space
#print axioms NSEGR.Assembly.conservedSourceUpper_divergence_space
#check @NSEGR.Assembly.conservedSourceUpper_conserved
#print axioms NSEGR.Assembly.conservedSourceUpper_conserved
#check @NSEGR.Assembly.scalar_local_assembly
#print axioms NSEGR.Assembly.scalar_local_assembly
#check @NSEGR.Assembly.jointTime
#print axioms NSEGR.Assembly.jointTime
#check @NSEGR.Assembly.jointSpace
#print axioms NSEGR.Assembly.jointSpace
#check @NSEGR.Assembly.jointTime_congr
#print axioms NSEGR.Assembly.jointTime_congr
#check @NSEGR.Assembly.jointSpace_congr
#print axioms NSEGR.Assembly.jointSpace_congr
#check @NSEGR.Assembly.jointTime_congr_germ
#print axioms NSEGR.Assembly.jointTime_congr_germ
#check @NSEGR.Assembly.jointSpace_congr_germ
#print axioms NSEGR.Assembly.jointSpace_congr_germ
#check @NSEGR.Assembly.analyticAt_jointTime
#print axioms NSEGR.Assembly.analyticAt_jointTime
#check @NSEGR.Assembly.analyticAt_jointSpace
#print axioms NSEGR.Assembly.analyticAt_jointSpace
#check @NSEGR.Assembly.jointTime_jointSpace
#print axioms NSEGR.Assembly.jointTime_jointSpace
#check @NSEGR.Assembly.scalarCKPotential
#print axioms NSEGR.Assembly.scalarCKPotential
#check @NSEGR.Assembly.scalarCK_coordinate_timeDerivative
#print axioms NSEGR.Assembly.scalarCK_coordinate_timeDerivative
#check @NSEGR.Assembly.scalarCK_coordinate_spaceDerivative
#print axioms NSEGR.Assembly.scalarCK_coordinate_spaceDerivative
#check @NSEGR.Assembly.scalarCK_potential_time_germ
#print axioms NSEGR.Assembly.scalarCK_potential_time_germ
#check @NSEGR.Assembly.scalarCK_potential_initial
#print axioms NSEGR.Assembly.scalarCK_potential_initial
#check @NSEGR.Assembly.scalarCK_potential_time_initial
#print axioms NSEGR.Assembly.scalarCK_potential_time_initial
#check @NSEGR.Assembly.scalarCK_secondOrder_equation
#print axioms NSEGR.Assembly.scalarCK_secondOrder_equation
#check @NSEGR.Assembly.scalarCK_scalarNormalGerm
#print axioms NSEGR.Assembly.scalarCK_scalarNormalGerm
#check @NSEGR.Assembly.scalarStateOfPotential
#print axioms NSEGR.Assembly.scalarStateOfPotential
#check @NSEGR.Assembly.analyticAt_scalarStateOfPotential
#print axioms NSEGR.Assembly.analyticAt_scalarStateOfPotential
#check @NSEGR.Assembly.scalarStateOfPotential_solution
#print axioms NSEGR.Assembly.scalarStateOfPotential_solution
#check @NSEGR.Assembly.scalar_normalized_germ_unique
#print axioms NSEGR.Assembly.scalar_normalized_germ_unique
#check @NSEGR.Assembly.scalarNormalGerm_exists
#print axioms NSEGR.Assembly.scalarNormalGerm_exists
#check @NSEGR.Assembly.scalarHessian_eq_zero_of_germ_zero
#print axioms NSEGR.Assembly.scalarHessian_eq_zero_of_germ_zero
#check @NSEGR.Assembly.scalarLaplacian_eq_zero_of_germ_zero
#print axioms NSEGR.Assembly.scalarLaplacian_eq_zero_of_germ_zero
#check @NSEGR.Assembly.analyticAt_scalarLaplacian_joint
#print axioms NSEGR.Assembly.analyticAt_scalarLaplacian_joint
#check @NSEGR.Assembly.ScalarNormalGerm.noncharacteristic
#print axioms NSEGR.Assembly.ScalarNormalGerm.noncharacteristic
#check @NSEGR.Assembly.ScalarNormalGerm.hamiltonian
#print axioms NSEGR.Assembly.ScalarNormalGerm.hamiltonian
#check @NSEGR.Assembly.analyticHodge_scalarSpatialPartial_joint
#print axioms NSEGR.Assembly.analyticHodge_scalarSpatialPartial_joint
#check @NSEGR.Assembly.analyticHodge_gradient_joint
#print axioms NSEGR.Assembly.analyticHodge_gradient_joint
#check @NSEGR.Assembly.analyticHodge_divergence_joint
#print axioms NSEGR.Assembly.analyticHodge_divergence_joint
#check @NSEGR.Assembly.analyticHodge_scalarLaplacian_joint
#print axioms NSEGR.Assembly.analyticHodge_scalarLaplacian_joint
#check @NSEGR.Assembly.scalarMean_analytic_of_poissonInverse_analytic
#print axioms NSEGR.Assembly.scalarMean_analytic_of_poissonInverse_analytic
#check @NSEGR.Assembly.analyticShiftMajorant
#print axioms NSEGR.Assembly.analyticShiftMajorant
#check @NSEGR.Assembly.analyticShiftMajorant_summable
#print axioms NSEGR.Assembly.analyticShiftMajorant_summable
#check @NSEGR.Assembly.changeOrigin_uniform_coefficient_bound
#print axioms NSEGR.Assembly.changeOrigin_uniform_coefficient_bound
#check @NSEGR.Assembly.analyticHodge_norm_iteratedFDeriv_le_factorial
#print axioms NSEGR.Assembly.analyticHodge_norm_iteratedFDeriv_le_factorial
#check @NSEGR.Assembly.analyticAt_exists_uniform_iteratedFDeriv_bound
#print axioms NSEGR.Assembly.analyticAt_exists_uniform_iteratedFDeriv_bound
#check @NSEGR.Assembly.analyticOnNhd_compact_uniform_iteratedFDeriv_bound
#print axioms NSEGR.Assembly.analyticOnNhd_compact_uniform_iteratedFDeriv_bound
#check @NSEGR.Assembly.analyticHodge_factorial_shift_bound
#print axioms NSEGR.Assembly.analyticHodge_factorial_shift_bound
#check @NSEGR.Assembly.analyticHodge_absorb_fixed_loss
#print axioms NSEGR.Assembly.analyticHodge_absorb_fixed_loss
#check @NSEGR.Assembly.analyticHodge_order_monotone
#print axioms NSEGR.Assembly.analyticHodge_order_monotone
#check @NSEGR.Assembly.analyticHodge_open_slab_local_uniform_bound
#print axioms NSEGR.Assembly.analyticHodge_open_slab_local_uniform_bound
#check @NSEGR.Assembly.factorialTaylor_remainder_bound
#print axioms NSEGR.Assembly.factorialTaylor_remainder_bound
#check @NSEGR.Assembly.analyticAt_of_iteratedFDeriv_bound
#print axioms NSEGR.Assembly.analyticAt_of_iteratedFDeriv_bound
#check @NSEGR.Assembly.poissonInverse_joint_smooth_global
#print axioms NSEGR.Assembly.poissonInverse_joint_smooth_global
#check @NSEGR.Assembly.poissonInverse_joint_smooth_on_open_slab
#print axioms NSEGR.Assembly.poissonInverse_joint_smooth_on_open_slab
#check @NSEGR.Assembly.scalarSpatialIterate
#print axioms NSEGR.Assembly.scalarSpatialIterate
#check @NSEGR.Assembly.scalarSpatialIterate_smooth
#print axioms NSEGR.Assembly.scalarSpatialIterate_smooth
#check @NSEGR.Assembly.scalarSpatialIterate_periodic
#print axioms NSEGR.Assembly.scalarSpatialIterate_periodic
#check @NSEGR.Assembly.scalarLift_scalarSpatialIterate
#print axioms NSEGR.Assembly.scalarLift_scalarSpatialIterate
#check @NSEGR.Assembly.scalar_integral_norm_le
#print axioms NSEGR.Assembly.scalar_integral_norm_le
#check @NSEGR.Assembly.scalar_fourierDecayConstant_eight_le
#print axioms NSEGR.Assembly.scalar_fourierDecayConstant_eight_le
#check @NSEGR.Assembly.scalarCoeff_norm_le_eight
#print axioms NSEGR.Assembly.scalarCoeff_norm_le_eight
#check @NSEGR.Assembly.poissonInverseFixedLossConstant
#print axioms NSEGR.Assembly.poissonInverseFixedLossConstant
#check @NSEGR.Assembly.poissonInverseFixedLossConstant_pos
#print axioms NSEGR.Assembly.poissonInverseFixedLossConstant_pos
#check @NSEGR.Assembly.poissonInverse_norm_le_eight
#print axioms NSEGR.Assembly.poissonInverse_norm_le_eight
#check @NSEGR.Assembly.poissonInverse_const_mul
#print axioms NSEGR.Assembly.poissonInverse_const_mul
#check @NSEGR.Assembly.poissonInverse_add
#print axioms NSEGR.Assembly.poissonInverse_add
#check @NSEGR.Assembly.jointLinear_coordinate_expansion
#print axioms NSEGR.Assembly.jointLinear_coordinate_expansion
#check @NSEGR.Assembly.joint_fderiv_time
#print axioms NSEGR.Assembly.joint_fderiv_time
#check @NSEGR.Assembly.joint_fderiv_space
#print axioms NSEGR.Assembly.joint_fderiv_space
#check @NSEGR.Assembly.joint_fderiv_smooth
#print axioms NSEGR.Assembly.joint_fderiv_smooth
#check @NSEGR.Assembly.joint_fderiv_periodic
#print axioms NSEGR.Assembly.joint_fderiv_periodic
#check @NSEGR.Assembly.poissonInverse_fderiv_commute_global
#print axioms NSEGR.Assembly.poissonInverse_fderiv_commute_global
#check @NSEGR.Assembly.iteratedFDeriv_apply_smooth_global
#print axioms NSEGR.Assembly.iteratedFDeriv_apply_smooth_global
#check @NSEGR.Assembly.iteratedFDeriv_slice_periodic_global
#print axioms NSEGR.Assembly.iteratedFDeriv_slice_periodic_global
#check @NSEGR.Assembly.poissonInverse_iteratedFDeriv_commute_global
#print axioms NSEGR.Assembly.poissonInverse_iteratedFDeriv_commute_global
#check @NSEGR.Assembly.fullSlice_iteratedFDeriv_eq
#print axioms NSEGR.Assembly.fullSlice_iteratedFDeriv_eq
#check @NSEGR.Assembly.iteratedFDeriv_slice_smooth_periodic
#print axioms NSEGR.Assembly.iteratedFDeriv_slice_smooth_periodic
#check @NSEGR.Assembly.poissonInverse_iteratedFDeriv_commute
#print axioms NSEGR.Assembly.poissonInverse_iteratedFDeriv_commute
#check @NSEGR.Assembly.prependSpatialDirections
#print axioms NSEGR.Assembly.prependSpatialDirections
#check @NSEGR.Assembly.scalarSpatialIterate_iteratedFDeriv_global
#print axioms NSEGR.Assembly.scalarSpatialIterate_iteratedFDeriv_global
#check @NSEGR.Assembly.prependSpatialDirections_norm_prod
#print axioms NSEGR.Assembly.prependSpatialDirections_norm_prod
#check @NSEGR.Assembly.scalarSpatialIterate_iteratedFDeriv
#print axioms NSEGR.Assembly.scalarSpatialIterate_iteratedFDeriv
#check @NSEGR.Assembly.poissonInverse_iteratedFDeriv_bound_eight
#print axioms NSEGR.Assembly.poissonInverse_iteratedFDeriv_bound_eight
#check @NSEGR.Assembly.poissonInverse_joint_analytic_on_open_slab
#print axioms NSEGR.Assembly.poissonInverse_joint_analytic_on_open_slab
#check @NSEGR.Assembly.scalarMean_analytic_on_open_slab
#print axioms NSEGR.Assembly.scalarMean_analytic_on_open_slab
#check @NSEGR.Assembly.leray_joint_analytic_on_open_slab
#print axioms NSEGR.Assembly.leray_joint_analytic_on_open_slab
#check @NSEGR.Assembly.matrixEntryCLM
#print axioms NSEGR.Assembly.matrixEntryCLM
#check @NSEGR.Assembly.analyticAt_matrix_entry
#print axioms NSEGR.Assembly.analyticAt_matrix_entry
#check @NSEGR.Assembly.analyticAt_matrix_of_entries
#print axioms NSEGR.Assembly.analyticAt_matrix_of_entries
#check @NSEGR.Assembly.matrix_entry_fderiv
#print axioms NSEGR.Assembly.matrix_entry_fderiv
#check @NSEGR.Assembly.boundaryEmbed
#print axioms NSEGR.Assembly.boundaryEmbed
#check @NSEGR.Assembly.boundaryEmbed_coe
#print axioms NSEGR.Assembly.boundaryEmbed_coe
#check @NSEGR.Assembly.boundaryEmbed_time
#print axioms NSEGR.Assembly.boundaryEmbed_time
#check @NSEGR.Assembly.boundaryEmbed_space
#print axioms NSEGR.Assembly.boundaryEmbed_space
#check @NSEGR.Assembly.analyticAt_bulkPartial
#print axioms NSEGR.Assembly.analyticAt_bulkPartial
#check @NSEGR.Assembly.boundaryPartial_restrict
#print axioms NSEGR.Assembly.boundaryPartial_restrict
#check @NSEGR.Assembly.boundaryPartial_congr
#print axioms NSEGR.Assembly.boundaryPartial_congr
#check @NSEGR.Assembly.bulkPartial_tangent_zero
#print axioms NSEGR.Assembly.bulkPartial_tangent_zero
#check @NSEGR.Assembly.bulkPartial_radial_restrict
#print axioms NSEGR.Assembly.bulkPartial_radial_restrict
#check @NSEGR.Assembly.analyticAt_matrix_inverse
#print axioms NSEGR.Assembly.analyticAt_matrix_inverse
#check @NSEGR.Assembly.bulkPartial_inverse
#print axioms NSEGR.Assembly.bulkPartial_inverse
#check @NSEGR.Assembly.analyticAt_gaussianSecondForm
#print axioms NSEGR.Assembly.analyticAt_gaussianSecondForm
#check @NSEGR.Assembly.analyticAt_gaussianShape
#print axioms NSEGR.Assembly.analyticAt_gaussianShape
#check @NSEGR.Assembly.analyticAt_gaussianTangentialChristoffel
#print axioms NSEGR.Assembly.analyticAt_gaussianTangentialChristoffel
#check @NSEGR.Assembly.gaussianShape_at_flat
#print axioms NSEGR.Assembly.gaussianShape_at_flat
#check @NSEGR.Assembly.bulkPartial_inverse_at_flat
#print axioms NSEGR.Assembly.bulkPartial_inverse_at_flat
#check @NSEGR.Assembly.bulkPartial_mul
#print axioms NSEGR.Assembly.bulkPartial_mul
#check @NSEGR.Assembly.bulkPartial_sum
#print axioms NSEGR.Assembly.bulkPartial_sum
#check @NSEGR.Assembly.bulkPartial_shape_at_flat
#print axioms NSEGR.Assembly.bulkPartial_shape_at_flat
#check @NSEGR.Assembly.gaussian_normal_flat
#print axioms NSEGR.Assembly.gaussian_normal_flat
#check @NSEGR.Assembly.gaussian_tangential_flat
#print axioms NSEGR.Assembly.gaussian_tangential_flat
#check @NSEGR.Assembly.gaussian_hamiltonian_flat
#print axioms NSEGR.Assembly.gaussian_hamiltonian_flat
#check @NSEGR.Assembly.boundaryDirection
#print axioms NSEGR.Assembly.boundaryDirection
#check @NSEGR.Assembly.boundaryPartial_eq_joint
#print axioms NSEGR.Assembly.boundaryPartial_eq_joint
#check @NSEGR.Assembly.boundaryPartial_sub
#print axioms NSEGR.Assembly.boundaryPartial_sub
#check @NSEGR.Assembly.boundaryPartial_const_mul
#print axioms NSEGR.Assembly.boundaryPartial_const_mul
#check @NSEGR.Assembly.boundaryPartial_sum
#print axioms NSEGR.Assembly.boundaryPartial_sum
#check @NSEGR.Assembly.lorentzTrace4_eq_sum
#print axioms NSEGR.Assembly.lorentzTrace4_eq_sum
#check @NSEGR.Assembly.analyticAt_boundaryTrace
#print axioms NSEGR.Assembly.analyticAt_boundaryTrace
#check @NSEGR.Assembly.boundaryCodazzi_expanded
#print axioms NSEGR.Assembly.boundaryCodazzi_expanded
#check @NSEGR.Assembly.metricTangentialBlock
#print axioms NSEGR.Assembly.metricTangentialBlock
#check @NSEGR.Assembly.bulkCollar_isOpen
#print axioms NSEGR.Assembly.bulkCollar_isOpen
#check @NSEGR.Assembly.boundaryPoint_mem_collar
#print axioms NSEGR.Assembly.boundaryPoint_mem_collar
#check @NSEGR.Assembly.boundary_time_eventually
#print axioms NSEGR.Assembly.boundary_time_eventually
#check @NSEGR.Assembly.gaussianVacuum_block_analytic
#print axioms NSEGR.Assembly.gaussianVacuum_block_analytic
#check @NSEGR.Assembly.gaussianVacuum_eq_gaussian
#print axioms NSEGR.Assembly.gaussianVacuum_eq_gaussian
#check @NSEGR.Assembly.gaussianVacuum_eq_gaussian_germ
#print axioms NSEGR.Assembly.gaussianVacuum_eq_gaussian_germ
#check @NSEGR.Assembly.gaussianVacuum_block_unit
#print axioms NSEGR.Assembly.gaussianVacuum_block_unit
#check @NSEGR.Assembly.gaussianVacuum_block_unit_germ
#print axioms NSEGR.Assembly.gaussianVacuum_block_unit_germ
#check @NSEGR.Assembly.christoffel_congr_germ
#print axioms NSEGR.Assembly.christoffel_congr_germ
#check @NSEGR.Assembly.ricci_congr_germ
#print axioms NSEGR.Assembly.ricci_congr_germ
#check @NSEGR.Assembly.gaussianVacuum_block_vacuum
#print axioms NSEGR.Assembly.gaussianVacuum_block_vacuum
#check @NSEGR.Assembly.boundaryK_eq_block
#print axioms NSEGR.Assembly.boundaryK_eq_block
#check @NSEGR.Assembly.gaussianVacuum_boundary_analytic
#print axioms NSEGR.Assembly.gaussianVacuum_boundary_analytic
#check @NSEGR.Assembly.gaussianVacuum_boundary_symmetric
#print axioms NSEGR.Assembly.gaussianVacuum_boundary_symmetric
#check @NSEGR.Assembly.gaussianVacuum_boundary_periodic
#print axioms NSEGR.Assembly.gaussianVacuum_boundary_periodic
#check @NSEGR.Assembly.gaussianVacuum_block_flat
#print axioms NSEGR.Assembly.gaussianVacuum_block_flat
#check @NSEGR.Assembly.gaussianVacuum_block_tangent_zero
#print axioms NSEGR.Assembly.gaussianVacuum_block_tangent_zero
#check @NSEGR.Assembly.gaussianVacuum_connection_zero
#print axioms NSEGR.Assembly.gaussianVacuum_connection_zero
#check @NSEGR.Assembly.gaussianVacuum_connection_tangent_zero
#print axioms NSEGR.Assembly.gaussianVacuum_connection_tangent_zero
#check @NSEGR.Assembly.gaussianVacuum_boundary_hamiltonian
#print axioms NSEGR.Assembly.gaussianVacuum_boundary_hamiltonian
#check @NSEGR.Assembly.gaussianVacuum_shape_tangent
#print axioms NSEGR.Assembly.gaussianVacuum_shape_tangent
#check @NSEGR.Assembly.gaussianVacuum_boundary_codazzi
#print axioms NSEGR.Assembly.gaussianVacuum_boundary_codazzi
#check @NSEGR.Assembly.gaussianVacuum_boundaryAdmissible
#print axioms NSEGR.Assembly.gaussianVacuum_boundaryAdmissible
#check @NSEGR.Assembly.tensor4Entry
#print axioms NSEGR.Assembly.tensor4Entry
#check @NSEGR.Assembly.analyticAt_tensor4_entry
#print axioms NSEGR.Assembly.analyticAt_tensor4_entry
#check @NSEGR.Assembly.analyticAt_tensor4_of_entries
#print axioms NSEGR.Assembly.analyticAt_tensor4_of_entries
#check @NSEGR.Assembly.analyticAt_vec_of_components
#print axioms NSEGR.Assembly.analyticAt_vec_of_components
#check @NSEGR.Assembly.analyticOnNhd_slab_contDiffOn
#print axioms NSEGR.Assembly.analyticOnNhd_slab_contDiffOn
#check @NSEGR.Assembly.analyticOnNhd_slab_slice_smooth
#print axioms NSEGR.Assembly.analyticOnNhd_slab_slice_smooth
#check @NSEGR.Assembly.jointSpace_jointSpace
#print axioms NSEGR.Assembly.jointSpace_jointSpace
#check @NSEGR.Assembly.jointTime_sum
#print axioms NSEGR.Assembly.jointTime_sum
#check @NSEGR.Assembly.jointSpace_sum
#print axioms NSEGR.Assembly.jointSpace_sum
#check @NSEGR.Assembly.jointTime_add
#print axioms NSEGR.Assembly.jointTime_add
#check @NSEGR.Assembly.jointSpace_add
#print axioms NSEGR.Assembly.jointSpace_add
#check @NSEGR.Assembly.jointSpace_sub
#print axioms NSEGR.Assembly.jointSpace_sub
#check @NSEGR.Assembly.analyticAt_gradient_joint
#print axioms NSEGR.Assembly.analyticAt_gradient_joint
#check @NSEGR.Assembly.analyticAt_boundaryBeta
#print axioms NSEGR.Assembly.analyticAt_boundaryBeta
#check @NSEGR.Assembly.analyticAt_boundaryRawVelocity
#print axioms NSEGR.Assembly.analyticAt_boundaryRawVelocity
#check @NSEGR.Assembly.scalar_time_laplacian_commute
#print axioms NSEGR.Assembly.scalar_time_laplacian_commute
#check @NSEGR.Assembly.scalar_time_gradient_commute
#print axioms NSEGR.Assembly.scalar_time_gradient_commute
#check @NSEGR.Assembly.scalarMean_sub_const_native
#print axioms NSEGR.Assembly.scalarMean_sub_const_native
#check @NSEGR.Assembly.poissonInverse_neg_native
#print axioms NSEGR.Assembly.poissonInverse_neg_native
#check @NSEGR.Assembly.jointSpace_isotropic_sum
#print axioms NSEGR.Assembly.jointSpace_isotropic_sum
#check @NSEGR.Assembly.jointSpace_hessian_divergence
#print axioms NSEGR.Assembly.jointSpace_hessian_divergence
#check @NSEGR.Assembly.scalarCompletionUpper_conserved
#print axioms NSEGR.Assembly.scalarCompletionUpper_conserved
#check @NSEGR.Assembly.analyticAt_conservedSourceUpper_entry
#print axioms NSEGR.Assembly.analyticAt_conservedSourceUpper_entry
#check @NSEGR.Assembly.analyticAt_scalarCompletionUpper_entry
#print axioms NSEGR.Assembly.analyticAt_scalarCompletionUpper_entry
#check @NSEGR.Assembly.analyticAt_completedBoundary
#print axioms NSEGR.Assembly.analyticAt_completedBoundary
#check @NSEGR.Assembly.boundaryPartial_add_native
#print axioms NSEGR.Assembly.boundaryPartial_add_native
#check @NSEGR.Assembly.boundaryPartial_const_mul_native
#print axioms NSEGR.Assembly.boundaryPartial_const_mul_native
#check @NSEGR.Assembly.traceReverse_lower_codazzi
#print axioms NSEGR.Assembly.traceReverse_lower_codazzi
#check @NSEGR.Assembly.completedBoundary_codazzi
#print axioms NSEGR.Assembly.completedBoundary_codazzi
#check @NSEGR.Assembly.completedBoundary_symmetric
#print axioms NSEGR.Assembly.completedBoundary_symmetric
#check @NSEGR.Assembly.scalarLocalTimeDerivative_periodic_on_interval
#print axioms NSEGR.Assembly.scalarLocalTimeDerivative_periodic_on_interval
#check @NSEGR.Assembly.scalarHessian_periodic_native
#print axioms NSEGR.Assembly.scalarHessian_periodic_native
#check @NSEGR.Assembly.completedBoundary_periodic
#print axioms NSEGR.Assembly.completedBoundary_periodic
#check @NSEGR.Assembly.completedBoundary_admissible
#print axioms NSEGR.Assembly.completedBoundary_admissible
#check @NSEGR.Assembly.spatialTranslate
#print axioms NSEGR.Assembly.spatialTranslate
#check @NSEGR.Assembly.gluingSpatialBox
#print axioms NSEGR.Assembly.gluingSpatialBox
#check @NSEGR.Assembly.gluingSpatialBox_isOpen
#print axioms NSEGR.Assembly.gluingSpatialBox_isOpen
#check @NSEGR.Assembly.unitCube_subset_gluingSpatialBox
#print axioms NSEGR.Assembly.unitCube_subset_gluingSpatialBox
#check @NSEGR.Assembly.periodic_law_of_unique_local_germs
#print axioms NSEGR.Assembly.periodic_law_of_unique_local_germs
#check @NSEGR.Assembly.positive_timeInterval_subset
#print axioms NSEGR.Assembly.positive_timeInterval_subset
#check @NSEGR.Assembly.spatialPeriodic_sub_integer
#print axioms NSEGR.Assembly.spatialPeriodic_sub_integer
#check @NSEGR.Assembly.fderiv_spatialPeriodic_sub_integer
#print axioms NSEGR.Assembly.fderiv_spatialPeriodic_sub_integer
#check @NSEGR.Assembly.scalarCompletionUpper_spatial_sub
#print axioms NSEGR.Assembly.scalarCompletionUpper_spatial_sub
#check @NSEGR.Assembly.conservedSourceUpper_periodic_sub
#print axioms NSEGR.Assembly.conservedSourceUpper_periodic_sub
#check @NSEGR.Assembly.completedBoundary_spatial_sub
#print axioms NSEGR.Assembly.completedBoundary_spatial_sub
#check @NSEGR.Assembly.scalarCompletionUpper_joint_congr
#print axioms NSEGR.Assembly.scalarCompletionUpper_joint_congr
#check @NSEGR.Assembly.completedBoundary_joint_congr
#print axioms NSEGR.Assembly.completedBoundary_joint_congr
#check @NSEGR.Assembly.boundaryHamiltonian_joint_congr
#print axioms NSEGR.Assembly.boundaryHamiltonian_joint_congr
#check @NSEGR.Assembly.bulkPartial_comp_sub
#print axioms NSEGR.Assembly.bulkPartial_comp_sub
#check @NSEGR.Assembly.christoffel_comp_sub
#print axioms NSEGR.Assembly.christoffel_comp_sub
#check @NSEGR.Assembly.ricci_comp_sub
#print axioms NSEGR.Assembly.ricci_comp_sub
#check @NSEGR.Assembly.bulkPoint_sub_spatial
#print axioms NSEGR.Assembly.bulkPoint_sub_spatial
#check @NSEGR.Assembly.boundaryK_comp_spatial_sub
#print axioms NSEGR.Assembly.boundaryK_comp_spatial_sub
#check @NSEGR.Assembly.scalarNormalGerm_of_hamiltonian_nativeGluing
#print axioms NSEGR.Assembly.scalarNormalGerm_of_hamiltonian_nativeGluing
#check @NSEGR.Assembly.ScalarGluingLaw
#print axioms NSEGR.Assembly.ScalarGluingLaw
#check @NSEGR.Assembly.ScalarGluingLaw.congr
#print axioms NSEGR.Assembly.ScalarGluingLaw.congr
#check @NSEGR.Assembly.ScalarGluingLaw.translate
#print axioms NSEGR.Assembly.ScalarGluingLaw.translate
#check @NSEGR.Assembly.scalarGluingLaw_germ_of_normal
#print axioms NSEGR.Assembly.scalarGluingLaw_germ_of_normal
#check @NSEGR.Assembly.scalarNormalGerm_of_gluingLaw
#print axioms NSEGR.Assembly.scalarNormalGerm_of_gluingLaw
#check @NSEGR.Assembly.scalar_periodic_cylinder_of_literatureCK
#print axioms NSEGR.Assembly.scalar_periodic_cylinder_of_literatureCK
#check @NSEGR.Assembly.scalarLaplacian_spatial_sub
#print axioms NSEGR.Assembly.scalarLaplacian_spatial_sub
#check @NSEGR.Assembly.scalarLaplacian_periodic_nativeGluing
#print axioms NSEGR.Assembly.scalarLaplacian_periodic_nativeGluing
#check @NSEGR.Assembly.scalar_periodic_normal_cylinder_of_literatureCK
#print axioms NSEGR.Assembly.scalar_periodic_normal_cylinder_of_literatureCK
#check @NSEGR.Assembly.boundaryAdmissible_entry_analytic
#print axioms NSEGR.Assembly.boundaryAdmissible_entry_analytic
#check @NSEGR.Assembly.boundaryAdmissible_beta_analytic
#print axioms NSEGR.Assembly.boundaryAdmissible_beta_analytic
#check @NSEGR.Assembly.boundaryAdmissible_raw_analytic
#print axioms NSEGR.Assembly.boundaryAdmissible_raw_analytic
#check @NSEGR.Assembly.boundaryAdmissible_beta_periodic
#print axioms NSEGR.Assembly.boundaryAdmissible_beta_periodic
#check @NSEGR.Assembly.boundaryAdmissible_raw_periodic
#print axioms NSEGR.Assembly.boundaryAdmissible_raw_periodic
#check @NSEGR.Assembly.boundaryAdmissible_raw_smooth
#print axioms NSEGR.Assembly.boundaryAdmissible_raw_smooth
#check @NSEGR.Assembly.boundaryAdmissible_beta_time
#print axioms NSEGR.Assembly.boundaryAdmissible_beta_time
#check @NSEGR.Assembly.boundaryAdmissible_beta_mean
#print axioms NSEGR.Assembly.boundaryAdmissible_beta_mean
#check @NSEGR.Assembly.boundaryAdmissible_rawVelocity_time
#print axioms NSEGR.Assembly.boundaryAdmissible_rawVelocity_time
#check @NSEGR.Assembly.boundaryAdmissible_velocity_analytic
#print axioms NSEGR.Assembly.boundaryAdmissible_velocity_analytic
#check @NSEGR.Assembly.boundaryAdmissible_solenoidal
#print axioms NSEGR.Assembly.boundaryAdmissible_solenoidal
#check @NSEGR.Assembly.boundaryAdmissible_potential_eq
#print axioms NSEGR.Assembly.boundaryAdmissible_potential_eq
#check @NSEGR.Assembly.boundaryAdmissible_potential_eq_eventually
#print axioms NSEGR.Assembly.boundaryAdmissible_potential_eq_eventually
#check @NSEGR.Assembly.boundaryAdmissible_potential_analytic
#print axioms NSEGR.Assembly.boundaryAdmissible_potential_analytic
#check @NSEGR.Assembly.boundaryAdmissible_potential_laplacian
#print axioms NSEGR.Assembly.boundaryAdmissible_potential_laplacian
#check @NSEGR.Assembly.boundaryAdmissible_potential_time
#print axioms NSEGR.Assembly.boundaryAdmissible_potential_time
#check @NSEGR.Assembly.boundaryAdmissible_potential_initial
#print axioms NSEGR.Assembly.boundaryAdmissible_potential_initial
#check @NSEGR.Assembly.boundaryAdmissible_potential_time_initial
#print axioms NSEGR.Assembly.boundaryAdmissible_potential_time_initial
#check @NSEGR.Assembly.boundaryAdmissible_raw_recovery
#print axioms NSEGR.Assembly.boundaryAdmissible_raw_recovery
#check @NSEGR.Assembly.boundaryAdmissible_hodge_time
#print axioms NSEGR.Assembly.boundaryAdmissible_hodge_time
#check @NSEGR.Assembly.scalarLocalTimeDerivative_periodic_native
#print axioms NSEGR.Assembly.scalarLocalTimeDerivative_periodic_native
#check @NSEGR.Assembly.boundaryAdmissible_pressure_analytic
#print axioms NSEGR.Assembly.boundaryAdmissible_pressure_analytic
#check @NSEGR.Assembly.boundaryAdmissible_decoded_pair
#print axioms NSEGR.Assembly.boundaryAdmissible_decoded_pair
#check @NSEGR.Assembly.boundaryAdmissible_residual
#print axioms NSEGR.Assembly.boundaryAdmissible_residual
#check @NSEGR.Assembly.poissonInverse_sub_native
#print axioms NSEGR.Assembly.poissonInverse_sub_native
#check @NSEGR.Assembly.leray_sub_native
#print axioms NSEGR.Assembly.leray_sub_native
#check @NSEGR.Assembly.completedBoundary_velocity_recovery
#print axioms NSEGR.Assembly.completedBoundary_velocity_recovery
#check @NSEGR.Assembly.completedBoundary_potential_recovery
#print axioms NSEGR.Assembly.completedBoundary_potential_recovery
#check @NSEGR.Assembly.completedBoundary_stress_zero
#print axioms NSEGR.Assembly.completedBoundary_stress_zero
#check @NSEGR.Assembly.completedBoundary_pressure_recovery
#print axioms NSEGR.Assembly.completedBoundary_pressure_recovery
#check @NSEGR.Assembly.localNSE_restrict_native
#print axioms NSEGR.Assembly.localNSE_restrict_native
#check @NSEGR.Assembly.scalarBoundaryCompletionLaws_of_literatureCK
#print axioms NSEGR.Assembly.scalarBoundaryCompletionLaws_of_literatureCK
#check @NSEGR.Assembly.GaussianJoint
#print axioms NSEGR.Assembly.GaussianJoint
#check @NSEGR.Assembly.bulkFromJoint
#print axioms NSEGR.Assembly.bulkFromJoint
#check @NSEGR.Assembly.jointFromBulk
#print axioms NSEGR.Assembly.jointFromBulk
#check @NSEGR.Assembly.jointMetric
#print axioms NSEGR.Assembly.jointMetric
#check @NSEGR.Assembly.metricOfJoint
#print axioms NSEGR.Assembly.metricOfJoint
#check @NSEGR.Assembly.metricOfJoint_germ
#print axioms NSEGR.Assembly.metricOfJoint_germ
#check @NSEGR.Assembly.jointMetric_germ
#print axioms NSEGR.Assembly.jointMetric_germ
#check @NSEGR.Assembly.metricOfJoint_translate
#print axioms NSEGR.Assembly.metricOfJoint_translate
#check @NSEGR.Assembly.bulkPartial_metric_germ
#print axioms NSEGR.Assembly.bulkPartial_metric_germ
#check @NSEGR.Assembly.christoffel_metric_germ
#print axioms NSEGR.Assembly.christoffel_metric_germ
#check @NSEGR.Assembly.ricci_metric_germ
#print axioms NSEGR.Assembly.ricci_metric_germ
#check @NSEGR.Assembly.boundaryK_metric_germ
#print axioms NSEGR.Assembly.boundaryK_metric_germ
#check @NSEGR.Assembly.gluingMetricEntry
#print axioms NSEGR.Assembly.gluingMetricEntry
#check @NSEGR.Assembly.near_eta4_of_gaussianGerm
#print axioms NSEGR.Assembly.near_eta4_of_gaussianGerm
#check @NSEGR.Assembly.GaussianGluingLaw
#print axioms NSEGR.Assembly.GaussianGluingLaw
#check @NSEGR.Assembly.GaussianGluingLaw.congr
#print axioms NSEGR.Assembly.GaussianGluingLaw.congr
#check @NSEGR.Assembly.GaussianGluingLaw.translate
#print axioms NSEGR.Assembly.GaussianGluingLaw.translate
#check @NSEGR.Assembly.gaussianGluingLaw_germ_of_literature
#print axioms NSEGR.Assembly.gaussianGluingLaw_germ_of_literature
#check @NSEGR.Assembly.literatureGaussianGerm_of_gluingLaw
#print axioms NSEGR.Assembly.literatureGaussianGerm_of_gluingLaw
#check @NSEGR.Assembly.lorentzian_of_gaussianGluingLaw
#print axioms NSEGR.Assembly.lorentzian_of_gaussianGluingLaw
#check @NSEGR.Assembly.radialExtensionResult_of_literatureGaussian
#print axioms NSEGR.Assembly.radialExtensionResult_of_literatureGaussian
#check @NSEGR.Assembly.analyticRadialExtensionLaws_of_literatureGaussian
#print axioms NSEGR.Assembly.analyticRadialExtensionLaws_of_literatureGaussian
#check @NSEGR.Assembly.scalarNormalGerm_of_hamiltonian
#print axioms NSEGR.Assembly.scalarNormalGerm_of_hamiltonian
#check @NSEGR.Assembly.completedBoundary_scalarNormalGerm
#print axioms NSEGR.Assembly.completedBoundary_scalarNormalGerm
#check @NSEGR.Assembly.scalarLocalTimeDerivative_congr_eventually
#print axioms NSEGR.Assembly.scalarLocalTimeDerivative_congr_eventually
#check @NSEGR.Assembly.completedBoundary_congr_eventually
#print axioms NSEGR.Assembly.completedBoundary_congr_eventually
#check @NSEGR.Assembly.completedBoundary_input_congr_slice
#print axioms NSEGR.Assembly.completedBoundary_input_congr_slice
#check @NSEGR.Assembly.forward_respects_of_literature
#print axioms NSEGR.Assembly.forward_respects_of_literature
#check @NSEGR.Assembly.canonical_boundary_exact_completion
#print axioms NSEGR.Assembly.canonical_boundary_exact_completion
#check @NSEGR.Assembly.geometricReconstructionLaws_native
#print axioms NSEGR.Assembly.geometricReconstructionLaws_native
#check @NSEGR.Assembly.canonical_scalarNormalGerm
#print axioms NSEGR.Assembly.canonical_scalarNormalGerm
#check @NSEGR.Assembly.canonical_chosenBoundary_eventually
#print axioms NSEGR.Assembly.canonical_chosenBoundary_eventually
#check @NSEGR.Assembly.lift_decode_of_literature
#print axioms NSEGR.Assembly.lift_decode_of_literature
#check @NSEGR.Assembly.germInverseLaws_of_literature
#print axioms NSEGR.Assembly.germInverseLaws_of_literature
#check @NSEGR.Assembly.nativeLawPackages_of_literatureInputs
#print axioms NSEGR.Assembly.nativeLawPackages_of_literatureInputs
#check @NSEGR.Assembly.NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_LITERATURE_INPUTS
#print axioms NSEGR.Assembly.NSE_GR_EXACT_SECTOR_EQUIVALENCE_OF_LITERATURE_INPUTS
#check @NSEGR.Assembly.NSE_GR_THREE_OBLIGATION_CLOSURE
#print axioms NSEGR.Assembly.NSE_GR_THREE_OBLIGATION_CLOSURE
#check @NSEGR.NativeLiterature.CKTimeSpace
#print axioms NSEGR.NativeLiterature.CKTimeSpace
#check @NSEGR.NativeLiterature.CKCoeff
#print axioms NSEGR.NativeLiterature.CKCoeff
#check @NSEGR.NativeLiterature.CKSeriesSpace
#print axioms NSEGR.NativeLiterature.CKSeriesSpace
#check @NSEGR.NativeLiterature.CKSeries
#print axioms NSEGR.NativeLiterature.CKSeries
#check @NSEGR.NativeLiterature.ckSeriesSpace_isClosed
#print axioms NSEGR.NativeLiterature.ckSeriesSpace_isClosed
#check @NSEGR.NativeLiterature.ckSeries_completeSpace
#print axioms NSEGR.NativeLiterature.ckSeries_completeSpace
#check @NSEGR.NativeLiterature.ckSymmetrize
#print axioms NSEGR.NativeLiterature.ckSymmetrize
#check @NSEGR.NativeLiterature.ckSymmetrize_symmetric
#print axioms NSEGR.NativeLiterature.ckSymmetrize_symmetric
#check @NSEGR.NativeLiterature.ckSymmetrize_diagonal
#print axioms NSEGR.NativeLiterature.ckSymmetrize_diagonal
#check @NSEGR.NativeLiterature.ckSymmetrize_norm_le
#print axioms NSEGR.NativeLiterature.ckSymmetrize_norm_le
#check @NSEGR.NativeLiterature.ckSymmetrizeCLM
#print axioms NSEGR.NativeLiterature.ckSymmetrizeCLM
#check @NSEGR.NativeLiterature.ckSymmetrizeCLM_apply
#print axioms NSEGR.NativeLiterature.ckSymmetrizeCLM_apply
#check @NSEGR.NativeLiterature.ckSymmetrizeCLM_norm_le
#print axioms NSEGR.NativeLiterature.ckSymmetrizeCLM_norm_le
#check @NSEGR.NativeLiterature.CKSeries.coeff
#print axioms NSEGR.NativeLiterature.CKSeries.coeff
#check @NSEGR.NativeLiterature.CKSeries.formal
#print axioms NSEGR.NativeLiterature.CKSeries.formal
#check @NSEGR.NativeLiterature.CKSeries.coeff_zero
#print axioms NSEGR.NativeLiterature.CKSeries.coeff_zero
#check @NSEGR.NativeLiterature.CKSeries.coeff_symm
#print axioms NSEGR.NativeLiterature.CKSeries.coeff_symm
#check @NSEGR.NativeLiterature.CKSeries.coeff_add
#print axioms NSEGR.NativeLiterature.CKSeries.coeff_add
#check @NSEGR.NativeLiterature.CKSeries.coeff_smul
#print axioms NSEGR.NativeLiterature.CKSeries.coeff_smul
#check @NSEGR.NativeLiterature.CKSeries.coeff_sub
#print axioms NSEGR.NativeLiterature.CKSeries.coeff_sub
#check @NSEGR.NativeLiterature.CKSeries.coeff_zero_series
#print axioms NSEGR.NativeLiterature.CKSeries.coeff_zero_series
#check @NSEGR.NativeLiterature.CKSeries.ext
#print axioms NSEGR.NativeLiterature.CKSeries.ext
#check @NSEGR.NativeLiterature.CKSeries.hasSum_norm
#print axioms NSEGR.NativeLiterature.CKSeries.hasSum_norm
#check @NSEGR.NativeLiterature.CKSeries.summable_norm
#print axioms NSEGR.NativeLiterature.CKSeries.summable_norm
#check @NSEGR.NativeLiterature.CKSeries.norm_eq_tsum
#print axioms NSEGR.NativeLiterature.CKSeries.norm_eq_tsum
#check @NSEGR.NativeLiterature.CKSeries.coeff_norm_le
#print axioms NSEGR.NativeLiterature.CKSeries.coeff_norm_le
#check @NSEGR.NativeLiterature.CKSeries.ofCoeffs
#print axioms NSEGR.NativeLiterature.CKSeries.ofCoeffs
#check @NSEGR.NativeLiterature.CKSeries.ofCoeffs_coeff
#print axioms NSEGR.NativeLiterature.CKSeries.ofCoeffs_coeff
#check @NSEGR.NativeLiterature.CKSeries.one_le_radius
#print axioms NSEGR.NativeLiterature.CKSeries.one_le_radius
#check @NSEGR.NativeLiterature.CKSeries.radius_pos
#print axioms NSEGR.NativeLiterature.CKSeries.radius_pos
#check @NSEGR.NativeLiterature.CKSeries.eval
#print axioms NSEGR.NativeLiterature.CKSeries.eval
#check @NSEGR.NativeLiterature.CKSeries.hasFPowerSeriesOnBall
#print axioms NSEGR.NativeLiterature.CKSeries.hasFPowerSeriesOnBall
#check @NSEGR.NativeLiterature.CKSeries.analyticAt_zero
#print axioms NSEGR.NativeLiterature.CKSeries.analyticAt_zero
#check @NSEGR.NativeLiterature.CKSeries.analyticAt
#print axioms NSEGR.NativeLiterature.CKSeries.analyticAt
#check @NSEGR.NativeLiterature.CKSeries.eval_zero
#print axioms NSEGR.NativeLiterature.CKSeries.eval_zero
#check @NSEGR.NativeLiterature.CKSeries.hasSum_eval
#print axioms NSEGR.NativeLiterature.CKSeries.hasSum_eval
#check @NSEGR.NativeLiterature.CKSeries.norm_eval_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_eval_le
#check @NSEGR.NativeLiterature.CKSeries.iteratedFDeriv_eval_zero
#print axioms NSEGR.NativeLiterature.CKSeries.iteratedFDeriv_eval_zero
#check @NSEGR.NativeLiterature.CKSeries.eq_of_eval_eventuallyEq
#print axioms NSEGR.NativeLiterature.CKSeries.eq_of_eval_eventuallyEq
#check @NSEGR.NativeLiterature.CKSeries.coeffCLM
#print axioms NSEGR.NativeLiterature.CKSeries.coeffCLM
#check @NSEGR.NativeLiterature.CKSeries.coeffCLM_apply
#print axioms NSEGR.NativeLiterature.CKSeries.coeffCLM_apply
#check @NSEGR.NativeLiterature.CKSeries.coeff_tsum
#print axioms NSEGR.NativeLiterature.CKSeries.coeff_tsum
#check @NSEGR.NativeLiterature.CKSeries.postcompose
#print axioms NSEGR.NativeLiterature.CKSeries.postcompose
#check @NSEGR.NativeLiterature.CKSeries.postcompose_coeff
#print axioms NSEGR.NativeLiterature.CKSeries.postcompose_coeff
#check @NSEGR.NativeLiterature.CKSeries.norm_postcompose_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_postcompose_le
#check @NSEGR.NativeLiterature.CKSeries.postcompose_add
#print axioms NSEGR.NativeLiterature.CKSeries.postcompose_add
#check @NSEGR.NativeLiterature.CKSeries.postcompose_smul
#print axioms NSEGR.NativeLiterature.CKSeries.postcompose_smul
#check @NSEGR.NativeLiterature.CKSeries.postcomposeCLM
#print axioms NSEGR.NativeLiterature.CKSeries.postcomposeCLM
#check @NSEGR.NativeLiterature.CKSeries.postcomposeCLM_apply
#print axioms NSEGR.NativeLiterature.CKSeries.postcomposeCLM_apply
#check @NSEGR.NativeLiterature.CKSeries.norm_postcomposeCLM_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_postcomposeCLM_le
#check @NSEGR.NativeLiterature.CKSeries.single
#print axioms NSEGR.NativeLiterature.CKSeries.single
#check @NSEGR.NativeLiterature.CKSeries.single_coeff_self
#print axioms NSEGR.NativeLiterature.CKSeries.single_coeff_self
#check @NSEGR.NativeLiterature.CKSeries.single_coeff_ne
#print axioms NSEGR.NativeLiterature.CKSeries.single_coeff_ne
#check @NSEGR.NativeLiterature.CKSeries.norm_single
#print axioms NSEGR.NativeLiterature.CKSeries.norm_single
#check @NSEGR.NativeLiterature.CKSeries.eval_add
#print axioms NSEGR.NativeLiterature.CKSeries.eval_add
#check @NSEGR.NativeLiterature.CKSeries.eval_smul
#print axioms NSEGR.NativeLiterature.CKSeries.eval_smul
#check @NSEGR.NativeLiterature.CKSeries.evalCLM
#print axioms NSEGR.NativeLiterature.CKSeries.evalCLM
#check @NSEGR.NativeLiterature.CKSeries.evalCLM_apply
#print axioms NSEGR.NativeLiterature.CKSeries.evalCLM_apply
#check @NSEGR.NativeLiterature.CKSeries.eval_tsum
#print axioms NSEGR.NativeLiterature.CKSeries.eval_tsum
#check @NSEGR.NativeLiterature.CKSeries.eval_postcompose
#print axioms NSEGR.NativeLiterature.CKSeries.eval_postcompose
#check @NSEGR.NativeLiterature.CKSeries.eval_single
#print axioms NSEGR.NativeLiterature.CKSeries.eval_single
#check @NSEGR.NativeLiterature.ckTimeProj
#print axioms NSEGR.NativeLiterature.ckTimeProj
#check @NSEGR.NativeLiterature.ckSpaceProj
#print axioms NSEGR.NativeLiterature.ckSpaceProj
#check @NSEGR.NativeLiterature.ckTimeInclude
#print axioms NSEGR.NativeLiterature.ckTimeInclude
#check @NSEGR.NativeLiterature.ckSpaceInclude
#print axioms NSEGR.NativeLiterature.ckSpaceInclude
#check @NSEGR.NativeLiterature.ckTimeScale
#print axioms NSEGR.NativeLiterature.ckTimeScale
#check @NSEGR.NativeLiterature.ckTimeProj_apply
#print axioms NSEGR.NativeLiterature.ckTimeProj_apply
#check @NSEGR.NativeLiterature.ckSpaceProj_apply
#print axioms NSEGR.NativeLiterature.ckSpaceProj_apply
#check @NSEGR.NativeLiterature.ckTimeScale_apply
#print axioms NSEGR.NativeLiterature.ckTimeScale_apply
#check @NSEGR.NativeLiterature.ckTimeScale_continuous
#print axioms NSEGR.NativeLiterature.ckTimeScale_continuous
#check @NSEGR.NativeLiterature.ckTimeScale_norm
#print axioms NSEGR.NativeLiterature.ckTimeScale_norm
#check @NSEGR.NativeLiterature.ck_prod_erase_eq_succAbove
#print axioms NSEGR.NativeLiterature.ck_prod_erase_eq_succAbove
#check @NSEGR.NativeLiterature.ck_hasDerivAt_product
#print axioms NSEGR.NativeLiterature.ck_hasDerivAt_product
#check @NSEGR.NativeLiterature.ck_integral_product_derivative
#print axioms NSEGR.NativeLiterature.ck_integral_product_derivative
#check @NSEGR.NativeLiterature.ckInsertTimeCLM
#print axioms NSEGR.NativeLiterature.ckInsertTimeCLM
#check @NSEGR.NativeLiterature.ckInsertTimeCLM_apply
#print axioms NSEGR.NativeLiterature.ckInsertTimeCLM_apply
#check @NSEGR.NativeLiterature.ckPrimitiveKernelCLM
#print axioms NSEGR.NativeLiterature.ckPrimitiveKernelCLM
#check @NSEGR.NativeLiterature.ckPrimitiveKernelCLM_apply
#print axioms NSEGR.NativeLiterature.ckPrimitiveKernelCLM_apply
#check @NSEGR.NativeLiterature.ckPrimitiveKernelCLM_continuous
#print axioms NSEGR.NativeLiterature.ckPrimitiveKernelCLM_continuous
#check @NSEGR.NativeLiterature.ckPrimitiveKernelCLM_eval_norm_le
#print axioms NSEGR.NativeLiterature.ckPrimitiveKernelCLM_eval_norm_le
#check @NSEGR.NativeLiterature.ckPrimitiveCoeffCLM
#print axioms NSEGR.NativeLiterature.ckPrimitiveCoeffCLM
#check @NSEGR.NativeLiterature.ckPrimitiveIntegral_apply
#print axioms NSEGR.NativeLiterature.ckPrimitiveIntegral_apply
#check @NSEGR.NativeLiterature.ckPrimitiveIntegral_norm_le
#print axioms NSEGR.NativeLiterature.ckPrimitiveIntegral_norm_le
#check @NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_norm_apply_le
#print axioms NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_norm_apply_le
#check @NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_norm_le
#print axioms NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_norm_le
#check @NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_symmetric
#print axioms NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_symmetric
#check @NSEGR.NativeLiterature.ckTimePrimitiveFormal
#print axioms NSEGR.NativeLiterature.ckTimePrimitiveFormal
#check @NSEGR.NativeLiterature.ckTimePrimitiveFormal_norm_le
#print axioms NSEGR.NativeLiterature.ckTimePrimitiveFormal_norm_le
#check @NSEGR.NativeLiterature.ckTimePrimitiveFormal_summable
#print axioms NSEGR.NativeLiterature.ckTimePrimitiveFormal_summable
#check @NSEGR.NativeLiterature.ckTimePrimitiveSeries
#print axioms NSEGR.NativeLiterature.ckTimePrimitiveSeries
#check @NSEGR.NativeLiterature.ckTimePrimitiveSeries_coeff_succ
#print axioms NSEGR.NativeLiterature.ckTimePrimitiveSeries_coeff_succ
#check @NSEGR.NativeLiterature.ckTimePrimitiveSeries_norm_le
#print axioms NSEGR.NativeLiterature.ckTimePrimitiveSeries_norm_le
#check @NSEGR.NativeLiterature.timePrimitive
#print axioms NSEGR.NativeLiterature.timePrimitive
#check @NSEGR.NativeLiterature.timePrimitive_apply
#print axioms NSEGR.NativeLiterature.timePrimitive_apply
#check @NSEGR.NativeLiterature.timePrimitive_norm_le
#print axioms NSEGR.NativeLiterature.timePrimitive_norm_le
#check @NSEGR.NativeLiterature.ckPrimitiveKernelCLM_diagonal
#print axioms NSEGR.NativeLiterature.ckPrimitiveKernelCLM_diagonal
#check @NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_diagonal
#print axioms NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_diagonal
#check @NSEGR.NativeLiterature.ckTimeScale_norm_le
#print axioms NSEGR.NativeLiterature.ckTimeScale_norm_le
#check @NSEGR.NativeLiterature.timePrimitive_eval_eq_scaled_integral
#print axioms NSEGR.NativeLiterature.timePrimitive_eval_eq_scaled_integral
#check @NSEGR.NativeLiterature.timePrimitive_eval_eq_integral
#print axioms NSEGR.NativeLiterature.timePrimitive_eval_eq_integral
#check @NSEGR.NativeLiterature.ckSymmetric_update_eq_snoc
#print axioms NSEGR.NativeLiterature.ckSymmetric_update_eq_snoc
#check @NSEGR.NativeLiterature.ckSymmetric_hasFDerivAt_diagonal
#print axioms NSEGR.NativeLiterature.ckSymmetric_hasFDerivAt_diagonal
#check @NSEGR.NativeLiterature.ckPrimitiveDerivativeCoeffCLM
#print axioms NSEGR.NativeLiterature.ckPrimitiveDerivativeCoeffCLM
#check @NSEGR.NativeLiterature.ckPrimitiveDerivativeCoeffCLM_apply
#print axioms NSEGR.NativeLiterature.ckPrimitiveDerivativeCoeffCLM_apply
#check @NSEGR.NativeLiterature.ckPrimitiveDerivativeCoeffCLM_norm_apply_le
#print axioms NSEGR.NativeLiterature.ckPrimitiveDerivativeCoeffCLM_norm_apply_le
#check @NSEGR.NativeLiterature.ckPrimitiveDerivativeCoeffCLM_symmetric
#print axioms NSEGR.NativeLiterature.ckPrimitiveDerivativeCoeffCLM_symmetric
#check @NSEGR.NativeLiterature.ckPrimitiveDerivativeSeries
#print axioms NSEGR.NativeLiterature.ckPrimitiveDerivativeSeries
#check @NSEGR.NativeLiterature.ckPrimitiveDerivativeSeries_coeff
#print axioms NSEGR.NativeLiterature.ckPrimitiveDerivativeSeries_coeff
#check @NSEGR.NativeLiterature.ckPrimitiveDerivativeSeries_norm_le
#print axioms NSEGR.NativeLiterature.ckPrimitiveDerivativeSeries_norm_le
#check @NSEGR.NativeLiterature.timePrimitiveDerivative
#print axioms NSEGR.NativeLiterature.timePrimitiveDerivative
#check @NSEGR.NativeLiterature.timePrimitiveDerivative_coeff
#print axioms NSEGR.NativeLiterature.timePrimitiveDerivative_coeff
#check @NSEGR.NativeLiterature.timePrimitiveDerivative_norm_le
#print axioms NSEGR.NativeLiterature.timePrimitiveDerivative_norm_le
#check @NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_hasFDerivAt_diagonal
#print axioms NSEGR.NativeLiterature.ckPrimitiveCoeffCLM_hasFDerivAt_diagonal
#check @NSEGR.NativeLiterature.timePrimitive_hasFDerivAt
#print axioms NSEGR.NativeLiterature.timePrimitive_hasFDerivAt
#check @NSEGR.NativeLiterature.timePrimitiveDerivative_eval_eq_fderiv
#print axioms NSEGR.NativeLiterature.timePrimitiveDerivative_eval_eq_fderiv
#check @NSEGR.NativeLiterature.ckSpaceInclude_apply
#print axioms NSEGR.NativeLiterature.ckSpaceInclude_apply
#check @NSEGR.NativeLiterature.ckSpaceInclude_norm_le
#print axioms NSEGR.NativeLiterature.ckSpaceInclude_norm_le
#check @NSEGR.NativeLiterature.ckSpatialRestriction
#print axioms NSEGR.NativeLiterature.ckSpatialRestriction
#check @NSEGR.NativeLiterature.ckSpatialRestriction_apply
#print axioms NSEGR.NativeLiterature.ckSpatialRestriction_apply
#check @NSEGR.NativeLiterature.ckSpatialRestriction_norm_le
#print axioms NSEGR.NativeLiterature.ckSpatialRestriction_norm_le
#check @NSEGR.NativeLiterature.spatialPrimitive
#print axioms NSEGR.NativeLiterature.spatialPrimitive
#check @NSEGR.NativeLiterature.spatialPrimitive_norm_le
#print axioms NSEGR.NativeLiterature.spatialPrimitive_norm_le
#check @NSEGR.NativeLiterature.spatialPrimitive_eval_eq_fderiv
#print axioms NSEGR.NativeLiterature.spatialPrimitive_eval_eq_fderiv
#check @NSEGR.NativeLiterature.ck_exists_scaling_budget
#print axioms NSEGR.NativeLiterature.ck_exists_scaling_budget
#check @NSEGR.NativeLiterature.ck_scaled_tuple_budget
#print axioms NSEGR.NativeLiterature.ck_scaled_tuple_budget
#check @NSEGR.NativeLiterature.ck_exists_scaling_budget_lt
#print axioms NSEGR.NativeLiterature.ck_exists_scaling_budget_lt
#check @NSEGR.NativeLiterature.ck_exists_unique_fixedPoint_closedUnitBall
#print axioms NSEGR.NativeLiterature.ck_exists_unique_fixedPoint_closedUnitBall
#check @NSEGR.NativeLiterature.ck_scaled_superposition_bounds
#print axioms NSEGR.NativeLiterature.ck_scaled_superposition_bounds
#check @NSEGR.NativeLiterature.ck_exists_unique_scaled_fixedPoint
#print axioms NSEGR.NativeLiterature.ck_exists_unique_scaled_fixedPoint
#check @NSEGR.NativeLiterature.ckBilinearCoeff
#print axioms NSEGR.NativeLiterature.ckBilinearCoeff
#check @NSEGR.NativeLiterature.ckBilinearCoeff_diagonal
#print axioms NSEGR.NativeLiterature.ckBilinearCoeff_diagonal
#check @NSEGR.NativeLiterature.ckBilinearCoeff_norm_le
#print axioms NSEGR.NativeLiterature.ckBilinearCoeff_norm_le
#check @NSEGR.NativeLiterature.CKSeries.bilinearTerm
#print axioms NSEGR.NativeLiterature.CKSeries.bilinearTerm
#check @NSEGR.NativeLiterature.CKSeries.norm_bilinearTerm_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_bilinearTerm_le
#check @NSEGR.NativeLiterature.CKSeries.bilinearTerm_summable
#print axioms NSEGR.NativeLiterature.CKSeries.bilinearTerm_summable
#check @NSEGR.NativeLiterature.CKSeries.bilinear
#print axioms NSEGR.NativeLiterature.CKSeries.bilinear
#check @NSEGR.NativeLiterature.CKSeries.norm_bilinear_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_bilinear_le
#check @NSEGR.NativeLiterature.CKSeries.eval_bilinearTerm
#print axioms NSEGR.NativeLiterature.CKSeries.eval_bilinearTerm
#check @NSEGR.NativeLiterature.CKSeries.eval_bilinear
#print axioms NSEGR.NativeLiterature.CKSeries.eval_bilinear
#check @NSEGR.NativeLiterature.CKSeries.bilinear_add_left
#print axioms NSEGR.NativeLiterature.CKSeries.bilinear_add_left
#check @NSEGR.NativeLiterature.CKSeries.bilinear_smul_left
#print axioms NSEGR.NativeLiterature.CKSeries.bilinear_smul_left
#check @NSEGR.NativeLiterature.CKSeries.bilinear_add_right
#print axioms NSEGR.NativeLiterature.CKSeries.bilinear_add_right
#check @NSEGR.NativeLiterature.CKSeries.bilinear_smul_right
#print axioms NSEGR.NativeLiterature.CKSeries.bilinear_smul_right
#check @NSEGR.NativeLiterature.ck_multilinear_diagonal_difference_bound
#print axioms NSEGR.NativeLiterature.ck_multilinear_diagonal_difference_bound
#check @NSEGR.NativeLiterature.ck_multilinear_diagonal_norm_bound
#print axioms NSEGR.NativeLiterature.ck_multilinear_diagonal_norm_bound
#check @NSEGR.NativeLiterature.ckPositiveMultilinearSum
#print axioms NSEGR.NativeLiterature.ckPositiveMultilinearSum
#check @NSEGR.NativeLiterature.ckPositiveMajorant
#print axioms NSEGR.NativeLiterature.ckPositiveMajorant
#check @NSEGR.NativeLiterature.ckPositiveMajorant_nonneg
#print axioms NSEGR.NativeLiterature.ckPositiveMajorant_nonneg
#check @NSEGR.NativeLiterature.ckPositiveMultilinearSum_summable
#print axioms NSEGR.NativeLiterature.ckPositiveMultilinearSum_summable
#check @NSEGR.NativeLiterature.ckPositiveMultilinearSum_norm_le
#print axioms NSEGR.NativeLiterature.ckPositiveMultilinearSum_norm_le
#check @NSEGR.NativeLiterature.ckPositiveMultilinearSum_difference_le
#print axioms NSEGR.NativeLiterature.ckPositiveMultilinearSum_difference_le
#check @NSEGR.NativeLiterature.ck_summable_derivative_majorant_halfRadius
#print axioms NSEGR.NativeLiterature.ck_summable_derivative_majorant_halfRadius
#check @NSEGR.NativeLiterature.ckCurryZeroCLM
#print axioms NSEGR.NativeLiterature.ckCurryZeroCLM
#check @NSEGR.NativeLiterature.ckCurryLeftCLM
#print axioms NSEGR.NativeLiterature.ckCurryLeftCLM
#check @NSEGR.NativeLiterature.ckCurryZeroCLM_norm_le
#print axioms NSEGR.NativeLiterature.ckCurryZeroCLM_norm_le
#check @NSEGR.NativeLiterature.ckCurryLeftCLM_norm_le
#print axioms NSEGR.NativeLiterature.ckCurryLeftCLM_norm_le
#check @NSEGR.NativeLiterature.CKSeries.contractMultilinear
#print axioms NSEGR.NativeLiterature.CKSeries.contractMultilinear
#check @NSEGR.NativeLiterature.CKSeries.norm_contractMultilinear_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_contractMultilinear_le
#check @NSEGR.NativeLiterature.CKSeries.eval_contractMultilinear
#print axioms NSEGR.NativeLiterature.CKSeries.eval_contractMultilinear
#check @NSEGR.NativeLiterature.CKSeries.multilinearApply
#print axioms NSEGR.NativeLiterature.CKSeries.multilinearApply
#check @NSEGR.NativeLiterature.CKSeries.norm_multilinearApply_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_multilinearApply_le
#check @NSEGR.NativeLiterature.CKSeries.eval_multilinearApply
#print axioms NSEGR.NativeLiterature.CKSeries.eval_multilinearApply
#check @NSEGR.NativeLiterature.CKSeries.multilinearLift
#print axioms NSEGR.NativeLiterature.CKSeries.multilinearLift
#check @NSEGR.NativeLiterature.CKSeries.multilinearLift_apply
#print axioms NSEGR.NativeLiterature.CKSeries.multilinearLift_apply
#check @NSEGR.NativeLiterature.CKSeries.norm_multilinearLift_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_multilinearLift_le
#check @NSEGR.NativeLiterature.CKSeries.superposition
#print axioms NSEGR.NativeLiterature.CKSeries.superposition
#check @NSEGR.NativeLiterature.CKSeries.superposition_majorant_summable
#print axioms NSEGR.NativeLiterature.CKSeries.superposition_majorant_summable
#check @NSEGR.NativeLiterature.CKSeries.superposition_majorant_le
#print axioms NSEGR.NativeLiterature.CKSeries.superposition_majorant_le
#check @NSEGR.NativeLiterature.CKSeries.norm_superposition_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_superposition_le
#check @NSEGR.NativeLiterature.CKSeries.superposition_difference_le
#print axioms NSEGR.NativeLiterature.CKSeries.superposition_difference_le
#check @NSEGR.NativeLiterature.CKSeries.eval_superposition
#print axioms NSEGR.NativeLiterature.CKSeries.eval_superposition
#check @NSEGR.NativeLiterature.CKJet
#print axioms NSEGR.NativeLiterature.CKJet
#check @NSEGR.NativeLiterature.CKRHS
#print axioms NSEGR.NativeLiterature.CKRHS
#check @NSEGR.NativeLiterature.ckInitialJet
#print axioms NSEGR.NativeLiterature.ckInitialJet
#check @NSEGR.NativeLiterature.CKLocalSolution
#print axioms NSEGR.NativeLiterature.CKLocalSolution
#check @NSEGR.NativeLiterature.ckInitialVelocity
#print axioms NSEGR.NativeLiterature.ckInitialVelocity
#check @NSEGR.NativeLiterature.ckNormalizeJet
#print axioms NSEGR.NativeLiterature.ckNormalizeJet
#check @NSEGR.NativeLiterature.ckNormalizeRHS
#print axioms NSEGR.NativeLiterature.ckNormalizeRHS
#check @NSEGR.NativeLiterature.ckNormalizeSolution
#print axioms NSEGR.NativeLiterature.ckNormalizeSolution
#check @NSEGR.NativeLiterature.ckDenormalizeSolution
#print axioms NSEGR.NativeLiterature.ckDenormalizeSolution
#check @NSEGR.NativeLiterature.CKNormalizedSolution
#print axioms NSEGR.NativeLiterature.CKNormalizedSolution
#check @NSEGR.NativeLiterature.ckTimeDerivative
#print axioms NSEGR.NativeLiterature.ckTimeDerivative
#check @NSEGR.NativeLiterature.ckSpaceDerivative
#print axioms NSEGR.NativeLiterature.ckSpaceDerivative
#check @NSEGR.NativeLiterature.ckSpaceDerivative_eq_fderiv
#print axioms NSEGR.NativeLiterature.ckSpaceDerivative_eq_fderiv
#check @NSEGR.NativeLiterature.ckSpaceDerivative_germ_of_eq
#print axioms NSEGR.NativeLiterature.ckSpaceDerivative_germ_of_eq
#check @NSEGR.NativeLiterature.ckScaledSolution
#print axioms NSEGR.NativeLiterature.ckScaledSolution
#check @NSEGR.NativeLiterature.ckScaledSolution_analyticAt
#print axioms NSEGR.NativeLiterature.ckScaledSolution_analyticAt
#check @NSEGR.NativeLiterature.ckScaledSolution_timeDerivative
#print axioms NSEGR.NativeLiterature.ckScaledSolution_timeDerivative
#check @NSEGR.NativeLiterature.ckScaledSolution_spaceDerivative
#print axioms NSEGR.NativeLiterature.ckScaledSolution_spaceDerivative
#check @NSEGR.NativeLiterature.ckTimeDerivative_eq_fderiv
#print axioms NSEGR.NativeLiterature.ckTimeDerivative_eq_fderiv
#check @NSEGR.NativeLiterature.ckTimeDerivative_analyticAt
#print axioms NSEGR.NativeLiterature.ckTimeDerivative_analyticAt
#check @NSEGR.NativeLiterature.ckTimeDerivative_germ_of_eq
#print axioms NSEGR.NativeLiterature.ckTimeDerivative_germ_of_eq
#check @NSEGR.NativeLiterature.ckNormalizedSolution_congr
#print axioms NSEGR.NativeLiterature.ckNormalizedSolution_congr
#check @NSEGR.NativeLiterature.ckNormalizedSolution_timeDerivative_zero
#print axioms NSEGR.NativeLiterature.ckNormalizedSolution_timeDerivative_zero
#check @NSEGR.NativeLiterature.ckGerm_eq_of_timeDerivative_eq
#print axioms NSEGR.NativeLiterature.ckGerm_eq_of_timeDerivative_eq
#check @NSEGR.NativeLiterature.ckNormalizeJet_zero
#print axioms NSEGR.NativeLiterature.ckNormalizeJet_zero
#check @NSEGR.NativeLiterature.ckNormalizeRHS_zero
#print axioms NSEGR.NativeLiterature.ckNormalizeRHS_zero
#check @NSEGR.NativeLiterature.ckNormalizeJet_analyticAt
#print axioms NSEGR.NativeLiterature.ckNormalizeJet_analyticAt
#check @NSEGR.NativeLiterature.ckNormalizeRHS_analyticAt
#print axioms NSEGR.NativeLiterature.ckNormalizeRHS_analyticAt
#check @NSEGR.NativeLiterature.ckDenormalize_normalize
#print axioms NSEGR.NativeLiterature.ckDenormalize_normalize
#check @NSEGR.NativeLiterature.ckNormalize_denormalize
#print axioms NSEGR.NativeLiterature.ckNormalize_denormalize
#check @NSEGR.NativeLiterature.ckNormalizeSolution_analyticAt
#print axioms NSEGR.NativeLiterature.ckNormalizeSolution_analyticAt
#check @NSEGR.NativeLiterature.ckDenormalizeSolution_analyticAt
#print axioms NSEGR.NativeLiterature.ckDenormalizeSolution_analyticAt
#check @NSEGR.NativeLiterature.ckNormalizeSolution_timeDerivative
#print axioms NSEGR.NativeLiterature.ckNormalizeSolution_timeDerivative
#check @NSEGR.NativeLiterature.ckNormalizeSolution_spaceDerivative
#print axioms NSEGR.NativeLiterature.ckNormalizeSolution_spaceDerivative
#check @NSEGR.NativeLiterature.ckDenormalizeSolution_timeDerivative
#print axioms NSEGR.NativeLiterature.ckDenormalizeSolution_timeDerivative
#check @NSEGR.NativeLiterature.ckDenormalizeSolution_spaceDerivative
#print axioms NSEGR.NativeLiterature.ckDenormalizeSolution_spaceDerivative
#check @NSEGR.NativeLiterature.ckNormalizeSolution_jet
#print axioms NSEGR.NativeLiterature.ckNormalizeSolution_jet
#check @NSEGR.NativeLiterature.ckDenormalizeSolution_jet
#print axioms NSEGR.NativeLiterature.ckDenormalizeSolution_jet
#check @NSEGR.NativeLiterature.ckNormalizeSolution_isSolution
#print axioms NSEGR.NativeLiterature.ckNormalizeSolution_isSolution
#check @NSEGR.NativeLiterature.ckDenormalizeSolution_isSolution
#print axioms NSEGR.NativeLiterature.ckDenormalizeSolution_isSolution
#check @NSEGR.NativeLiterature.ckDenormalizeSolution_germ
#print axioms NSEGR.NativeLiterature.ckDenormalizeSolution_germ
#check @NSEGR.NativeLiterature.ckLocal_exists_unique_of_normalized
#print axioms NSEGR.NativeLiterature.ckLocal_exists_unique_of_normalized
#check @NSEGR.NativeLiterature.CKSeries.linear
#print axioms NSEGR.NativeLiterature.CKSeries.linear
#check @NSEGR.NativeLiterature.CKSeries.norm_linear
#print axioms NSEGR.NativeLiterature.CKSeries.norm_linear
#check @NSEGR.NativeLiterature.CKSeries.eval_linear
#print axioms NSEGR.NativeLiterature.CKSeries.eval_linear
#check @NSEGR.NativeLiterature.CKSeries.pair
#print axioms NSEGR.NativeLiterature.CKSeries.pair
#check @NSEGR.NativeLiterature.CKSeries.norm_pair_le
#print axioms NSEGR.NativeLiterature.CKSeries.norm_pair_le
#check @NSEGR.NativeLiterature.CKSeries.pair_sub
#print axioms NSEGR.NativeLiterature.CKSeries.pair_sub
#check @NSEGR.NativeLiterature.CKSeries.eval_pair
#print axioms NSEGR.NativeLiterature.CKSeries.eval_pair
#check @NSEGR.NativeLiterature.ckCoefficientScale
#print axioms NSEGR.NativeLiterature.ckCoefficientScale
#check @NSEGR.NativeLiterature.ckCoefficientScale_norm_le
#print axioms NSEGR.NativeLiterature.ckCoefficientScale_norm_le
#check @NSEGR.NativeLiterature.ckScaledJetUsing
#print axioms NSEGR.NativeLiterature.ckScaledJetUsing
#check @NSEGR.NativeLiterature.ckScaledJetUsing_norm_le
#print axioms NSEGR.NativeLiterature.ckScaledJetUsing_norm_le
#check @NSEGR.NativeLiterature.ckScaledJetUsing_difference_le
#print axioms NSEGR.NativeLiterature.ckScaledJetUsing_difference_le
#check @NSEGR.NativeLiterature.ckScaledJetUsing_eval
#print axioms NSEGR.NativeLiterature.ckScaledJetUsing_eval
#check @NSEGR.NativeLiterature.ckScaledCoefficientMapUsing
#print axioms NSEGR.NativeLiterature.ckScaledCoefficientMapUsing
#check @NSEGR.NativeLiterature.ckScaledCoefficientMapUsing_eval
#print axioms NSEGR.NativeLiterature.ckScaledCoefficientMapUsing_eval
#check @NSEGR.NativeLiterature.ckScaledCoefficientMapUsing_fixedPoint
#print axioms NSEGR.NativeLiterature.ckScaledCoefficientMapUsing_fixedPoint
#check @NSEGR.NativeLiterature.ckScaledCoefficientMapUsing_exists_fixedPoint
#print axioms NSEGR.NativeLiterature.ckScaledCoefficientMapUsing_exists_fixedPoint
#check @NSEGR.NativeLiterature.ckAnalytic_superposition_data
#print axioms NSEGR.NativeLiterature.ckAnalytic_superposition_data
#check @NSEGR.NativeLiterature.ckScaledJet
#print axioms NSEGR.NativeLiterature.ckScaledJet
#check @NSEGR.NativeLiterature.ckScaledJet_norm_le
#print axioms NSEGR.NativeLiterature.ckScaledJet_norm_le
#check @NSEGR.NativeLiterature.ckScaledJet_difference_le
#print axioms NSEGR.NativeLiterature.ckScaledJet_difference_le
#check @NSEGR.NativeLiterature.ckScaledJet_eval
#print axioms NSEGR.NativeLiterature.ckScaledJet_eval
#check @NSEGR.NativeLiterature.ckScaledCoefficientMap
#print axioms NSEGR.NativeLiterature.ckScaledCoefficientMap
#check @NSEGR.NativeLiterature.ckScaledCoefficientMap_fixedPoint
#print axioms NSEGR.NativeLiterature.ckScaledCoefficientMap_fixedPoint
#check @NSEGR.NativeLiterature.ckScaledCoefficientMap_eval
#print axioms NSEGR.NativeLiterature.ckScaledCoefficientMap_eval
#check @NSEGR.NativeLiterature.ckAnalytic_exists_coefficient_fixedPoint
#print axioms NSEGR.NativeLiterature.ckAnalytic_exists_coefficient_fixedPoint
#check @NSEGR.NativeLiterature.ckCoordinateEval
#print axioms NSEGR.NativeLiterature.ckCoordinateEval
#check @NSEGR.NativeLiterature.ckCoordinateEval_analyticAt
#print axioms NSEGR.NativeLiterature.ckCoordinateEval_analyticAt
#check @NSEGR.NativeLiterature.ckCoordinateEval_analyticAt_zero
#print axioms NSEGR.NativeLiterature.ckCoordinateEval_analyticAt_zero
#check @NSEGR.NativeLiterature.ckCoordinate_unitBall_eventually
#print axioms NSEGR.NativeLiterature.ckCoordinate_unitBall_eventually
#check @NSEGR.NativeLiterature.ckPhysicalScale
#print axioms NSEGR.NativeLiterature.ckPhysicalScale
#check @NSEGR.NativeLiterature.ckPhysicalScale_apply
#print axioms NSEGR.NativeLiterature.ckPhysicalScale_apply
#check @NSEGR.NativeLiterature.ckPhysicalScale_norm_le
#print axioms NSEGR.NativeLiterature.ckPhysicalScale_norm_le
#check @NSEGR.NativeLiterature.ckInversePhysicalScale
#print axioms NSEGR.NativeLiterature.ckInversePhysicalScale
#check @NSEGR.NativeLiterature.ckInversePhysicalScale_apply
#print axioms NSEGR.NativeLiterature.ckInversePhysicalScale_apply
#check @NSEGR.NativeLiterature.ckPhysicalScale_rightInverse
#print axioms NSEGR.NativeLiterature.ckPhysicalScale_rightInverse
#check @NSEGR.NativeLiterature.ckPhysicalScale_leftInverse
#print axioms NSEGR.NativeLiterature.ckPhysicalScale_leftInverse
#check @NSEGR.NativeLiterature.ckGerm_eq_of_physicalScale
#print axioms NSEGR.NativeLiterature.ckGerm_eq_of_physicalScale
#check @NSEGR.NativeLiterature.ckSymmetrize_hasFPowerSeriesAt
#print axioms NSEGR.NativeLiterature.ckSymmetrize_hasFPowerSeriesAt
#check @NSEGR.NativeLiterature.ckMajorant_tendsto_zero
#print axioms NSEGR.NativeLiterature.ckMajorant_tendsto_zero
#check @NSEGR.NativeLiterature.ckAnalytic_exists_small_comp_series
#print axioms NSEGR.NativeLiterature.ckAnalytic_exists_small_comp_series
#check @NSEGR.NativeLiterature.ckNormalizedSolution_small_timeSeries
#print axioms NSEGR.NativeLiterature.ckNormalizedSolution_small_timeSeries
#check @NSEGR.NativeLiterature.ckNormalizedSolution_eq_of_timeSeries
#print axioms NSEGR.NativeLiterature.ckNormalizedSolution_eq_of_timeSeries
#check @NSEGR.NativeLiterature.ckInversePhysicalScale_unitBall_eventually
#print axioms NSEGR.NativeLiterature.ckInversePhysicalScale_unitBall_eventually
#check @NSEGR.NativeLiterature.ckLocalSolution_iff_literature
#print axioms NSEGR.NativeLiterature.ckLocalSolution_iff_literature
#check @NSEGR.NativeLiterature.literatureAnalyticCKInput_of_normalized
#print axioms NSEGR.NativeLiterature.literatureAnalyticCKInput_of_normalized
#check @NSEGR.NativeLiterature.ckTimePrimitive_hasDerivAt
#print axioms NSEGR.NativeLiterature.ckTimePrimitive_hasDerivAt
#check @NSEGR.NativeLiterature.ckTimePrimitive_initial
#print axioms NSEGR.NativeLiterature.ckTimePrimitive_initial
#check @NSEGR.NativeLiterature.ckTimePrimitive_initial_germ
#print axioms NSEGR.NativeLiterature.ckTimePrimitive_initial_germ
#check @NSEGR.NativeLiterature.ckTimePrimitive_timeDerivative_germ
#print axioms NSEGR.NativeLiterature.ckTimePrimitive_timeDerivative_germ
#check @NSEGR.NativeLiterature.ckSpatialPrimitive_eq_spaceDerivative
#print axioms NSEGR.NativeLiterature.ckSpatialPrimitive_eq_spaceDerivative
#check @NSEGR.NativeLiterature.ckSeriesSolution
#print axioms NSEGR.NativeLiterature.ckSeriesSolution
#check @NSEGR.NativeLiterature.ckSeriesSolution_analyticAt
#print axioms NSEGR.NativeLiterature.ckSeriesSolution_analyticAt
#check @NSEGR.NativeLiterature.ckSeriesSolution_initial_germ
#print axioms NSEGR.NativeLiterature.ckSeriesSolution_initial_germ
#check @NSEGR.NativeLiterature.ckSeriesSolution_timeDerivative
#print axioms NSEGR.NativeLiterature.ckSeriesSolution_timeDerivative
#check @NSEGR.NativeLiterature.ckSeriesSolution_spaceDerivative
#print axioms NSEGR.NativeLiterature.ckSeriesSolution_spaceDerivative
#check @NSEGR.NativeLiterature.ckSeriesSolution_spaceDerivative_eq
#print axioms NSEGR.NativeLiterature.ckSeriesSolution_spaceDerivative_eq
#check @NSEGR.NativeLiterature.ckScaledSolution_eq_timePrimitive
#print axioms NSEGR.NativeLiterature.ckScaledSolution_eq_timePrimitive
#check @NSEGR.NativeLiterature.ckNormalizedSolution_eq_seriesSolution
#print axioms NSEGR.NativeLiterature.ckNormalizedSolution_eq_seriesSolution
#check @NSEGR.NativeLiterature.ckSeriesSolution_isSolution
#print axioms NSEGR.NativeLiterature.ckSeriesSolution_isSolution
#check @NSEGR.NativeLiterature.ck_normalized_solution_exists
#print axioms NSEGR.NativeLiterature.ck_normalized_solution_exists
#check @NSEGR.NativeLiterature.ckSeriesSolution_fixedPoint
#print axioms NSEGR.NativeLiterature.ckSeriesSolution_fixedPoint
#check @NSEGR.NativeLiterature.ckTimeSeries_fixedPoint
#print axioms NSEGR.NativeLiterature.ckTimeSeries_fixedPoint
#check @NSEGR.NativeLiterature.ck_normalized_solution_unique
#print axioms NSEGR.NativeLiterature.ck_normalized_solution_unique
#check @NSEGR.NativeLiterature.ck_normalized_exists_unique
#print axioms NSEGR.NativeLiterature.ck_normalized_exists_unique
#check @NSEGR.NativeLiterature.ckLocal_exists_unique
#print axioms NSEGR.NativeLiterature.ckLocal_exists_unique
#check @NSEGR.NativeLiterature.literatureAnalyticCKInput_native
#print axioms NSEGR.NativeLiterature.literatureAnalyticCKInput_native
#check @NSEGR.NativeLiterature.coordinateDerivative
#print axioms NSEGR.NativeLiterature.coordinateDerivative
#check @NSEGR.NativeLiterature.derivativeSymbol
#print axioms NSEGR.NativeLiterature.derivativeSymbol
#check @NSEGR.NativeLiterature.characterPhaseCLM
#print axioms NSEGR.NativeLiterature.characterPhaseCLM
#check @NSEGR.NativeLiterature.characterPhaseCLM_apply
#print axioms NSEGR.NativeLiterature.characterPhaseCLM_apply
#check @NSEGR.NativeLiterature.characterPhaseCLM_unitVector
#print axioms NSEGR.NativeLiterature.characterPhaseCLM_unitVector
#check @NSEGR.NativeLiterature.character_eq_exp_phase
#print axioms NSEGR.NativeLiterature.character_eq_exp_phase
#check @NSEGR.NativeLiterature.character_contDiff
#print axioms NSEGR.NativeLiterature.character_contDiff
#check @NSEGR.NativeLiterature.character_hasFDerivAt
#print axioms NSEGR.NativeLiterature.character_hasFDerivAt
#check @NSEGR.NativeLiterature.character_periodic
#print axioms NSEGR.NativeLiterature.character_periodic
#check @NSEGR.NativeLiterature.character_norm
#print axioms NSEGR.NativeLiterature.character_norm
#check @NSEGR.NativeLiterature.coordinateDerivative_contDiff
#print axioms NSEGR.NativeLiterature.coordinateDerivative_contDiff
#check @NSEGR.NativeLiterature.coordinateDerivative_periodic
#print axioms NSEGR.NativeLiterature.coordinateDerivative_periodic
#check @NSEGR.NativeLiterature.partialWord_contDiff
#print axioms NSEGR.NativeLiterature.partialWord_contDiff
#check @NSEGR.NativeLiterature.partialWord_periodic
#print axioms NSEGR.NativeLiterature.partialWord_periodic
#check @NSEGR.NativeLiterature.cube_isCompact
#print axioms NSEGR.NativeLiterature.cube_isCompact
#check @NSEGR.NativeLiterature.integral_cube_coordinateDerivative_eq_zero
#print axioms NSEGR.NativeLiterature.integral_cube_coordinateDerivative_eq_zero
#check @NSEGR.NativeLiterature.fourierIntegrand_contDiff
#print axioms NSEGR.NativeLiterature.fourierIntegrand_contDiff
#check @NSEGR.NativeLiterature.fourierIntegrand_periodic
#print axioms NSEGR.NativeLiterature.fourierIntegrand_periodic
#check @NSEGR.NativeLiterature.fourierIntegrand_integrableOn
#print axioms NSEGR.NativeLiterature.fourierIntegrand_integrableOn
#check @NSEGR.NativeLiterature.fourierIntegrand_coordinateDerivative
#print axioms NSEGR.NativeLiterature.fourierIntegrand_coordinateDerivative
#check @NSEGR.NativeLiterature.fourierCoefficient_coordinateDerivative
#print axioms NSEGR.NativeLiterature.fourierCoefficient_coordinateDerivative
#check @NSEGR.NativeLiterature.fourierCoefficient_partialWord
#print axioms NSEGR.NativeLiterature.fourierCoefficient_partialWord
#check @NSEGR.NativeLiterature.fourierCoefficient_norm_le_integral_norm
#print axioms NSEGR.NativeLiterature.fourierCoefficient_norm_le_integral_norm
#check @NSEGR.NativeLiterature.frequencyWeight
#print axioms NSEGR.NativeLiterature.frequencyWeight
#check @NSEGR.NativeLiterature.productWeight
#print axioms NSEGR.NativeLiterature.productWeight
#check @NSEGR.NativeLiterature.frequencyWeight_pos
#print axioms NSEGR.NativeLiterature.frequencyWeight_pos
#check @NSEGR.NativeLiterature.productWeight_nonneg
#print axioms NSEGR.NativeLiterature.productWeight_nonneg
#check @NSEGR.NativeLiterature.summable_inverse_frequencyWeight
#print axioms NSEGR.NativeLiterature.summable_inverse_frequencyWeight
#check @NSEGR.NativeLiterature.summable_productWeight
#print axioms NSEGR.NativeLiterature.summable_productWeight
#check @NSEGR.NativeLiterature.coordinateHelmholtz
#print axioms NSEGR.NativeLiterature.coordinateHelmholtz
#check @NSEGR.NativeLiterature.productHelmholtz
#print axioms NSEGR.NativeLiterature.productHelmholtz
#check @NSEGR.NativeLiterature.coordinateHelmholtz_contDiff
#print axioms NSEGR.NativeLiterature.coordinateHelmholtz_contDiff
#check @NSEGR.NativeLiterature.coordinateHelmholtz_periodic
#print axioms NSEGR.NativeLiterature.coordinateHelmholtz_periodic
#check @NSEGR.NativeLiterature.productHelmholtz_contDiff
#print axioms NSEGR.NativeLiterature.productHelmholtz_contDiff
#check @NSEGR.NativeLiterature.productHelmholtz_periodic
#print axioms NSEGR.NativeLiterature.productHelmholtz_periodic
#check @NSEGR.NativeLiterature.fourierCoefficient_sub
#print axioms NSEGR.NativeLiterature.fourierCoefficient_sub
#check @NSEGR.NativeLiterature.one_sub_derivativeSymbol_sq
#print axioms NSEGR.NativeLiterature.one_sub_derivativeSymbol_sq
#check @NSEGR.NativeLiterature.fourierCoefficient_coordinateHelmholtz
#print axioms NSEGR.NativeLiterature.fourierCoefficient_coordinateHelmholtz
#check @NSEGR.NativeLiterature.fourierCoefficient_productHelmholtz
#print axioms NSEGR.NativeLiterature.fourierCoefficient_productHelmholtz
#check @NSEGR.NativeLiterature.productDecayConstant
#print axioms NSEGR.NativeLiterature.productDecayConstant
#check @NSEGR.NativeLiterature.productDecayConstant_nonneg
#print axioms NSEGR.NativeLiterature.productDecayConstant_nonneg
#check @NSEGR.NativeLiterature.fourierCoefficient_product_decay
#print axioms NSEGR.NativeLiterature.fourierCoefficient_product_decay
#check @NSEGR.NativeLiterature.summable_norm_fourierCoefficient
#print axioms NSEGR.NativeLiterature.summable_norm_fourierCoefficient
#check @NSEGR.NativeLiterature.summable_norm_fourierCoefficient_partialWord
#print axioms NSEGR.NativeLiterature.summable_norm_fourierCoefficient_partialWord
#check @NSEGR.NativeLiterature.literaturePiToSpace
#print axioms NSEGR.NativeLiterature.literaturePiToSpace
#check @NSEGR.NativeLiterature.literaturePiToSpace_preimage_cube
#print axioms NSEGR.NativeLiterature.literaturePiToSpace_preimage_cube
#check @NSEGR.NativeLiterature.isCompact_literatureUnitCube
#print axioms NSEGR.NativeLiterature.isCompact_literatureUnitCube
#check @NSEGR.NativeLiterature.integrableOn_literatureUnitCube_of_continuous
#print axioms NSEGR.NativeLiterature.integrableOn_literatureUnitCube_of_continuous
#check @NSEGR.NativeLiterature.volume_literatureUnitCube
#print axioms NSEGR.NativeLiterature.volume_literatureUnitCube
#check @NSEGR.NativeLiterature.literatureUnitIntervalMeasure
#print axioms NSEGR.NativeLiterature.literatureUnitIntervalMeasure
#check @NSEGR.NativeLiterature.literatureUnitProductMeasure
#print axioms NSEGR.NativeLiterature.literatureUnitProductMeasure
#check @NSEGR.NativeLiterature.literatureUnitIntervalMeasure_probability
#print axioms NSEGR.NativeLiterature.literatureUnitIntervalMeasure_probability
#check @NSEGR.NativeLiterature.literatureUnitProductMeasure_probability
#print axioms NSEGR.NativeLiterature.literatureUnitProductMeasure_probability
#check @NSEGR.NativeLiterature.literaturePiCube_eq
#print axioms NSEGR.NativeLiterature.literaturePiCube_eq
#check @NSEGR.NativeLiterature.integral_literatureUnitCube_productMeasure
#print axioms NSEGR.NativeLiterature.integral_literatureUnitCube_productMeasure
#check @NSEGR.NativeLiterature.continuous_integrable_literatureUnitProduct
#print axioms NSEGR.NativeLiterature.continuous_integrable_literatureUnitProduct
#check @NSEGR.NativeLiterature.integral_literatureUnitCube_disintegrate
#print axioms NSEGR.NativeLiterature.integral_literatureUnitCube_disintegrate
#check @NSEGR.NativeLiterature.integral_literatureUnitCube_eq_piIoc
#print axioms NSEGR.NativeLiterature.integral_literatureUnitCube_eq_piIoc
#check @NSEGR.NativeLiterature.literatureIntegerShift
#print axioms NSEGR.NativeLiterature.literatureIntegerShift
#check @NSEGR.NativeLiterature.literatureIntegerShift_apply
#print axioms NSEGR.NativeLiterature.literatureIntegerShift_apply
#check @NSEGR.NativeLiterature.literaturePeriodic_integerShift
#print axioms NSEGR.NativeLiterature.literaturePeriodic_integerShift
#check @NSEGR.NativeLiterature.literatureTorusRepresentative
#print axioms NSEGR.NativeLiterature.literatureTorusRepresentative
#check @NSEGR.NativeLiterature.literatureTorusRepresentative_mem
#print axioms NSEGR.NativeLiterature.literatureTorusRepresentative_mem
#check @NSEGR.NativeLiterature.literatureTorusRepresentative_mk_of_mem
#print axioms NSEGR.NativeLiterature.literatureTorusRepresentative_mk_of_mem
#check @NSEGR.NativeLiterature.literatureTorusRepresentative_coe
#print axioms NSEGR.NativeLiterature.literatureTorusRepresentative_coe
#check @NSEGR.NativeLiterature.literatureTorusRepresentative_periodic
#print axioms NSEGR.NativeLiterature.literatureTorusRepresentative_periodic
#check @NSEGR.NativeLiterature.literatureTorusFunction
#print axioms NSEGR.NativeLiterature.literatureTorusFunction
#check @NSEGR.NativeLiterature.literatureTorusFunction_mk
#print axioms NSEGR.NativeLiterature.literatureTorusFunction_mk
#check @NSEGR.NativeLiterature.literatureCubeProjection
#print axioms NSEGR.NativeLiterature.literatureCubeProjection
#check @NSEGR.NativeLiterature.literatureCubeProjection_continuous
#print axioms NSEGR.NativeLiterature.literatureCubeProjection_continuous
#check @NSEGR.NativeLiterature.literatureCubeProjection_surjective
#print axioms NSEGR.NativeLiterature.literatureCubeProjection_surjective
#check @NSEGR.NativeLiterature.literatureCubeProjection_isQuotientMap
#print axioms NSEGR.NativeLiterature.literatureCubeProjection_isQuotientMap
#check @NSEGR.NativeLiterature.literatureTorusFunction_continuous
#print axioms NSEGR.NativeLiterature.literatureTorusFunction_continuous
#check @NSEGR.NativeLiterature.literatureTorusContinuous
#print axioms NSEGR.NativeLiterature.literatureTorusContinuous
#check @NSEGR.NativeLiterature.literatureCharacter_eq_mFourier
#print axioms NSEGR.NativeLiterature.literatureCharacter_eq_mFourier
#check @NSEGR.NativeLiterature.literatureCharacter_norm_eq_one
#print axioms NSEGR.NativeLiterature.literatureCharacter_norm_eq_one
#check @NSEGR.NativeLiterature.literatureTorusFunction_fourierCoeff
#print axioms NSEGR.NativeLiterature.literatureTorusFunction_fourierCoeff
#check @NSEGR.NativeLiterature.literatureFourier_hasSum_of_summable_norm
#print axioms NSEGR.NativeLiterature.literatureFourier_hasSum_of_summable_norm
#check @NSEGR.NativeLiterature.literatureFourier_hasSumUniformly_of_summable_norm
#print axioms NSEGR.NativeLiterature.literatureFourier_hasSumUniformly_of_summable_norm
#check @NSEGR.NativeLiterature.fourier_partialWord_hasSumUniformly
#print axioms NSEGR.NativeLiterature.fourier_partialWord_hasSumUniformly
#check @NSEGR.NativeLiterature.literatureSmoothFourierInput_native
#print axioms NSEGR.NativeLiterature.literatureSmoothFourierInput_native
#check @NSEGR.NativeLiterature.ckTimeEquiv
#print axioms NSEGR.NativeLiterature.ckTimeEquiv
#check @NSEGR.NativeLiterature.ckJetEquiv
#print axioms NSEGR.NativeLiterature.ckJetEquiv
#check @NSEGR.NativeLiterature.ckTransformInitial
#print axioms NSEGR.NativeLiterature.ckTransformInitial
#check @NSEGR.NativeLiterature.ckTransformSolution
#print axioms NSEGR.NativeLiterature.ckTransformSolution
#check @NSEGR.NativeLiterature.ckTransformRHS
#print axioms NSEGR.NativeLiterature.ckTransformRHS
#check @NSEGR.NativeLiterature.ckTimeEquiv_apply
#print axioms NSEGR.NativeLiterature.ckTimeEquiv_apply
#check @NSEGR.NativeLiterature.ckTimeEquiv_symm_apply
#print axioms NSEGR.NativeLiterature.ckTimeEquiv_symm_apply
#check @NSEGR.NativeLiterature.ckJetEquiv_apply
#print axioms NSEGR.NativeLiterature.ckJetEquiv_apply
#check @NSEGR.NativeLiterature.ckJetEquiv_symm_apply
#print axioms NSEGR.NativeLiterature.ckJetEquiv_symm_apply
#check @NSEGR.NativeLiterature.ckArrowCongr_inverse
#print axioms NSEGR.NativeLiterature.ckArrowCongr_inverse
#check @NSEGR.NativeLiterature.ckTransformInitial_fderiv
#print axioms NSEGR.NativeLiterature.ckTransformInitial_fderiv
#check @NSEGR.NativeLiterature.ckTransformSolution_spaceDerivative
#print axioms NSEGR.NativeLiterature.ckTransformSolution_spaceDerivative
#check @NSEGR.NativeLiterature.ckTransformSolution_timeDerivative
#print axioms NSEGR.NativeLiterature.ckTransformSolution_timeDerivative
#check @NSEGR.NativeLiterature.ckTransformInitial_analyticAt
#print axioms NSEGR.NativeLiterature.ckTransformInitial_analyticAt
#check @NSEGR.NativeLiterature.ckTransformSolution_analyticAt
#print axioms NSEGR.NativeLiterature.ckTransformSolution_analyticAt
#check @NSEGR.NativeLiterature.ckTransformInitial_jet
#print axioms NSEGR.NativeLiterature.ckTransformInitial_jet
#check @NSEGR.NativeLiterature.ckTransformRHS_analyticAt
#print axioms NSEGR.NativeLiterature.ckTransformRHS_analyticAt
#check @NSEGR.NativeLiterature.ckTransformSolution_isSolution
#print axioms NSEGR.NativeLiterature.ckTransformSolution_isSolution
#check @NSEGR.NativeLiterature.ckTransformInitial_inverse
#print axioms NSEGR.NativeLiterature.ckTransformInitial_inverse
#check @NSEGR.NativeLiterature.ckTransformSolution_inverse
#print axioms NSEGR.NativeLiterature.ckTransformSolution_inverse
#check @NSEGR.NativeLiterature.ckTransformRHS_inverse
#print axioms NSEGR.NativeLiterature.ckTransformRHS_inverse
#check @NSEGR.NativeLiterature.ckTransformSolution_germ
#print axioms NSEGR.NativeLiterature.ckTransformSolution_germ
#check @NSEGR.NativeLiterature.ckLocal_exists_unique_of_literatureCK
#print axioms NSEGR.NativeLiterature.ckLocal_exists_unique_of_literatureCK
#check @NSEGR.NativeLiterature.coordDeriv
#print axioms NSEGR.NativeLiterature.coordDeriv
#check @NSEGR.NativeLiterature.coordDeriv_scalar
#print axioms NSEGR.NativeLiterature.coordDeriv_scalar
#check @NSEGR.NativeLiterature.coordDeriv_const
#print axioms NSEGR.NativeLiterature.coordDeriv_const
#check @NSEGR.NativeLiterature.coordDeriv_add
#print axioms NSEGR.NativeLiterature.coordDeriv_add
#check @NSEGR.NativeLiterature.coordDeriv_sub
#print axioms NSEGR.NativeLiterature.coordDeriv_sub
#check @NSEGR.NativeLiterature.coordDeriv_sum
#print axioms NSEGR.NativeLiterature.coordDeriv_sum
#check @NSEGR.NativeLiterature.analyticAt_coordDeriv
#print axioms NSEGR.NativeLiterature.analyticAt_coordDeriv
#check @NSEGR.NativeLiterature.coordDeriv_coordDeriv
#print axioms NSEGR.NativeLiterature.coordDeriv_coordDeriv
#check @NSEGR.NativeLiterature.coordDeriv_commute
#print axioms NSEGR.NativeLiterature.coordDeriv_commute
#check @NSEGR.NativeLiterature.coordDeriv_congr_germ
#print axioms NSEGR.NativeLiterature.coordDeriv_congr_germ
#check @NSEGR.NativeLiterature.matrixCommutator
#print axioms NSEGR.NativeLiterature.matrixCommutator
#check @NSEGR.NativeLiterature.matrixCommutator_skew
#print axioms NSEGR.NativeLiterature.matrixCommutator_skew
#check @NSEGR.NativeLiterature.matrixCommutator_jacobi
#print axioms NSEGR.NativeLiterature.matrixCommutator_jacobi
#check @NSEGR.NativeLiterature.coordDeriv_matrix_mul
#print axioms NSEGR.NativeLiterature.coordDeriv_matrix_mul
#check @NSEGR.NativeLiterature.analyticAt_matrixCommutator
#print axioms NSEGR.NativeLiterature.analyticAt_matrixCommutator
#check @NSEGR.NativeLiterature.coordDeriv_matrixCommutator
#print axioms NSEGR.NativeLiterature.coordDeriv_matrixCommutator
#check @NSEGR.NativeLiterature.connectionCurvature
#print axioms NSEGR.NativeLiterature.connectionCurvature
#check @NSEGR.NativeLiterature.analyticAt_connectionCurvature
#print axioms NSEGR.NativeLiterature.analyticAt_connectionCurvature
#check @NSEGR.NativeLiterature.coordDeriv_connectionCurvature
#print axioms NSEGR.NativeLiterature.coordDeriv_connectionCurvature
#check @NSEGR.NativeLiterature.connection_differential_bianchi
#print axioms NSEGR.NativeLiterature.connection_differential_bianchi
#check @NSEGR.NativeLiterature.metricConnection
#print axioms NSEGR.NativeLiterature.metricConnection
#check @NSEGR.NativeLiterature.loweredConnection
#print axioms NSEGR.NativeLiterature.loweredConnection
#check @NSEGR.NativeLiterature.metricConnection_eq_inverse_mul
#print axioms NSEGR.NativeLiterature.metricConnection_eq_inverse_mul
#check @NSEGR.NativeLiterature.coordDeriv_matrix_entry
#print axioms NSEGR.NativeLiterature.coordDeriv_matrix_entry
#check @NSEGR.NativeLiterature.bulkPartial_entry_symm
#print axioms NSEGR.NativeLiterature.bulkPartial_entry_symm
#check @NSEGR.NativeLiterature.loweredConnection_add_transpose
#print axioms NSEGR.NativeLiterature.loweredConnection_add_transpose
#check @NSEGR.NativeLiterature.metric_mul_connection
#print axioms NSEGR.NativeLiterature.metric_mul_connection
#check @NSEGR.NativeLiterature.metric_connection_compatible
#print axioms NSEGR.NativeLiterature.metric_connection_compatible
#check @NSEGR.NativeLiterature.analyticAt_bulkMatrix_inverse
#print axioms NSEGR.NativeLiterature.analyticAt_bulkMatrix_inverse
#check @NSEGR.NativeLiterature.analyticAt_nativeChristoffel
#print axioms NSEGR.NativeLiterature.analyticAt_nativeChristoffel
#check @NSEGR.NativeLiterature.analyticAt_metricConnection
#print axioms NSEGR.NativeLiterature.analyticAt_metricConnection
#check @NSEGR.NativeLiterature.analyticAt_nativeRicci
#print axioms NSEGR.NativeLiterature.analyticAt_nativeRicci
#check @NSEGR.NativeLiterature.metricConnection_torsion
#print axioms NSEGR.NativeLiterature.metricConnection_torsion
#check @NSEGR.NativeLiterature.metricCurvature
#print axioms NSEGR.NativeLiterature.metricCurvature
#check @NSEGR.NativeLiterature.analyticAt_metricCurvature
#print axioms NSEGR.NativeLiterature.analyticAt_metricCurvature
#check @NSEGR.NativeLiterature.metricCurvature_skew_last
#print axioms NSEGR.NativeLiterature.metricCurvature_skew_last
#check @NSEGR.NativeLiterature.metricCurvature_differential_bianchi
#print axioms NSEGR.NativeLiterature.metricCurvature_differential_bianchi
#check @NSEGR.NativeLiterature.connectionCurvature_entry
#print axioms NSEGR.NativeLiterature.connectionCurvature_entry
#check @NSEGR.NativeLiterature.connection_curvature_first_bianchi
#print axioms NSEGR.NativeLiterature.connection_curvature_first_bianchi
#check @NSEGR.NativeLiterature.metric_curvature_first_bianchi
#print axioms NSEGR.NativeLiterature.metric_curvature_first_bianchi
#check @NSEGR.NativeLiterature.bulkTransposeCLM
#print axioms NSEGR.NativeLiterature.bulkTransposeCLM
#check @NSEGR.NativeLiterature.analyticAt_bulkTranspose
#print axioms NSEGR.NativeLiterature.analyticAt_bulkTranspose
#check @NSEGR.NativeLiterature.coordDeriv_bulkTranspose
#print axioms NSEGR.NativeLiterature.coordDeriv_bulkTranspose
#check @NSEGR.NativeLiterature.coordDeriv_metric_compatibility
#print axioms NSEGR.NativeLiterature.coordDeriv_metric_compatibility
#check @NSEGR.NativeLiterature.metric_curvature_skew_lower
#print axioms NSEGR.NativeLiterature.metric_curvature_skew_lower
#check @NSEGR.NativeLiterature.loweredCurvature
#print axioms NSEGR.NativeLiterature.loweredCurvature
#check @NSEGR.NativeLiterature.loweredCurvature_skew_first
#print axioms NSEGR.NativeLiterature.loweredCurvature_skew_first
#check @NSEGR.NativeLiterature.loweredCurvature_skew_last
#print axioms NSEGR.NativeLiterature.loweredCurvature_skew_last
#check @NSEGR.NativeLiterature.loweredCurvature_first_bianchi
#print axioms NSEGR.NativeLiterature.loweredCurvature_first_bianchi
#check @NSEGR.NativeLiterature.loweredCurvature_pair_symmetry
#print axioms NSEGR.NativeLiterature.loweredCurvature_pair_symmetry
#check @NSEGR.NativeLiterature.nativeRicci_eq_curvature_trace
#print axioms NSEGR.NativeLiterature.nativeRicci_eq_curvature_trace
#check @NSEGR.NativeLiterature.nativeRicci_eq_lowered_contraction
#print axioms NSEGR.NativeLiterature.nativeRicci_eq_lowered_contraction
#check @NSEGR.NativeLiterature.nativeRicci_symmetric
#print axioms NSEGR.NativeLiterature.nativeRicci_symmetric
#check @NSEGR.NativeLiterature.MetricSkew
#print axioms NSEGR.NativeLiterature.MetricSkew
#check @NSEGR.NativeLiterature.MetricSkew.zero
#print axioms NSEGR.NativeLiterature.MetricSkew.zero
#check @NSEGR.NativeLiterature.MetricSkew.add
#print axioms NSEGR.NativeLiterature.MetricSkew.add
#check @NSEGR.NativeLiterature.MetricSkew.neg
#print axioms NSEGR.NativeLiterature.MetricSkew.neg
#check @NSEGR.NativeLiterature.MetricSkew.sub
#print axioms NSEGR.NativeLiterature.MetricSkew.sub
#check @NSEGR.NativeLiterature.MetricSkew.smul
#print axioms NSEGR.NativeLiterature.MetricSkew.smul
#check @NSEGR.NativeLiterature.MetricSkew.sum
#print axioms NSEGR.NativeLiterature.MetricSkew.sum
#check @NSEGR.NativeLiterature.MetricSkew.connectionDerivative
#print axioms NSEGR.NativeLiterature.MetricSkew.connectionDerivative
#check @NSEGR.NativeLiterature.covariantCurvature
#print axioms NSEGR.NativeLiterature.covariantCurvature
#check @NSEGR.NativeLiterature.covariantCurvature_metricSkew
#print axioms NSEGR.NativeLiterature.covariantCurvature_metricSkew
#check @NSEGR.NativeLiterature.covariantCurvature_first_form_skew
#print axioms NSEGR.NativeLiterature.covariantCurvature_first_form_skew
#check @NSEGR.NativeLiterature.covariantCurvature_bianchi
#print axioms NSEGR.NativeLiterature.covariantCurvature_bianchi
#check @NSEGR.NativeLiterature.covariantRicci
#print axioms NSEGR.NativeLiterature.covariantRicci
#check @NSEGR.NativeLiterature.curvature_trace_algebra
#print axioms NSEGR.NativeLiterature.curvature_trace_algebra
#check @NSEGR.NativeLiterature.coordDeriv_nativeRicci_entry
#print axioms NSEGR.NativeLiterature.coordDeriv_nativeRicci_entry
#check @NSEGR.NativeLiterature.covariantRicci_eq_curvature_trace
#print axioms NSEGR.NativeLiterature.covariantRicci_eq_curvature_trace
#check @NSEGR.NativeLiterature.covariantRicci_first_contracted_bianchi
#print axioms NSEGR.NativeLiterature.covariantRicci_first_contracted_bianchi
#check @NSEGR.NativeLiterature.coordDeriv_bulkInverse
#print axioms NSEGR.NativeLiterature.coordDeriv_bulkInverse
#check @NSEGR.NativeLiterature.coordDeriv_inverse_compatible
#print axioms NSEGR.NativeLiterature.coordDeriv_inverse_compatible
#check @NSEGR.NativeLiterature.scalar_contraction_derivative_algebra
#print axioms NSEGR.NativeLiterature.scalar_contraction_derivative_algebra
#check @NSEGR.NativeLiterature.bulkPartial_scalarCurvature
#print axioms NSEGR.NativeLiterature.bulkPartial_scalarCurvature
#check @NSEGR.NativeLiterature.MetricSkew.inverse_pairing
#print axioms NSEGR.NativeLiterature.MetricSkew.inverse_pairing
#check @NSEGR.NativeLiterature.metricSkew_double_contraction
#print axioms NSEGR.NativeLiterature.metricSkew_double_contraction
#check @NSEGR.NativeLiterature.native_contracted_bianchi
#print axioms NSEGR.NativeLiterature.native_contracted_bianchi
#check @NSEGR.NativeLiterature.analyticAt_gaussianBlockMetric
#print axioms NSEGR.NativeLiterature.analyticAt_gaussianBlockMetric
#check @NSEGR.NativeLiterature.gaussianBlockMetric_symmetric
#print axioms NSEGR.NativeLiterature.gaussianBlockMetric_symmetric
#check @NSEGR.NativeLiterature.gaussianBlockMetric_unit
#print axioms NSEGR.NativeLiterature.gaussianBlockMetric_unit
#check @NSEGR.NativeLiterature.gaussianSecondForm_symmetric
#print axioms NSEGR.NativeLiterature.gaussianSecondForm_symmetric
#check @NSEGR.NativeLiterature.gaussianRicci_symmetric_eventually
#print axioms NSEGR.NativeLiterature.gaussianRicci_symmetric_eventually
#check @NSEGR.NativeLiterature.gaussianResidualA
#print axioms NSEGR.NativeLiterature.gaussianResidualA
#check @NSEGR.NativeLiterature.gaussianResidualC
#print axioms NSEGR.NativeLiterature.gaussianResidualC
#check @NSEGR.NativeLiterature.gaussianKappa
#print axioms NSEGR.NativeLiterature.gaussianKappa
#check @NSEGR.NativeLiterature.gaussianResidualDivergence
#print axioms NSEGR.NativeLiterature.gaussianResidualDivergence
#check @NSEGR.NativeLiterature.nativeRicciDivergence
#print axioms NSEGR.NativeLiterature.nativeRicciDivergence
#check @NSEGR.NativeLiterature.gaussian_scalarCurvature_eq_residual
#print axioms NSEGR.NativeLiterature.gaussian_scalarCurvature_eq_residual
#check @NSEGR.NativeLiterature.gaussian_scalarCurvature_derivative
#print axioms NSEGR.NativeLiterature.gaussian_scalarCurvature_derivative
#check @NSEGR.NativeLiterature.gaussianRicciDivergence_split
#print axioms NSEGR.NativeLiterature.gaussianRicciDivergence_split
#check @NSEGR.NativeLiterature.gaussianCovariantRicci_rrr
#print axioms NSEGR.NativeLiterature.gaussianCovariantRicci_rrr
#check @NSEGR.NativeLiterature.gaussianCovariantRicci_rra
#print axioms NSEGR.NativeLiterature.gaussianCovariantRicci_rra
#check @NSEGR.NativeLiterature.gaussianCovariantRicci_abr
#print axioms NSEGR.NativeLiterature.gaussianCovariantRicci_abr
#check @NSEGR.NativeLiterature.gaussianCovariantRicci_abi
#print axioms NSEGR.NativeLiterature.gaussianCovariantRicci_abi
#check @NSEGR.NativeLiterature.gaussianSecondForm_trace_contraction
#print axioms NSEGR.NativeLiterature.gaussianSecondForm_trace_contraction
#check @NSEGR.NativeLiterature.gaussianShape_contraction
#print axioms NSEGR.NativeLiterature.gaussianShape_contraction
#check @NSEGR.NativeLiterature.gaussianRicciDivergence_normal
#print axioms NSEGR.NativeLiterature.gaussianRicciDivergence_normal
#check @NSEGR.NativeLiterature.gaussianRicciDivergence_tangential
#print axioms NSEGR.NativeLiterature.gaussianRicciDivergence_tangential
#check @NSEGR.NativeLiterature.gaussian_constraint_evolution
#print axioms NSEGR.NativeLiterature.gaussian_constraint_evolution
#check @NSEGR.NativeLiterature.GaussianBase
#print axioms NSEGR.NativeLiterature.GaussianBase
#check @NSEGR.NativeLiterature.GaussianState
#print axioms NSEGR.NativeLiterature.GaussianState
#check @NSEGR.NativeLiterature.gaussianBaseBasis
#print axioms NSEGR.NativeLiterature.gaussianBaseBasis
#check @NSEGR.NativeLiterature.gaussianBulkCoordinates
#print axioms NSEGR.NativeLiterature.gaussianBulkCoordinates
#check @NSEGR.NativeLiterature.gaussianSplitCoordinates
#print axioms NSEGR.NativeLiterature.gaussianSplitCoordinates
#check @NSEGR.NativeLiterature.gaussianBulkCoordinates_apply
#print axioms NSEGR.NativeLiterature.gaussianBulkCoordinates_apply
#check @NSEGR.NativeLiterature.gaussianSplitCoordinates_bulkPoint
#print axioms NSEGR.NativeLiterature.gaussianSplitCoordinates_bulkPoint
#check @NSEGR.NativeLiterature.gaussianBulkCoordinates_split
#print axioms NSEGR.NativeLiterature.gaussianBulkCoordinates_split
#check @NSEGR.NativeLiterature.gaussianSymmetrize
#print axioms NSEGR.NativeLiterature.gaussianSymmetrize
#check @NSEGR.NativeLiterature.gaussianSymmetrize_apply
#print axioms NSEGR.NativeLiterature.gaussianSymmetrize_apply
#check @NSEGR.NativeLiterature.gaussianSymmetrize_isSymm
#print axioms NSEGR.NativeLiterature.gaussianSymmetrize_isSymm
#check @NSEGR.NativeLiterature.gaussianSymmetrize_eq_of_isSymm
#print axioms NSEGR.NativeLiterature.gaussianSymmetrize_eq_of_isSymm
#check @NSEGR.NativeLiterature.gaussianStateMetric
#print axioms NSEGR.NativeLiterature.gaussianStateMetric
#check @NSEGR.NativeLiterature.gaussianStateVelocity
#print axioms NSEGR.NativeLiterature.gaussianStateVelocity
#check @NSEGR.NativeLiterature.gaussianStateSpatial
#print axioms NSEGR.NativeLiterature.gaussianStateSpatial
#check @NSEGR.NativeLiterature.gaussianInitialState
#print axioms NSEGR.NativeLiterature.gaussianInitialState
#check @NSEGR.NativeLiterature.gaussianInitialState_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianInitialState_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetMetric
#print axioms NSEGR.NativeLiterature.gaussianJetMetric
#check @NSEGR.NativeLiterature.gaussianJetVelocity
#print axioms NSEGR.NativeLiterature.gaussianJetVelocity
#check @NSEGR.NativeLiterature.gaussianJetSpatial
#print axioms NSEGR.NativeLiterature.gaussianJetSpatial
#check @NSEGR.NativeLiterature.gaussianJetSecond
#print axioms NSEGR.NativeLiterature.gaussianJetSecond
#check @NSEGR.NativeLiterature.gaussianJetConnection
#print axioms NSEGR.NativeLiterature.gaussianJetConnection
#check @NSEGR.NativeLiterature.gaussianJetInverseDerivative
#print axioms NSEGR.NativeLiterature.gaussianJetInverseDerivative
#check @NSEGR.NativeLiterature.gaussianJetConnectionDerivative
#print axioms NSEGR.NativeLiterature.gaussianJetConnectionDerivative
#check @NSEGR.NativeLiterature.gaussianJetRicci
#print axioms NSEGR.NativeLiterature.gaussianJetRicci
#check @NSEGR.NativeLiterature.gaussianJetTrace
#print axioms NSEGR.NativeLiterature.gaussianJetTrace
#check @NSEGR.NativeLiterature.gaussianJetMetric_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetMetric_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetVelocity_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetVelocity_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetSpatial_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetSpatial_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetSecond_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetSecond_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetInverse_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetInverse_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetConnection_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetConnection_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetInverseDerivative_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetInverseDerivative_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetConnectionDerivative_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetConnectionDerivative_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetRicci_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetRicci_analyticAt
#check @NSEGR.NativeLiterature.gaussianJetTrace_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianJetTrace_analyticAt
#check @NSEGR.NativeLiterature.gaussianCKRHS
#print axioms NSEGR.NativeLiterature.gaussianCKRHS
#check @NSEGR.NativeLiterature.gaussianCKRHS_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianCKRHS_analyticAt
#check @NSEGR.NativeLiterature.gaussianCKRHS_metric
#print axioms NSEGR.NativeLiterature.gaussianCKRHS_metric
#check @NSEGR.NativeLiterature.gaussianCKRHS_velocity_symmetric
#print axioms NSEGR.NativeLiterature.gaussianCKRHS_velocity_symmetric
#check @NSEGR.NativeLiterature.gaussianCKRHS_spatial
#print axioms NSEGR.NativeLiterature.gaussianCKRHS_spatial
#check @NSEGR.NativeLiterature.GaussianEvolutionStateSolution
#print axioms NSEGR.NativeLiterature.GaussianEvolutionStateSolution
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric
#check @NSEGR.NativeLiterature.gaussianStateSolutionVelocity
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionVelocity
#check @NSEGR.NativeLiterature.gaussianStateSolutionSpatial
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionSpatial
#check @NSEGR.NativeLiterature.gaussianEta_determinant
#print axioms NSEGR.NativeLiterature.gaussianEta_determinant
#check @NSEGR.NativeLiterature.gaussianEta_isUnit
#print axioms NSEGR.NativeLiterature.gaussianEta_isUnit
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_analyticAt
#check @NSEGR.NativeLiterature.gaussianStateSolutionVelocity_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionVelocity_analyticAt
#check @NSEGR.NativeLiterature.gaussianStateSolutionSpatial_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionSpatial_analyticAt
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_induced
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_induced
#check @NSEGR.NativeLiterature.gaussianStateSolutionVelocity_initial
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionVelocity_initial
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_nondegenerate
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_nondegenerate
#check @NSEGR.NativeLiterature.GaussianEvolutionGerm
#print axioms NSEGR.NativeLiterature.GaussianEvolutionGerm
#check @NSEGR.NativeLiterature.GaussianEvolutionGerm.eventually_at_boundary
#print axioms NSEGR.NativeLiterature.GaussianEvolutionGerm.eventually_at_boundary
#check @NSEGR.NativeLiterature.flatBoundaryGerm_eventually
#print axioms NSEGR.NativeLiterature.flatBoundaryGerm_eventually
#check @NSEGR.NativeLiterature.gaussianEvolution_tangential_jet_zero
#print axioms NSEGR.NativeLiterature.gaussianEvolution_tangential_jet_zero
#check @NSEGR.NativeLiterature.gaussianEvolution_connection_zero
#print axioms NSEGR.NativeLiterature.gaussianEvolution_connection_zero
#check @NSEGR.NativeLiterature.gaussianEvolution_connection_tangent_zero
#print axioms NSEGR.NativeLiterature.gaussianEvolution_connection_tangent_zero
#check @NSEGR.NativeLiterature.gaussianResidualA_flat_of_tangential
#print axioms NSEGR.NativeLiterature.gaussianResidualA_flat_of_tangential
#check @NSEGR.NativeLiterature.gaussianResidualA_initial_eq_hamiltonian
#print axioms NSEGR.NativeLiterature.gaussianResidualA_initial_eq_hamiltonian
#check @NSEGR.NativeLiterature.gaussianEvolution_shape_boundary_derivative
#print axioms NSEGR.NativeLiterature.gaussianEvolution_shape_boundary_derivative
#check @NSEGR.NativeLiterature.gaussianResidualC_initial_eq_codazzi
#print axioms NSEGR.NativeLiterature.gaussianResidualC_initial_eq_codazzi
#check @NSEGR.NativeLiterature.gaussian_constraints_initial_zero
#print axioms NSEGR.NativeLiterature.gaussian_constraints_initial_zero
#check @NSEGR.NativeLiterature.gaussian_constraints_initial_zero_germ
#print axioms NSEGR.NativeLiterature.gaussian_constraints_initial_zero_germ
#check @NSEGR.NativeLiterature.gaussianDirectional
#print axioms NSEGR.NativeLiterature.gaussianDirectional
#check @NSEGR.NativeLiterature.gaussianDirectional_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianDirectional_analyticAt
#check @NSEGR.NativeLiterature.gaussianDirectional_clm
#print axioms NSEGR.NativeLiterature.gaussianDirectional_clm
#check @NSEGR.NativeLiterature.gaussianDirectional_comp_linear
#print axioms NSEGR.NativeLiterature.gaussianDirectional_comp_linear
#check @NSEGR.NativeLiterature.gaussianDirectional_twice
#print axioms NSEGR.NativeLiterature.gaussianDirectional_twice
#check @NSEGR.NativeLiterature.gaussianDirectional_commute
#print axioms NSEGR.NativeLiterature.gaussianDirectional_commute
#check @NSEGR.NativeLiterature.gaussianDirectional_germ
#print axioms NSEGR.NativeLiterature.gaussianDirectional_germ
#check @NSEGR.NativeLiterature.gaussianTimeDerivative_clm
#print axioms NSEGR.NativeLiterature.gaussianTimeDerivative_clm
#check @NSEGR.NativeLiterature.gaussianSpaceDerivative_eq_full
#print axioms NSEGR.NativeLiterature.gaussianSpaceDerivative_eq_full
#check @NSEGR.NativeLiterature.gaussianGerm_eq_of_timeDerivative_eq
#print axioms NSEGR.NativeLiterature.gaussianGerm_eq_of_timeDerivative_eq
#check @NSEGR.NativeLiterature.gaussianBulkCoordinates_radial
#print axioms NSEGR.NativeLiterature.gaussianBulkCoordinates_radial
#check @NSEGR.NativeLiterature.gaussianBulkCoordinates_tangent
#print axioms NSEGR.NativeLiterature.gaussianBulkCoordinates_tangent
#check @NSEGR.NativeLiterature.gaussianSplitCoordinates_bulkCoordinates
#print axioms NSEGR.NativeLiterature.gaussianSplitCoordinates_bulkCoordinates
#check @NSEGR.NativeLiterature.gaussianSplitCoordinates_radial
#print axioms NSEGR.NativeLiterature.gaussianSplitCoordinates_radial
#check @NSEGR.NativeLiterature.gaussianSplitCoordinates_tangent
#print axioms NSEGR.NativeLiterature.gaussianSplitCoordinates_tangent
#check @NSEGR.NativeLiterature.gaussianBulk_timeDerivative
#print axioms NSEGR.NativeLiterature.gaussianBulk_timeDerivative
#check @NSEGR.NativeLiterature.gaussianBulk_spaceDerivative
#print axioms NSEGR.NativeLiterature.gaussianBulk_spaceDerivative
#check @NSEGR.NativeLiterature.gaussianMetricComponent
#print axioms NSEGR.NativeLiterature.gaussianMetricComponent
#check @NSEGR.NativeLiterature.gaussianVelocityComponent
#print axioms NSEGR.NativeLiterature.gaussianVelocityComponent
#check @NSEGR.NativeLiterature.gaussianSpatialComponent
#print axioms NSEGR.NativeLiterature.gaussianSpatialComponent
#check @NSEGR.NativeLiterature.gaussianMetricComponent_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianMetricComponent_analyticAt
#check @NSEGR.NativeLiterature.gaussianVelocityComponent_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianVelocityComponent_analyticAt
#check @NSEGR.NativeLiterature.gaussianSpatialComponent_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianSpatialComponent_analyticAt
#check @NSEGR.NativeLiterature.gaussianMetricComponent_timeDerivative
#print axioms NSEGR.NativeLiterature.gaussianMetricComponent_timeDerivative
#check @NSEGR.NativeLiterature.gaussianMetricComponent_radial
#print axioms NSEGR.NativeLiterature.gaussianMetricComponent_radial
#check @NSEGR.NativeLiterature.gaussianSpatialComponent_timeDerivative
#print axioms NSEGR.NativeLiterature.gaussianSpatialComponent_timeDerivative
#check @NSEGR.NativeLiterature.gaussianSymmetryDefect
#print axioms NSEGR.NativeLiterature.gaussianSymmetryDefect
#check @NSEGR.NativeLiterature.gaussianSymmetryDefect_eq_zero
#print axioms NSEGR.NativeLiterature.gaussianSymmetryDefect_eq_zero
#check @NSEGR.NativeLiterature.gaussianSymmetryDefect_zero_iff
#print axioms NSEGR.NativeLiterature.gaussianSymmetryDefect_zero_iff
#check @NSEGR.NativeLiterature.gaussianVelocityComponent_symmetric
#print axioms NSEGR.NativeLiterature.gaussianVelocityComponent_symmetric
#check @NSEGR.NativeLiterature.gaussianMetricComponent_symmetric
#print axioms NSEGR.NativeLiterature.gaussianMetricComponent_symmetric
#check @NSEGR.NativeLiterature.gaussianSpatialComponent_eq_metricDerivative
#print axioms NSEGR.NativeLiterature.gaussianSpatialComponent_eq_metricDerivative
#check @NSEGR.NativeLiterature.gaussianSplit_tendsto
#print axioms NSEGR.NativeLiterature.gaussianSplit_tendsto
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_radial
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_radial
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_spatial
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_spatial
#check @NSEGR.NativeLiterature.gaussianStateSolutionSpatial_radial
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionSpatial_radial
#check @NSEGR.NativeLiterature.gaussianStateSolutionVelocity_symmetric
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionVelocity_symmetric
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_symmetric
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_symmetric
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_secondForm
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_secondForm
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_boundary_match
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_boundary_match
#check @NSEGR.NativeLiterature.GaussianConstraintState
#print axioms NSEGR.NativeLiterature.GaussianConstraintState
#check @NSEGR.NativeLiterature.gaussianResidualState
#print axioms NSEGR.NativeLiterature.gaussianResidualState
#check @NSEGR.NativeLiterature.gaussianConstraintSolution
#print axioms NSEGR.NativeLiterature.gaussianConstraintSolution
#check @NSEGR.NativeLiterature.gaussianConstraintRHS
#print axioms NSEGR.NativeLiterature.gaussianConstraintRHS
#check @NSEGR.NativeLiterature.analyticAt_gaussianResidualState
#print axioms NSEGR.NativeLiterature.analyticAt_gaussianResidualState
#check @NSEGR.NativeLiterature.analyticAt_gaussianKappa
#print axioms NSEGR.NativeLiterature.analyticAt_gaussianKappa
#check @NSEGR.NativeLiterature.gaussianConstraintRHS_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianConstraintRHS_analyticAt
#check @NSEGR.NativeLiterature.gaussianResidualState_derivative_fst
#print axioms NSEGR.NativeLiterature.gaussianResidualState_derivative_fst
#check @NSEGR.NativeLiterature.gaussianResidualState_derivative_snd
#print axioms NSEGR.NativeLiterature.gaussianResidualState_derivative_snd
#check @NSEGR.NativeLiterature.gaussianConstraintRHS_zero
#print axioms NSEGR.NativeLiterature.gaussianConstraintRHS_zero
#check @NSEGR.NativeLiterature.gaussianConstraint_zero_solution
#print axioms NSEGR.NativeLiterature.gaussianConstraint_zero_solution
#check @NSEGR.NativeLiterature.gaussianConstraintSolution_isSolution
#print axioms NSEGR.NativeLiterature.gaussianConstraintSolution_isSolution
#check @NSEGR.NativeLiterature.gaussian_constraints_zero_germ
#print axioms NSEGR.NativeLiterature.gaussian_constraints_zero_germ
#check @NSEGR.NativeLiterature.gaussianEvolution_vacuum_of_constraints
#print axioms NSEGR.NativeLiterature.gaussianEvolution_vacuum_of_constraints
#check @NSEGR.NativeLiterature.coordDeriv_tensor_entry
#print axioms NSEGR.NativeLiterature.coordDeriv_tensor_entry
#check @NSEGR.NativeLiterature.coordDeriv_tensor_second_entry
#print axioms NSEGR.NativeLiterature.coordDeriv_tensor_second_entry
#check @NSEGR.NativeLiterature.coordDeriv_tensorInverse
#print axioms NSEGR.NativeLiterature.coordDeriv_tensorInverse
#check @NSEGR.NativeLiterature.GaussianJetCompatible
#print axioms NSEGR.NativeLiterature.GaussianJetCompatible
#check @NSEGR.NativeLiterature.gaussianJetConnection_eq_native
#print axioms NSEGR.NativeLiterature.gaussianJetConnection_eq_native
#check @NSEGR.NativeLiterature.gaussianJetInverseDerivative_eq_native
#print axioms NSEGR.NativeLiterature.gaussianJetInverseDerivative_eq_native
#check @NSEGR.NativeLiterature.gaussianJetConnectionDerivative_eq_native
#print axioms NSEGR.NativeLiterature.gaussianJetConnectionDerivative_eq_native
#check @NSEGR.NativeLiterature.gaussianIntrinsicRicci
#print axioms NSEGR.NativeLiterature.gaussianIntrinsicRicci
#check @NSEGR.NativeLiterature.gaussianJetRicci_eq_native
#print axioms NSEGR.NativeLiterature.gaussianJetRicci_eq_native
#check @NSEGR.NativeLiterature.gaussianStateSolutionJet
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionJet
#check @NSEGR.NativeLiterature.gaussianStateSolutionVelocity_radial
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionVelocity_radial
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_secondRadial
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_secondRadial
#check @NSEGR.NativeLiterature.gaussianStateSolutionJet_second_derivative
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionJet_second_derivative
#check @NSEGR.NativeLiterature.gaussianStateSolutionJet_compatible
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionJet_compatible
#check @NSEGR.NativeLiterature.gaussianEvolutionState_exists_unique
#print axioms NSEGR.NativeLiterature.gaussianEvolutionState_exists_unique
#check @NSEGR.NativeLiterature.gaussianExtrinsicRicci_algebra
#print axioms NSEGR.NativeLiterature.gaussianExtrinsicRicci_algebra
#check @NSEGR.NativeLiterature.gaussianSecondForm_eq_half_radial
#print axioms NSEGR.NativeLiterature.gaussianSecondForm_eq_half_radial
#check @NSEGR.NativeLiterature.gaussianSecondForm_radial
#print axioms NSEGR.NativeLiterature.gaussianSecondForm_radial
#check @NSEGR.NativeLiterature.gaussianShapeOperator_eq_mul
#print axioms NSEGR.NativeLiterature.gaussianShapeOperator_eq_mul
#check @NSEGR.NativeLiterature.coordDeriv_tensor_symmetric
#print axioms NSEGR.NativeLiterature.coordDeriv_tensor_symmetric
#check @NSEGR.NativeLiterature.coordDeriv_tensor_second_symmetric
#print axioms NSEGR.NativeLiterature.coordDeriv_tensor_second_symmetric
#check @NSEGR.NativeLiterature.gaussianTangentialNativeRicci
#print axioms NSEGR.NativeLiterature.gaussianTangentialNativeRicci
#check @NSEGR.NativeLiterature.gaussianTangentialNativeRicci_symmetric
#print axioms NSEGR.NativeLiterature.gaussianTangentialNativeRicci_symmetric
#check @NSEGR.NativeLiterature.gaussianTangentialRicci_eq_intrinsic_extrinsic
#print axioms NSEGR.NativeLiterature.gaussianTangentialRicci_eq_intrinsic_extrinsic
#check @NSEGR.NativeLiterature.gaussianJet_rawAcceleration_eq_native
#print axioms NSEGR.NativeLiterature.gaussianJet_rawAcceleration_eq_native
#check @NSEGR.NativeLiterature.gaussianCKRHS_velocity_eq_native
#print axioms NSEGR.NativeLiterature.gaussianCKRHS_velocity_eq_native
#check @NSEGR.NativeLiterature.gaussianTangentialVacuum_iff_CKRHS
#print axioms NSEGR.NativeLiterature.gaussianTangentialVacuum_iff_CKRHS
#check @NSEGR.NativeLiterature.gaussianRecoveredState
#print axioms NSEGR.NativeLiterature.gaussianRecoveredState
#check @NSEGR.NativeLiterature.gaussianRecoveredJet
#print axioms NSEGR.NativeLiterature.gaussianRecoveredJet
#check @NSEGR.NativeLiterature.gaussianState_eq_of_components
#print axioms NSEGR.NativeLiterature.gaussianState_eq_of_components
#check @NSEGR.NativeLiterature.gaussianRecoveredState_analyticAt
#print axioms NSEGR.NativeLiterature.gaussianRecoveredState_analyticAt
#check @NSEGR.NativeLiterature.gaussianRecoveredJet_compatible
#print axioms NSEGR.NativeLiterature.gaussianRecoveredJet_compatible
#check @NSEGR.NativeLiterature.gaussianRecoveredState_metric
#print axioms NSEGR.NativeLiterature.gaussianRecoveredState_metric
#check @NSEGR.NativeLiterature.gaussianRecoveredState_equation
#print axioms NSEGR.NativeLiterature.gaussianRecoveredState_equation
#check @NSEGR.NativeLiterature.gaussianRecoveredState_initial
#print axioms NSEGR.NativeLiterature.gaussianRecoveredState_initial
#check @NSEGR.NativeLiterature.gaussianRecoveredState_solution
#print axioms NSEGR.NativeLiterature.gaussianRecoveredState_solution
#check @NSEGR.NativeLiterature.gaussianEvolutionGerm_unique_of_state_unique
#print axioms NSEGR.NativeLiterature.gaussianEvolutionGerm_unique_of_state_unique
#check @NSEGR.NativeLiterature.gaussianStateSolutionMetric_tangential_vacuum
#print axioms NSEGR.NativeLiterature.gaussianStateSolutionMetric_tangential_vacuum
#check @NSEGR.NativeLiterature.gaussianEvolutionGerm_of_state
#print axioms NSEGR.NativeLiterature.gaussianEvolutionGerm_of_state
#check @NSEGR.NativeLiterature.gaussianEvolution_exists_of_CK
#print axioms NSEGR.NativeLiterature.gaussianEvolution_exists_of_CK
#check @NSEGR.NativeLiterature.gaussianEvolution_exists_unique_of_CK
#print axioms NSEGR.NativeLiterature.gaussianEvolution_exists_unique_of_CK
#check @NSEGR.NativeLiterature.literatureFlatGaussianGerm_of_evolution
#print axioms NSEGR.NativeLiterature.literatureFlatGaussianGerm_of_evolution
#check @NSEGR.NativeLiterature.literatureFlatGaussianGerm_exists_of_analyticCK
#print axioms NSEGR.NativeLiterature.literatureFlatGaussianGerm_exists_of_analyticCK
#check @NSEGR.NativeLiterature.literatureFlatGaussianGerm_eq_gaussian
#print axioms NSEGR.NativeLiterature.literatureFlatGaussianGerm_eq_gaussian
#check @NSEGR.NativeLiterature.literatureFlatGaussianGerm_evolution
#print axioms NSEGR.NativeLiterature.literatureFlatGaussianGerm_evolution
#check @NSEGR.NativeLiterature.literatureGaussianJetInput_of_analyticCK
#print axioms NSEGR.NativeLiterature.literatureGaussianJetInput_of_analyticCK
#check @NSEGR.NativeLiterature.literatureGaussianJetInput_native
#print axioms NSEGR.NativeLiterature.literatureGaussianJetInput_native
#check @NSEGR.NativeLiterature.literatureInputs_native
#print axioms NSEGR.NativeLiterature.literatureInputs_native
#check @NSEGR.NativeLiterature.NSE_GR_NATIVE_LITERATURE_CLOSURE
#print axioms NSEGR.NativeLiterature.NSE_GR_NATIVE_LITERATURE_CLOSURE
